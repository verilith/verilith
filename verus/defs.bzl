# Buck2 rules that verify a crate with Verus.
#
#   verus_library   a crate with proofs. Building it checks them.
#   rustc_library   a dependency with no proofs (from crates.io), compiled
#                   by the rustc Verus is built on.
#
# Every action runs verus.py, which holds the checks that make "the action
# passed" mean "the proofs hold". Read its header before changing anything
# here.
#
# A verus_library has these outputs:
#
#   :NAME            proof.json. Building it verifies the whole crate: every
#                    part, then a check that the parts add up to the crate.
#   :NAME[partK]     verifies one part only (K from 0). CI runs each part
#                    as its own job.
#   :NAME[export]    the crate compiled for its dependents, nothing verified.
#
# The crates a crate depends on are compiled, not verified again: each is
# verified by its own target.

VerusCrateInfo = provider(fields = {
    "crate": provider_field(str),
    "rmeta": provider_field(Artifact),
    # None for a crate with no proofs.
    "vir": provider_field(Artifact | None),
    # The vstd it was compiled against (None for a crate with no proofs).
    "vstd": provider_field(Label | None, default = None),
    # Every crate this one needs, itself included: {crate: VerusCrateInfo}.
    "closure": provider_field(dict),
})

VstdInfo = provider(fields = {
    "rlib": provider_field(Artifact),
    "vir": provider_field(Artifact),
})

VerusToolchainInfo = provider(fields = {
    "driver": provider_field(RunInfo),
    "pin": provider_field(Artifact),
})

def _verus_toolchain_impl(ctx):
    return [
        DefaultInfo(),
        VerusToolchainInfo(
            driver = RunInfo(args = cmd_args("python3", ctx.attrs.driver)),
            pin = ctx.attrs.pin,
        ),
    ]

# Verus itself comes from PATH (or $VERUS), like the prelude's system
# toolchains. What is pinned is checked instead of fetched: verus.py refuses
# any Verus that was not built from the commit in `pin`.
verus_toolchain = rule(
    impl = _verus_toolchain_impl,
    attrs = {
        "driver": attrs.source(doc = "verus.py"),
        "pin": attrs.source(doc = "scripts/verus-version"),
    },
    is_toolchain_rule = True,
)

def _crate_root(ctx):
    """The crate root: a source file, or a path inside a downloaded archive."""
    if ctx.attrs.archive != None:
        return cmd_args(ctx.attrs.archive, format = "{}/" + ctx.attrs.archive_root)
    if ctx.attrs.crate_root == None:
        fail("crate_root or archive is required")
    return cmd_args(ctx.attrs.crate_root)

def _verus_vstd_impl(ctx):
    toolchain = ctx.attrs._toolchain[VerusToolchainInfo]
    rlib = ctx.actions.declare_output("vstd", "libvstd.rlib")
    vir = ctx.actions.declare_output("vstd", "vstd.vir")
    cmd = cmd_args(
        toolchain.driver,
        "vstd",
        "--pin",
        toolchain.pin,
        "--edition",
        ctx.attrs.edition,
        "--root",
        _crate_root(ctx),
        "--rmeta",
        rlib.as_output(),
        "--vir",
        vir.as_output(),
    )
    for f in ctx.attrs.features:
        cmd.add("--feature", f)
    ctx.actions.run(cmd, category = "verus_vstd", identifier = ctx.label.name)
    return [DefaultInfo(default_outputs = [rlib, vir]), VstdInfo(rlib = rlib, vir = vir)]

# vstd, compiled from the crates.io release Cargo.lock pins, with the features
# a crate's Cargo.toml asks of it. Not verified here: it is verified by the
# Verus project, and trusted, exactly as under `cargo verus`.
verus_vstd = rule(
    impl = _verus_vstd_impl,
    attrs = {
        "archive": attrs.option(attrs.source(), default = None),
        "archive_root": attrs.string(default = "vstd.rs"),
        "crate_root": attrs.option(attrs.source(), default = None),
        "edition": attrs.string(default = "2021"),
        "features": attrs.list(attrs.string(), default = []),
        "_toolchain": attrs.toolchain_dep(default = "toolchains//:verus", providers = [VerusToolchainInfo]),
    },
)

def _vstd_label(ctx):
    return ctx.attrs.vstd.label if ctx.attrs.vstd != None else None

def _closure(deps):
    out = {}
    for d in deps:
        for name, info in d[VerusCrateInfo].closure.items():
            if name in out and out[name].rmeta != info.rmeta:
                fail("two different crates named {} in the dependencies".format(name))
            out[name] = info
    return out

def _crate_args(ctx, toolchain):
    """The arguments that define the crate. The same for every action on it."""
    args = cmd_args(
        "--pin",
        toolchain.pin,
        "--crate",
        ctx.attrs.crate,
        "--package",
        ctx.attrs.package or ctx.attrs.crate,
        "--version",
        ctx.attrs.version,
        "--edition",
        ctx.attrs.edition,
        "--root",
        _crate_root(ctx),
    )
    if ctx.attrs.vstd != None:
        vstd = ctx.attrs.vstd[VstdInfo]
        args.add("--vstd-rlib", vstd.rlib, "--vstd-vir", vstd.vir)
    for f in ctx.attrs.features:
        args.add("--feature", f)
    for c in ctx.attrs.cfgs:
        args.add("--cfg", c)
    direct = {d[VerusCrateInfo].crate: True for d in ctx.attrs.deps}
    mine = _vstd_label(ctx)
    for name, info in _closure(ctx.attrs.deps).items():
        if info.vir != None and info.vstd != mine:
            # Cargo builds one vstd for everything in a build. Two would be
            # two different libraries with one name.
            fail("{} is verified against {} but its dependency {} against {}".format(
                ctx.attrs.crate,
                mine,
                name,
                info.vstd,
            ))
        if name in direct:
            args.add("--extern", cmd_args(name, info.rmeta, delimiter = "="))

        # rustc finds a crate that another dependency needs only through a
        # search directory, even when the crate is also named with --extern.
        args.add("--dep-dir", cmd_args(info.rmeta, parent = 1))
        if info.vir != None:
            args.add("--import", cmd_args(name, info.vir, delimiter = "="))

    # The sources are read in place, through the crate root. Listing them
    # here makes them inputs of the action.
    args.add(cmd_args(hidden = ctx.attrs.srcs))
    return args

def _verus_library_impl(ctx):
    toolchain = ctx.attrs._toolchain[VerusToolchainInfo]
    crate = ctx.attrs.crate
    parts = ctx.attrs.parts
    if parts < 1:
        fail("parts must be at least 1")
    common = _crate_args(ctx, toolchain)

    out = "lib" + crate
    rmeta = ctx.actions.declare_output(out, "lib{}.rmeta".format(crate))
    vir = ctx.actions.declare_output(out, "{}.vir".format(crate))
    modules = ctx.actions.declare_output(out, "modules.json")
    ctx.actions.run(
        cmd_args(
            toolchain.driver,
            "export",
            common,
            "--parts",
            str(parts),
            "--rmeta",
            rmeta.as_output(),
            "--vir",
            vir.as_output(),
            "--modules",
            modules.as_output(),
        ),
        category = "verus_export",
        identifier = crate,
    )

    results = []
    sub_targets = {"export": [DefaultInfo(default_outputs = [rmeta, vir, modules])]}
    for k in range(parts):
        result = ctx.actions.declare_output("part{}.json".format(k))
        cmd = cmd_args(
            toolchain.driver,
            "verify",
            common,
            "--parts",
            str(parts),
            "--part",
            str(k),
            "--modules",
            modules,
            "--out",
            result.as_output(),
        )
        if ctx.attrs.allow_empty:
            cmd.add("--allow-empty")
        for a in ctx.attrs.verus_args:
            cmd.add("--verus-arg", a)
        ctx.actions.run(
            cmd,
            category = "verus_verify",
            identifier = "{} {}/{}".format(crate, k + 1, parts),
            # Verus runs one solver per core, so one of these at a time.
            weight_percentage = 100,
        )
        results.append(result)
        sub_targets["part{}".format(k)] = [DefaultInfo(default_output = result)]

    proof = ctx.actions.declare_output("proof.json")
    seal = cmd_args(toolchain.driver, "seal", "--modules", modules, "--out", proof.as_output())
    for r in results:
        seal.add("--result", r)
    if ctx.attrs.allow_empty:
        seal.add("--allow-empty")
    ctx.actions.run(seal, category = "verus_seal", identifier = crate)

    closure = _closure(ctx.attrs.deps)
    vstd = _vstd_label(ctx)
    closure[crate] = VerusCrateInfo(crate = crate, rmeta = rmeta, vir = vir, vstd = vstd, closure = {})
    return [
        DefaultInfo(default_output = proof, sub_targets = sub_targets),
        VerusCrateInfo(crate = crate, rmeta = rmeta, vir = vir, vstd = vstd, closure = closure),
    ]

_CRATE_ATTRS = {
    "crate": attrs.string(doc = "The crate name rustc sees (verilith_zlib)."),
    "package": attrs.option(attrs.string(), default = None, doc = "The Cargo package name (verilith-zlib)."),
    "version": attrs.string(),
    "edition": attrs.string(default = "2021"),
    "crate_root": attrs.option(attrs.source(), default = None),
    "archive": attrs.option(attrs.source(), default = None, doc = "A downloaded crate, instead of crate_root and srcs."),
    "archive_root": attrs.string(default = "src/lib.rs"),
    "srcs": attrs.list(attrs.source(), default = [], doc = "Every file the crate root pulls in."),
    "vstd": attrs.option(attrs.dep(providers = [VstdInfo]), default = None, doc = "The vstd to verify against."),
    "features": attrs.list(attrs.string(), default = []),
    "cfgs": attrs.list(attrs.string(), default = []),
    "deps": attrs.list(attrs.dep(providers = [VerusCrateInfo]), default = []),
    "_toolchain": attrs.toolchain_dep(default = "toolchains//:verus", providers = [VerusToolchainInfo]),
}

verus_library = rule(
    impl = _verus_library_impl,
    attrs = _CRATE_ATTRS | {
        "parts": attrs.int(default = 1, doc = "Verify the crate as this many parts, split by top-level module."),
        "allow_empty": attrs.bool(default = False, doc = "The crate has no proofs, on purpose."),
        "verus_args": attrs.list(attrs.string(), default = [], doc = "Extra arguments for Verus when verifying."),
    },
)

def _rustc_library_impl(ctx):
    toolchain = ctx.attrs._toolchain[VerusToolchainInfo]
    crate = ctx.attrs.crate
    rmeta = ctx.actions.declare_output("lib" + crate, "lib{}.rmeta".format(crate))
    ctx.actions.run(
        cmd_args(toolchain.driver, "rustc", _crate_args(ctx, toolchain), "--rmeta", rmeta.as_output()),
        category = "verus_rustc",
        identifier = crate,
    )
    closure = _closure(ctx.attrs.deps)
    closure[crate] = VerusCrateInfo(crate = crate, rmeta = rmeta, vir = None, closure = {})
    return [
        DefaultInfo(default_output = rmeta),
        VerusCrateInfo(crate = crate, rmeta = rmeta, vir = None, closure = closure),
    ]

rustc_library = rule(impl = _rustc_library_impl, attrs = _CRATE_ATTRS)
