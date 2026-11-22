#!/usr/bin/env python3
"""Writes include/ada_url_pattern.h from an ada release.

ada's URLPattern (ada::url_pattern, ada::parse_url_pattern) is a pattern
compiler and matcher written on top of ada's URL parser. Node.js uses it for
its URLPattern class. vbind keeps that code as ada wrote it and puts vurl
under it: this script copies the URLPattern files out of ada's single-header
release, unchanged except that the functions from ada's .cpp files are marked
`inline`, so the result is a header. Every URL it parses or canonicalizes goes
through the ada::parse and setters of vbind's ada.h, that is, through vurl.

The one thing not copied is ada's table of identifier code points, which ada
stores compressed inside its IDNA tables. The script builds the real ada,
asks it about every code point, and writes the answer as ranges.

    scripts/vendor-ada-url-pattern.py DIR > include/ada_url_pattern.h

DIR holds the release's ada.h and ada.cpp (tests/cpp/run.sh fetches them).
"""
import os
import re
import subprocess
import sys
import tempfile

HEADER_FILES = [
    "include/ada/expected.h",
    "include/ada/url_pattern_regex.h",
    "include/ada/url_pattern_init.h",
    "include/ada/url_pattern.h",
    "include/ada/url_pattern_helpers.h",
    "include/ada/parser-inl.h",
    "include/ada/url_pattern-inl.h",
    "include/ada/url_pattern_helpers-inl.h",
]
SOURCE_FILES = [
    "src/url_pattern.cpp",
    "src/url_pattern_helpers.cpp",
    "src/url_pattern_regex.cpp",
]

# Declarations from ada files this header does not copy (parser.h,
# implementation.h and implementation-inl.h).
FORWARD = """\
namespace ada {
template <url_pattern_regex::regex_concept regex_provider>
class url_pattern;
struct url_pattern_options;
namespace parser {
template <url_pattern_regex::regex_concept regex_provider>
tl::expected<url_pattern<regex_provider>, errors> parse_url_pattern_impl(
    std::variant<std::string_view, url_pattern_init>&& input,
    const std::string_view* base_url, const url_pattern_options* options);
}  // namespace parser
}  // namespace ada
"""
ENTRY = """\
namespace ada {
template <url_pattern_regex::regex_concept regex_provider>
ada_warn_unused tl::expected<url_pattern<regex_provider>, errors>
parse_url_pattern(std::variant<std::string_view, url_pattern_init>&& input,
                  const std::string_view* base_url = nullptr,
                  const url_pattern_options* options = nullptr) {
  return parser::parse_url_pattern_impl<regex_provider>(std::move(input),
                                                        base_url, options);
}
}  // namespace ada
"""

DUMPER = r"""
#include <cstdio>
#include "ada.h"
int main() {
  for (int first = 1; first >= 0; first--) {
    long start = -1;
    for (long c = 0; c <= 0x110000; c++) {
      bool in = c < 0x110000 && ada::idna::valid_name_code_point(char32_t(c), first);
      if (in && start < 0) start = c;
      if (!in && start >= 0) { std::printf("%d %ld %ld\n", first, start, c - 1); start = -1; }
    }
  }
}
"""


def own_text(lines, name):
    """The lines of one amalgamated file, without the files nested in it."""
    out, depth, inside = [], 0, False
    for line in lines:
        m = re.match(r"/\* (begin|end) file (\S+) \*/", line)
        if m:
            if m.group(2) == name and not inside and m.group(1) == "begin":
                inside, depth = True, 0
                out.append(line)
                continue
            if inside:
                if m.group(1) == "begin":
                    depth += 1
                elif depth == 0:
                    out.append(line)
                    return out
                else:
                    depth -= 1
                continue
        if inside and depth == 0:
            out.append(line)
    raise SystemExit(f"{name}: not found")


def inline_definitions(lines):
    """Marks the namespace-scope function definitions of a .cpp file inline."""
    out = []
    for line in lines:
        if re.match(r"(tl::expected<|std::|bool )", line):
            line = "inline " + line
        out.append(line)
    return out


def identifier_ranges(directory):
    cxx = os.environ.get("CXX", "c++")
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "dump.cc")
        exe = os.path.join(tmp, "dump")
        with open(src, "w") as f:
            f.write(DUMPER)
        subprocess.check_call(
            [cxx, "-std=c++20", "-O2", "-I", directory, src,
             os.path.join(directory, "ada.cpp"), "-o", exe])
        rows = subprocess.check_output([exe], text=True).split("\n")
    tables = {"1": [], "0": []}
    for row in rows:
        if row:
            first, lo, hi = row.split()
            tables[first].append((int(lo), int(hi)))
    return tables["1"], tables["0"]


def table(name, ranges):
    out = [f"inline constexpr uint32_t {name}[][2] = {{"]
    for i in range(0, len(ranges), 4):
        out.append("    " + " ".join(f"{{0x{lo:x}, 0x{hi:x}}}," for lo, hi in ranges[i:i + 4]))
    out.append("};")
    return out


def main():
    directory = sys.argv[1]
    header = open(os.path.join(directory, "ada.h"), encoding="utf-8").read().split("\n")
    source = open(os.path.join(directory, "ada.cpp"), encoding="utf-8").read().split("\n")
    version = next(re.search(r'"(.*)"', l).group(1) for l in header
                   if l.startswith("#define ADA_VERSION "))
    start, part = identifier_ranges(directory)

    out = [
        "/*",
        f" * ada_url_pattern.h: ada {version}'s URLPattern, over vbind's ada.h.",
        " *",
        " * Written by scripts/vendor-ada-url-pattern.py; do not edit. Everything",
        " * between the \"begin file\" and \"end file\" marks is copied from",
        " * https://github.com/ada-url/ada (Copyright 2023 Yagiz Nizipli and Daniel",
        " * Lemire, Apache-2.0 or MIT; expected.h is Sy Brand's tl::expected, CC0),",
        " * with the functions of ada's .cpp files marked inline. The code parses",
        " * and matches patterns; the URLs it meets are parsed by ada.h's",
        " * ada::parse, which is vurl. Included by ada.h, not on its own.",
        " */",
        "#ifndef VBIND_ADA_URL_PATTERN_H",
        "#define VBIND_ADA_URL_PATTERN_H",
        "",
        "#include <algorithm>",
        "#include <array>",
        "#include <charconv>",
        "#include <concepts>",
        "#include <optional>",
        "#include <ostream>",
        "#include <ranges>",
        "#include <string>",
        "#include <string_view>",
        "#include <tuple>",
        "#include <unordered_map>",
        "#include <variant>",
        "#include <vector>",
        "",
        "/* ada's identifier code points (IdentifierStart and IdentifierPart of",
        f" * ECMAScript), read out of ada {version} one code point at a time. */",
        "namespace ada::idna {",
    ]
    out += table("vbind_id_start", start)
    out += table("vbind_id_part", part)
    out += [
        "inline bool valid_name_code_point(char32_t code_point, bool first) {",
        "  const auto* t = first ? vbind_id_start : vbind_id_part;",
        "  size_t n = first ? std::size(vbind_id_start) : std::size(vbind_id_part);",
        "  size_t lo = 0, hi = n;",
        "  while (lo < hi) {",
        "    size_t mid = (lo + hi) / 2;",
        "    if (t[mid][1] < code_point) lo = mid + 1; else hi = mid;",
        "  }",
        "  return lo < n && t[lo][0] <= code_point;",
        "}",
        "}  // namespace ada::idna",
        "",
    ]
    for i, name in enumerate(HEADER_FILES):
        out += own_text(header, name)
        if name == "include/ada/url_pattern_init.h":
            out += FORWARD.split("\n")
    for name in SOURCE_FILES:
        out += inline_definitions(own_text(source, name))
    out += ENTRY.split("\n")
    out += ["#endif  // VBIND_ADA_URL_PATTERN_H", ""]
    sys.stdout.write("\n".join(out))


if __name__ == "__main__":
    main()
