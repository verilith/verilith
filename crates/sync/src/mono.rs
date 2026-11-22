//! A ghost monotonic counter: one authoritative value that can only grow,
//! and duplicable lower bounds on it. Used to carry facts like "this stamp
//! was at least `s` when I read it" from one atomic step to a later one.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::{Resource, PCM};
use vstd::resource::Loc;

verus! {

pub ghost enum MaxNat {
    Ok { auth: Option<nat>, lb: nat },
    Bad,
}

pub open spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

impl ResourceAlgebra for MaxNat {
    open spec fn valid(self) -> bool {
        match self {
            MaxNat::Ok { auth, lb } => auth matches Some(v) ==> lb <= v,
            MaxNat::Bad => false,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (MaxNat::Ok { auth: a1, lb: l1 }, MaxNat::Ok { auth: a2, lb: l2 }) => {
                if a1 is Some && a2 is Some {
                    MaxNat::Bad
                } else {
                    MaxNat::Ok { auth: if a1 is Some { a1 } else { a2 }, lb: max(l1, l2) }
                }
            }
            _ => MaxNat::Bad,
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl PCM for MaxNat {
    open spec fn unit() -> Self {
        MaxNat::Ok { auth: None, lb: 0 }
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

/// The authoritative value.
pub tracked struct MonoAuth {
    r: Resource<MaxNat>,
}

/// A lower bound on a [`MonoAuth`]'s value at the time it was taken,
/// and so forever after.
pub tracked struct MonoLb {
    r: Resource<MaxNat>,
}

impl MonoAuth {
    pub closed spec fn wf(self) -> bool {
        &&& self.r.value() matches MaxNat::Ok { auth: Some(_), lb }
        &&& self.r.value()->Ok_lb == 0
    }

    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> nat {
        self.r.value()->Ok_auth->0
    }

    pub proof fn alloc(v: nat) -> (tracked r: MonoAuth)
        ensures
            r.wf(),
            r@ == v,
    {
        MonoAuth { r: Resource::alloc(MaxNat::Ok { auth: Some(v), lb: 0 }) }
    }

    /// Raises the value.
    pub proof fn advance(tracked &mut self, v: nat)
        requires
            old(self).wf(),
            old(self)@ <= v,
        ensures
            final(self).wf(),
            final(self).loc() == old(self).loc(),
            final(self)@ == v,
    {
        let tracked mut r = Resource::alloc(MaxNat::unit());
        vstd::modes::tracked_swap(&mut r, &mut self.r);
        let new_v = MaxNat::Ok { auth: Some(v), lb: 0 };
        assert(vstd::resource::relations::frame_preserving_update(r.value(), new_v));
        self.r = r.update(new_v);
    }

    /// A lower bound equal to the current value.
    pub proof fn lb(tracked &self) -> (tracked l: MonoLb)
        requires
            self.wf(),
        ensures
            l.loc() == self.loc(),
            l@ == self@,
    {
        let f = MaxNat::Ok { auth: None, lb: self@ };
        assert(vstd::resource::relations::frame_preserving_update(self.r.value(), MaxNat::op(f, self.r.value())));
        MonoLb { r: self.r.duplicate_previous(f) }
    }

    /// Every lower bound is at most the current value.
    pub proof fn check(tracked &mut self, tracked l: &MonoLb)
        requires
            old(self).wf(),
            old(self).loc() == l.loc(),
        ensures
            *final(self) == *old(self),
            l@ <= final(self)@,
    {
        use_type_invariant(l);
        self.r.validate_2(&l.r);
    }
}

impl MonoLb {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches MaxNat::Ok { auth: None, .. }
    }

    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> nat {
        self.r.value()->Ok_lb
    }

    pub proof fn dup(tracked &self) -> (tracked l: MonoLb)
        ensures
            l.loc() == self.loc(),
            l@ == self@,
    {
        use_type_invariant(self);
        MonoLb { r: self.r.duplicate_previous(self.r.value()) }
    }

    /// A weaker bound.
    pub proof fn weaken(tracked &self, n: nat) -> (tracked l: MonoLb)
        requires
            n <= self@,
        ensures
            l.loc() == self.loc(),
            l@ == n,
    {
        use_type_invariant(self);
        let f = MaxNat::Ok { auth: None, lb: n };
        assert(vstd::resource::relations::frame_preserving_update(self.r.value(), MaxNat::op(f, self.r.value())));
        MonoLb { r: self.r.duplicate_previous(f) }
    }
}

} // verus!
