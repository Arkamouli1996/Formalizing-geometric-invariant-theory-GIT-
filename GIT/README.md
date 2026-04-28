# Reynolds Operator

This file proves that if a linearly reductive group acts on a finite-dimensional vector space, then a Reynolds operator exists.

First it defines what a linearly reductive group is: a group is linearly reductive if for every representation, the invariant subspace `V^G` has a complementary submodule `W'` such that `V = V^G ⊕ W'`.

It then constructs the Reynolds operator as the projection `R : V → V` onto `V^G` along `W'`. We show that `R` sends every element of `V` into the invariants, and everything outside the invariants gets sent to zero. Finally, we prove that this operator is unique. For uniqueness: any `v` splits as a kernel part plus an invariant part. Two operators with the same kernel must agree on both parts, so they are equal.