# Reynolds Operator and Local Finiteness: Summary of Formalized Mathematics

## Overview

In `GIT/Basic.lean`, we formalize the construction of the **Reynolds operator** for linearly reductive groups acting on possibly infinite-dimensional modules, using the theory of locally finite representations. The key achievement is a fully sorry-free proof that a linearly reductive group acting locally finitely on a module admits a canonical k-linear projection onto the invariants.

---

## What We Define

### 1. Locally Finite Actions (`Representation.IsLocallyFinite`)

**Definition.** A `DistribMulAction` of a monoid `G` on a `k`-module `R` is *locally finite* if every element `r : R` is contained in a finite-dimensional, `G`-stable `k`-submodule `V ≤ R`.

This is a new definition (not in Mathlib). It is stated at maximal generality: `CommSemiring k`, `Monoid G`, `AddCommMonoid R`.

### 2. Reynolds Operator for Finite Groups (`reynoldsOperator`)

**Definition.** For a finite group `G` with `|G|` invertible in `k`, the Reynolds operator `R →ₗ[k] R` is defined as the averaging map `r ↦ (1/|G|) ∑_g g • r`, obtained by composing `Representation.averageMap` with `Representation.ofDistribMulAction`.

### 3. Linear Reductivity (`IsLinearlyReductive`)

**Definition.** A group `G` is *linearly reductive* over `k` if every finite-dimensional representation of `G` over `k` is completely reducible, i.e., every subrepresentation has a G-stable complement. Formally: every finite-dimensional `ρ : Representation k G V` satisfies `IsSemisimpleRepresentation ρ` (equivalently, `ComplementedLattice (Subrepresentation ρ)`).

### 4. Invariant Subrepresentation (`Representation.invariantSubrepresentation`)

**Definition.** The invariants `ρ.invariants` (vectors fixed by all `g ∈ G`) form a `Subrepresentation` of `ρ`. This wraps the existing Mathlib submodule `ρ.invariants` into the subrepresentation lattice.

---

## What We Prove

### Theorem 1: Finite actions are locally finite (`isLocallyFinite_of_finite`)

> If `G` is finite, then any `DistribMulAction` of `G` on a `k`-module `R` is locally finite.

**Proof idea.** For any `r : R`, take `V = span_k(G • r)`. The orbit is finite (since `G` is finite), so `V` is finite-dimensional. It is `G`-stable because `g • (g' • r) = (gg') • r ∈ orbit`.

### Theorem 2: Reynolds operator maps into invariants (`reynoldsOperator_mem_invariants`)

> For a finite group, the Reynolds operator sends every element into the `G`-invariant submodule.

### Theorem 3: Reynolds operator fixes invariants (`reynoldsOperator_id`)

> For a finite group, the Reynolds operator is the identity on `G`-invariant elements.

### Theorem 4: Finite groups are linearly reductive (`IsLinearlyReductive.of_fintype`)

> If `G` is a finite group with `|G|` invertible in `k`, then `G` is linearly reductive.

**Proof idea.** Follows from Maschke's theorem: the group algebra `k[G]` is semisimple when `|G|` is invertible, which implies every finite-dimensional `k[G]`-module (= representation) is semisimple.

### Theorem 5: Existence of the Reynolds projection (`exists_reynolds_projection`)

> If `G` is linearly reductive and `ρ` is a finite-dimensional representation, there exists a `k`-linear, `G`-equivariant projection `π : V →ₗ[k] V` onto `ρ.invariants`.

**Proof idea.** By complete reducibility, the invariant subrepresentation has a `G`-stable complement `W`. The projection along `V = V^G ⊕ W` is the identity on `V^G` and zero on `W`. G-equivariance follows because both summands are `G`-stable: if `v = v_inv + v_W`, then `ρ(g)(v_inv) = v_inv` and `ρ(g)(v_W) ∈ W`, so the projection commutes with the group action.

### Theorem 6: Uniqueness of the Reynolds projection — "Lemma A" (`reynolds_unique`)

> Any two `G`-equivariant, `k`-linear projections `π₁, π₂ : V → V` onto `ρ.invariants` are equal.

**Proof idea.** This is the most technically involved result. The argument proceeds by:

1. **Restrict to ker π₁.** The kernel `ker π₁` is `G`-stable (by equivariance) and finite-dimensional, hence semisimple by linear reductivity.
2. **Form L = ker π₁ ∩ ker π₂** as a subrepresentation of `ker π₁`.
3. **Get a complement T** of `L` inside `ker π₁` by semisimplicity.
4. **Show T = 0:** For `t ∈ T`, compute `ρ(g)(t) - t`. This difference lies in `L` (because `π₂(ρ(g)(t) - t) = π₂(t) - π₂(t) = 0` by equivariance) and also in `T` (because `T` is `G`-stable). Since `L ∩ T = 0` (they are complements), we get `ρ(g)(t) = t`, i.e., `t` is invariant. But `t ∈ ker π₁` and `t ∈ V^G` implies `t ∈ V^G ∩ ker π₁ = 0`.
5. **Conclude:** `T = 0` implies `L = ker π₁`, meaning `ker π₁ ⊆ ker π₂`. Both projections are the identity on `V^G` and zero on `ker π₁`, so `π₁ = π₂`.

### Theorem 7: Naturality of the Reynolds projection — "Lemma B" (`reynolds_natural`)

> If `ι : V₁ →ₗ[k] V₂` intertwines representations `ρ₁` and `ρ₂`, and `π₁, π₂` are the Reynolds projections on `V₁, V₂` respectively, then `π₂ ∘ ι = ι ∘ π₁`.

**Proof idea.** Decompose `v = π₁(v) + (v - π₁(v))`. On `V^G`, `ι ∘ π₁ = π₂ ∘ ι` because both sides equal `ι` there (both projections fix invariants, and `ι` preserves invariants). On `ker π₁`, apply the same complement argument as in Lemma A: form `L = {w ∈ ker π₁ : π₂(ι(w)) = 0}`, get a complement `T`, show `T = 0` by the same invariant-and-complement trick, conclude `L = ker π₁`, so `π₂ ∘ ι$ vanishes on `ker π₁$, matching `ι ∘ π₁`.

### Theorem 8: Reynolds operator for locally finite actions (`exists_reynolds_of_locallyFinite`)

> If `G` is linearly reductive and acts locally finitely on a `k`-module `R`, there exists a `k`-linear, `G`-equivariant projection `R →ₗ[k] R` onto the invariants `R^G`.

This is the main result, assembling everything above. The proof constructs a global Reynolds operator from local ones:

**Proof idea.**

1. **Local construction.** For each `r : R`, use local finiteness to choose a finite-dimensional `G`-stable submodule `V(r)` containing `r`. Apply `exists_reynolds_projection` to get a local projection `π_r` on `V(r)`.

2. **Compatibility (well-definedness).** If `r ∈ W₁` and `r ∈ W₂` for two different finite-dimensional `G`-stable submodules, embed both into `W₁ + W₂` (still finite-dimensional and `G`-stable). By **naturality** applied to the inclusions `W₁ ↪ W₁ + W₂ ↩ W₂`, the projections on `W₁` and `W₂` agree on `r` when mapped back to `R`.

3. **Define the global map** `f(r) = V(r).subtype(π_{V(r)}(r))`. By compatibility, this does not depend on the choice of `V(r)`.

4. **Linearity.** For `f(r + s)`, use the common submodule `V(r) + V(s)` and compatibility to reduce to linearity of the local projection. Similarly for scalar multiplication.

5. **Projection property.** `f(r) ∈ R^G` follows from the local projection landing in invariants. `f(r) = r` for invariant `r` follows from the local projection fixing invariants.

6. **G-equivariance.** `f(g • r) = f(r)` because `g • r ∈ V(r)` (by `G`-stability), and by compatibility we can compute both `f(g • r)` and `f(r)` using the same local projection on `V(r)`, where equivariance holds.

---

## Status

All definitions and theorems are **fully proved** — no `sorry` anywhere in the file. The code compiles cleanly with `lake build`.

## Mathematical Significance

This formalizes a key step in Geometric Invariant Theory: the existence of a Reynolds operator for linearly reductive groups is the foundation for proving that invariant rings `R^G` are finitely generated (Hilbert's finiteness theorem). The locally finite approach handles the infinite-dimensional case (e.g., `G` acting on a polynomial ring) by reducing to the finite-dimensional theory via complete reducibility.