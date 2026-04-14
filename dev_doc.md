# GIT Formalization — Developer Notes

## Current State (Basic.lean)

Imports: Maschke's theorem, symmetric polynomials, GL_n, `Rep k G`, irreducibility.

Definitions so far:
- `IsLinearAlgebraic`: G embeds into GL_n(k) for some n.
- Verified Mathlib API: `Rep k G`, `k[G]`, products, morphisms, `FiniteDimensional`, indexed products, `IsIrreducible`.

---

## Section 1.5: Reynolds Operator on k-Algebras via Local Finiteness

### Mathematical Setup

**Goal.** Given a linearly reductive group G acting on a k-algebra R, construct a k-linear retraction R -> R^G (the Reynolds operator).

**Finite case.** When G is finite with |G| invertible in k, average: reynolds(r) = (1/|G|) sum_{g} g.r. Already in Mathlib as `Representation.averageMap`.

**Infinite case.** For GL_n, SL_n, etc., the action on R is *locally finite*: every r in R lies in a finite-dimensional G-stable subspace. The Reynolds operator is defined by applying the finite-dimensional projection on each such subspace.

### Local Finiteness

A G-action on a k-module R is **locally finite** if for every r in R, there exists a finite-dimensional G-stable k-submodule V with r in V.

**Well-definedness.** If r in V_1 and r in V_2 (both f.d., G-stable), then r in V_1 + V_2. Naturality of the Reynolds operator (commutes with G-equivariant inclusions) forces the projections in V_1, V_2, and V_1 + V_2 to agree on r.

### Relevant Mathlib API

| Concept | Mathlib name |
|---------|-------------|
| G acts on ring R | `MulSemiringAction G R` |
| Action to representation | `Representation.ofDistribMulAction k G R` |
| Averaging map (finite G) | `Representation.averageMap` |
| Projection proof | `Representation.isProj_averageMap` |
| Invariants R^G (subalgebra) | `FixedPoints.subalgebra k R G` |
| Invariants (submodule) | `Representation.invariants` |

Required typeclasses for `averageMap`: `Fintype G`, `Invertible (Fintype.card G : k)`.
Required for `FixedPoints.subalgebra`: `MulSemiringAction G R`, `SMulCommClass G k R`.
Required for `ofDistribMulAction`: `DistribMulAction G R`, `SMulCommClass G k R`.

### Implementation Plan

All work in `GIT/Basic.lean`, after line 67.

1. **Imports.** Add `RepresentationTheory.Invariants`, `Algebra.Ring.Action.Basic`.

2. **`IsLocallyFinite`** (new definition, not in Mathlib).
   For every r : R, exists a finite-dimensional G-stable k-submodule V <= R with r in V.
   Use maximal generality: `CommSemiring k`, `Monoid G`, `AddCommMonoid R`, `Module k R`, `DistribMulAction G R`.

3. **`isLocallyFinite_of_fintype`.**
   Finite G implies locally finite. Proof: V = span_k(orbit of r); finite orbit, hence f.d.; G-stable by closure.

4. **`reynoldsOperator`** (finite group case).
   Compose `Representation.averageMap` with `Representation.ofDistribMulAction k G R`.
   Type: `R ->_l[k] R`.

5. **`reynoldsOperator_mem_fixedPoints`.**
   Image lands in `FixedPoints.subalgebra k R G`. From `isProj_averageMap`.

6. **`reynoldsOperator_id_of_invariant`.**
   Reynolds fixes R^G pointwise. From `isProj_averageMap`.

7. **(Stretch) General locally-finite case.** State the construction for infinite G with a "Reynolds operator on f.d. reps" as a typeclass hypothesis; prove well-definedness via naturality.

### Completed (steps 1–7)

Steps 1–6 are fully proved (no `sorry`). Step 7 introduced:
- `IsLinearlyReductive` class: refactored to use `IsSemisimpleRepresentation` (complete reducibility)
- `IsLinearlyReductive.of_fintype` instance (finite groups, no `sorry`)
- `Representation.invariantSubrepresentation`: invariants as a `Subrepresentation`
- `IsLinearlyReductive.exists_reynolds_projection`: existence of G-equivariant projection (no `sorry`)
- `IsLinearlyReductive.reynolds_unique`: uniqueness of the projection (no `sorry`)
- `exists_reynolds_of_locallyFinite` (statement only, `sorry`)

---

## Completed: Refactoring and Lemma A

### Refactored `IsLinearlyReductive`

Used `IsSemisimpleRepresentation ρ` (= `ComplementedLattice (Subrepresentation ρ)`) instead of raw existence of a projection. This directly gives G-stable complements for any subrepresentation.

```
class IsLinearlyReductive (k : Type*) [Field k] (G : Type*) [Group G] : Prop where
  isSemisimple : ∀ (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), IsSemisimpleRepresentation ρ
```

`of_fintype` proved via `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule` and the Maschke instance `IsSemisimpleModule k[G] V`.

### `exists_reynolds_projection` (existence)

From `IsSemisimpleRepresentation ρ`, get a complement `W` of `ρ.invariantSubrepresentation`. Convert `IsCompl` on `Subrepresentation` to `IsCompl` on `Submodule` (via `toSubmodule_inf`/`toSubmodule_sup`). Build projection using `Submodule.linearProjOfIsCompl`. G-equivariance: decompose `v = vi + vw`, use that `ρ g vi = vi` (invariant) and `ρ g vw ∈ W` (G-stable), so the projection is identity on `vi` and zero on both `vw` and `ρ g vw`.

### `reynolds_unique` (uniqueness, Lemma A)

**Proved theorem.** Any two G-equivariant k-linear projections `π₁, π₂` onto `ρ.invariants` are equal.

**Proof structure:**
1. Restrict ρ to `ker π₁` via `ρ.subrepresentation`. This is f.d. and semisimple (by `hlr.isSemisimple`).
2. Define `L = ker π₁ ∩ ker π₂` as a subrepresentation of the restriction (it's the comap of `ker π₂` along the inclusion `ker π₁ ↪ V`).
3. By semisimplicity of `ker π₁`, `L` has a complement `T` (from `ComplementedLattice`).
4. **Key step**: for `t ∈ T`, show `ρ g t = t`:
   - `ρ g t - t ∈ L` because `π₂(ρ g t - t) = π₂ t - π₂ t = 0` (G-equivariance of π₂).
   - `ρ g t - t ∈ T` because T is G-stable (subrepresentation) and closed under subtraction.
   - `ρ g t - t ∈ L ∩ T = ⊥` (complement), so `ρ g t = t`.
5. Then `t ∈ ρ.invariants` and `t ∈ ker π₁`, so `t ∈ ρ.invariants ∩ ker π₁ = ⊥` (from `h₁.isCompl`).
6. Hence `T = ⊥`, so `L = ⊤`, meaning `ker π₁ ⊆ ker π₂`.
7. Both projections are identity on `ρ.invariants` and zero on `ker π₁`, so `π₁ = π₂`.

**Mathlib API used:**
- `Representation.subrepresentation` to restrict ρ to a G-stable submodule
- `Subrepresentation` lattice operations (`toSubmodule_inf`, `toSubmodule_sup`)
- `ComplementedLattice.exists_isCompl` for the complement
- `LinearMap.IsProj.isCompl` connecting projections to complementary submodules

---

## Remaining `sorry`: `exists_reynolds_of_locallyFinite`

### What it needs

With uniqueness (Lemma A) now proved, the remaining steps are:

### Lemma B: Naturality

**Statement.** If `ι : V₁ →ₗ[k] V₂` is G-equivariant and `π₁, π₂` are the (unique) Reynolds projections on V₁, V₂, then `π₂ ∘ ι = ι ∘ π₁`.

**Proof.** The map `ι ∘ π₁ : V₁ → V₂` is G-equivariant and projects `V₁` into `V₂^G` (since ι maps invariants to invariants). The map `π₂ ∘ ι : V₁ → V₂` is also G-equivariant and agrees with `ι ∘ π₁` on `V₁^G`. Both are G-equivariant projections `V₁ → V₂^G` that restrict to `ι` on `V₁^G`. By `reynolds_unique` applied appropriately, they agree.

### Lemma C: Local construction

For each `r : R`, use `IsLocallyFinite` to choose (via `Classical.choice`) a f.d. G-stable `V` with `r ∈ V`. Restrict the representation, apply the Reynolds projection, and map back via the inclusion `V ↪ R`.

### Lemma D: Well-definedness and linearity

**Well-definedness.** If `r ∈ V₁ ∩ V₂`, embed both into `V₁ + V₂` (f.d., G-stable). By naturality (Lemma B), projections in V₁, V₂, and V₁ + V₂ agree on r.

**Linearity.** For `r, s : R`, pick a common f.d. G-stable submodule containing both (using `IsLocallyFinite` for each, then take their sum). Linearity of the local projection gives linearity of the global map.

### Verification

`lake build` after each step. No `sorry` in final code.

### 04.13 work:
1. draw a flow of the dependency of the 8 theorems. Not in img, in code.
2. stick to the rep k g and other representation inside basic.lean to make the proof more readable.

---

## Why Each Definition Is Needed

### `Representation.IsLocallyFinite` (line 79)

The Reynolds operator is straightforward on finite-dimensional representations, but invariant
rings like `k[x₁,...,xₙ]` are infinite-dimensional. `IsLocallyFinite` captures the structural
property that lets us reduce the infinite-dimensional problem to many finite-dimensional ones:
every element lives in some finite-dimensional G-stable subspace. Without this definition,
there is no way to state or prove the main theorem (`exists_reynolds_of_locallyFinite`).

### `reynoldsOperator` (line 115)

Packages the finite-group averaging map `r ↦ (1/|G|) ∑_g g·r` as a named `k`-linear map
`R →ₗ[k] R`. This is the concrete, computable Reynolds operator for the finite case and
serves as the base case: Theorems 2–3 establish it is indeed a projection onto invariants.

### `IsLinearlyReductive` (line 137)

The hypothesis that makes everything work for infinite groups (GL_n, SL_n, etc.). It says
every finite-dimensional representation is completely reducible. This is needed because:
- Theorem 5 uses it to get a G-stable complement of the invariants → Reynolds projection.
- Theorem 6 (uniqueness) uses it to get complements inside kernels.
- Theorem 7 (naturality) uses it the same way.
- Theorem 8 (main result) needs all of the above.

Without this class, there is no way to construct Reynolds projections on individual
finite-dimensional subspaces, which are the building blocks for the global operator.

### `Representation.invariantSubrepresentation` (line 154)

Adapter between two APIs. `IsLinearlyReductive` gives complete reducibility via
`IsSemisimpleRepresentation`, which works on the `Subrepresentation` lattice. But invariants
are naturally a `Submodule`. To ask "the invariants have a G-stable complement" and invoke
`exists_isCompl` from semisimplicity, we must present the invariants as a `Subrepresentation`.
Without this wrapper, Theorem 5 (`exists_reynolds_projection`) cannot be stated.

---

## Dependency Flow of the 8 Theorems

Definitions are in `[brackets]`. Arrows show "A is used in the proof of B".

```
[IsLocallyFinite]          [reynoldsOperator]         [IsLinearlyReductive]     [invariantSubrepresentation]
     (line 79)                (line 115)                   (line 137)                  (line 154)
        |                      |      |                      |    |                        |
        |                      v      v                      |    |                        |
        |                  Thm 2    Thm 3                    |    |                        |
        |               (line 119) (line 124)                |    |                        |
        |                                                    |    |                        |
        |                      Thm 4                         |    |                        |
        |                   (line 142)                       |    |                        |
        |                      |                             |    |                        |
        |                      | [Maschke]                   |    |                        |
        |                      v                             |    |                        |
        |              IsLinearlyReductive.of_fintype -------+ -- |                        |
        |                                                    |    |                        |
        |                                                    v    v                        |
        |                                                  Thm 5 <-------------------------+
        |                                            (line 164, existence)
        |                                          uses: IsLinearlyReductive
        |                                                 invariantSubrepresentation
        |                                                 IsSemisimpleRepresentation
        |                                                    |
        |                                                    v
        |                                                  Thm 6
        |                                            (line 209, uniqueness)
        |                                          uses: IsLinearlyReductive
        |                                                 Thm 5 (existence)
        |                                                    |
        |                                                    v
        |                                                  Thm 7
        |                                            (line 291, naturality)
        |                                          uses: IsLinearlyReductive
        |                                                 Thm 6 (uniqueness)
        |                                                    |
        +----------------------------------------------------+
                                    |
                                    v
                                 Thm 8
                          (line 361, main result)
                        uses: IsLocallyFinite (hypothesis)
                               Thm 5 (local projections)
                               Thm 7 (naturality → well-definedness)
```

### Dependency summary (text form):

```
Thm 1 (isLocallyFinite_of_finite, line 86)
  <- [IsLocallyFinite]

Thm 2 (reynoldsOperator_mem_invariants, line 119)
  <- [reynoldsOperator]

Thm 3 (reynoldsOperator_id, line 124)
  <- [reynoldsOperator]

Thm 4 (of_fintype, line 142)
  <- [IsLinearlyReductive], Maschke's theorem

Thm 5 (exists_reynolds_projection, line 164)
  <- [IsLinearlyReductive], [invariantSubrepresentation]

Thm 6 (reynolds_unique, line 209)
  <- [IsLinearlyReductive], Thm 5

Thm 7 (reynolds_natural, line 291)
  <- [IsLinearlyReductive], Thm 6

Thm 8 (exists_reynolds_of_locallyFinite, line 361)
  <- [IsLocallyFinite], Thm 5, Thm 7
```
