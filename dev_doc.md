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
- `IsLinearlyReductive` class (existence of G-equivariant projection for f.d. reps)
- `IsLinearlyReductive.of_fintype` instance (finite groups, no `sorry`)
- `exists_reynolds_of_locallyFinite` (statement only, `sorry`)

---

## Removing the `sorry` in `exists_reynolds_of_locallyFinite`

### Why it's hard

The construction requires choosing, for each `r : R`, a f.d. G-stable submodule `V` containing `r` (from `IsLocallyFinite`), applying the Reynolds projection on `V`, and mapping back to `R`. The result must be independent of the choice of `V`.

Well-definedness requires **naturality** of the Reynolds projection: if `ι : V₁ →ₗ[k] V₂` is G-equivariant, then `ι ∘ π₁ = π₂ ∘ ι`. Naturality in turn requires **uniqueness** of the projection on each f.d. representation. Uniqueness requires knowing that `Hom_G(W, T) = 0` when `W^G = 0` and `T` is trivial, which follows from **complete reducibility**.

### Prerequisite: Refactor `IsLinearlyReductive`

The current definition (existence of a projection) is too weak to derive uniqueness directly. Refactor to the equivalent formulation using **complete reducibility**:

> Every G-stable submodule of a f.d. representation has a G-stable complement.

```
class IsLinearlyReductive : Prop where
  hasComplement : ∀ (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (W : Submodule k V),
    (∀ (g : G) (w : V), w ∈ W → ρ g w ∈ W) →
    ∃ U : Submodule k V, (∀ (g : G) (u : V), u ∈ U → ρ g u ∈ U) ∧ IsCompl W U
```

Then derive the old formulation (existence of projection onto `V^G`) as a theorem: take `W = invariants ρ`, get complement `U`, and the projection along `U` onto `W` is the Reynolds operator.

Also re-prove `IsLinearlyReductive.of_fintype` from Maschke's theorem (`LinearMap.equivariantProjection`).

### Lemma A: Uniqueness of the Reynolds projection

**Statement.** For a f.d. representation `V` of a linearly reductive group, the G-equivariant k-linear projection `V → V^G` is unique.

**Proof sketch.** Let `π₁, π₂` be two such projections. Set `φ = π₁ - π₂ : V → V^G`. Then `φ` is G-equivariant and `φ|_{V^G} = 0`. By complete reducibility, `V = V^G ⊕ W` with `W` G-stable and `W^G = 0`. It suffices to show `φ|_W = 0`.

The restriction `φ|_W : W → V^G` is G-equivariant. Since `V^G` has trivial action, `φ(gw) = g · φ(w) = φ(w)` for all `g`, so `φ` factors through the coinvariants. Apply complete reducibility to `W`: the submodule `K = ker(φ|_W)` is G-stable, so `W = K ⊕ K'`. The quotient `W/K ≅ K'` maps isomorphically onto `im(φ|_W) ⊆ V^G`, so `K'` is a trivial sub-representation of `W`. But `K'^G = K' ⊆ W^G = 0`, so `K' = 0` and `φ|_W = 0`.

### Lemma B: Naturality

**Statement.** If `ι : V₁ →ₗ[k] V₂` is G-equivariant and `π₁, π₂` are the (unique) Reynolds projections, then `π₂ ∘ ι = ι ∘ π₁`.

**Proof sketch.** The map `π₂ ∘ ι|_{V₁^G}` is a G-equivariant projection `V₁ → V₂^G` that restricts to `ι` on `V₁^G` (since `ι` maps invariants to invariants, and `π₂` fixes invariants). By uniqueness (Lemma A), the composite `π₂ ∘ ι` agrees with `ι ∘ π₁` on all of `V₁`.

### Lemma C: Local construction

**Statement.** For each `r : R`, define `reynolds(r)` by choosing (via `IsLocallyFinite`) a f.d. G-stable `V` with `r ∈ V`, restricting the representation to `V`, applying the unique Reynolds projection, and mapping back to `R` via the inclusion `V ↪ R`.

This uses `Classical.choice` for the submodule selection.

### Lemma D: Well-definedness and linearity

**Well-definedness.** If `r ∈ V₁` and `r ∈ V₂`, then `r ∈ V₁ + V₂` (still f.d., G-stable). The inclusions `V₁ ↪ V₁ + V₂` and `V₂ ↪ V₁ + V₂` are G-equivariant. By naturality (Lemma B), the projections computed in `V₁`, `V₂`, and `V₁ + V₂` all agree on `r`.

**Linearity.** For `r, s : R`, use `IsLocallyFinite` to get `V_r ∋ r` and `V_s ∋ s`. Then `V_r + V_s` is f.d., G-stable, and contains both `r` and `s`. Linearity of the local projection on `V_r + V_s` gives `reynolds(r + s) = reynolds(r) + reynolds(s)` and `reynolds(c · r) = c · reynolds(r)` (after applying well-definedness to identify all three computations in `V_r + V_s`).

### Suggested order of work

1. Refactor `IsLinearlyReductive` to use complete reducibility
2. Re-prove `IsLinearlyReductive.of_fintype`
3. Derive existence of Reynolds projection on f.d. reps (old formulation) as a theorem
4. Prove Lemma A (uniqueness)
5. Prove Lemma B (naturality)
6. Prove Lemma C + D (local construction, well-definedness, linearity)
7. Remove the `sorry`

### Verification

`lake build` after each step. No `sorry` in final code.
