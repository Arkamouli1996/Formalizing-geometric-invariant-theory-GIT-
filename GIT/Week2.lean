import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic

open scoped DirectSum

universe u v w

section GradedCheck_S1

-- Step 0: Basic objects

variable (k : Type u) [Field k]
variable (G : Type v) [Group G]
variable (ι : Type w) [DecidableEq ι] [AddMonoid ι]
variable (R : Type*) [Semiring R] [Algebra k R]
variable (𝒜 : ι → Submodule k R)
/-
-- Step 1: Check the graded algebra infrastructure

#check GradedAlgebra
#check GradedAlgebra.proj
#check DirectSum.decomposeAlgEquiv

-- Step 2: Check group actions on rings / semirings

#check MulSemiringAction
#check MulSemiringAction.toRingEquiv

-- Step 3: Check invariant subring infrastructure

#check IsInvariantSubring
-/

-- Step 4: Assume R is already graded

variable [GradedAlgebra 𝒜]

-- Step 5: Encode the action by algebra automorphisms

variable (ρ : G →* R ≃ₐ[k] R)

-- Step 6: Define the missing condition: the action preserves the grading

def PreservesGrading : Prop :=
  ∀ (g : G) (d : ι) {r : R}, r ∈ 𝒜 d → (ρ g : R → R) r ∈ 𝒜 d

#check PreservesGrading

-- Step 7: Define the invariant subalgebra R^G

def FixedSubalgebra (ρ : G →* R ≃ₐ[k] R) : Subalgebra k R := by
  sorry

-- Step 8: Define the degree-d piece of the invariant subalgebra


def FixedPiece (d : ι) : Submodule k R :=
  𝒜 d ⊓ (FixedSubalgebra (ρ := ρ)).toSubmodule

-- Step 9: Main theorem skeleton:
-- R^G = ⨁ d, (R_d ∩ R^G)

theorem fixedSubalgebra_decomposes
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)) :
    True := by
  /-
  Intended mathematical content:

    The degree-d part of the invariant subalgebra is
      (R^G)_d := R_d ∩ R^G (subset of each other)

    and we have
      R^G = ⨁ d, (R_d ∩ R^G).

    Hence R^G is a graded k-subalgebra of R.
  -/
  sorry

end GradedCheck_S1

section IrrelevantIdeal_FiniteType_S2

variable (k : Type u) [Field k] (R : Type*) [CommRing R] [Algebra k R]
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

open Algebra HomogeneousIdeal

/- internally ℕ-graded `k`-algebra -/
#check GradedAlgebra 𝒜

/- irrelevant ideal `R₊` . Mathlib also writes `𝒜₊` locally -/
#check irrelevant 𝒜

/- as an ordinary ideal of `R` (used for `Ideal.FG`) -/
#check (irrelevant 𝒜).toIdeal

/- homogeneous ideal, not a separate type for `R₊` -/
#check HomogeneousIdeal 𝒜

/- finitely generated ideal of `R` -/
#check Ideal.FG (R := R)

/- finitely generated as `k`-algebra -/
#check FiniteType k R

/- degree-`0` part as `k`-algebra -/
#check Algebra k (𝒜 0)

/-
HANDWRITTEN PROOF TO FOLLOW: https://math.gsu.edu/fenescu/commalglectures/lect20.pdf

THRM:
Let R be a positively graded R_0-algebra. Let x_1, ..., x_n be elements of
positive degree. Then (x_1, ..., x_n) = bigoplus_{i=1}^∞ R_i ... only if {x_1, ..., x_n} generates R
as an R_0-algebra.

PROOF:
...we proceed by induction on the degree of y. If deg y = 0,
the proof is clear, so assume a positive degree. We have y ∈ (x_1, ..., x_n), so y = α_1x_1 +
··· + α_nx_n, with α_i ∈ R, and if deg x_i = d_i, then α_i ∈ R_{deg y−d_i} . To finish, apply the
induction hypothesis to the α_i’s.
-/

/-
If `R₊` is finitely generated as an ideal and `𝒜 0` is finitely generated as a `k`-algebra
(often `𝒜 0 = k` in GIT), then `R` is finitely generated as a `k`-algebra.
-/
theorem finiteType_of_finitely_generated_irrelevant_ideal
    [FiniteType k (𝒜 0)] (h : (irrelevant 𝒜).toIdeal.FG) :
    FiniteType k R := sorry

/-
suggested splitting into two part
theorem finiteType_over_degreeZero_of_finitely_generated_irrelevant
    (h : (irrelevant 𝒜).toIdeal.FG) :
    FiniteType (𝒜 0) R := by
  sorry
theorem finiteType_of_finitely_generated_irrelevant_ideal
    [FiniteType k (𝒜 0)] (h : (irrelevant 𝒜).toIdeal.FG) :
    FiniteType k R := by
  sorry
-/

end IrrelevantIdeal_FiniteType_S2

section RGplus_finitely_generated_S3
/-
We assume R is Noetherian. Then every ideal of R is finitely generated.
In particular, the extended ideal R₊^G R is finitely generated.
-/

variable (k : Type u) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable [IsNoetherianRing R]

/- Placeholder for the extended ideal `R₊^G R` inside `R`. -/
variable (extendedRGplus : Ideal R)

/-- Since `R` is Noetherian, the ideal `R₊^G R` is finitely generated. -/
theorem extendedRGplus_fg : extendedRGplus.FG := by
  sorry

/-- Choose a finite generating set for `R₊^G R`. -/
theorem exists_generators_extendedRGplus :
    ∃ s : Finset R, Ideal.span (↑s : Set R) = extendedRGplus := by
  sorry

end RGplus_finitely_generated_S3

section RGplus_generators_S4

variable (k : Type u) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable [IsNoetherianRing R]

/-
`RGplusSet` is the underlying set of `R₊^G` inside `R`,
and `extendedRGplus` is the extended ideal `R₊^G R ⊆ R`.
-/
variable (RGplusSet : Set R)
variable (extendedRGplus : Ideal R)

/-- Step 4:
If the extended ideal `R₊^G R` is generated by `RGplusSet`
and is finitely generated as an ideal of `R`,
then one can choose finitely many generators from `RGplusSet`. -/
theorem exists_generators_extendedRGplus_from_RGplus
    (hspan : Ideal.span RGplusSet = extendedRGplus)
    (hfg : extendedRGplus.FG) :
    ∃ s : Finset R,
      (∀ x ∈ s, x ∈ RGplusSet) ∧
      Ideal.span (↑s : Set R) = extendedRGplus := by
  /-
  Intended proof:
  since `extendedRGplus.FG`, there exists a finite set generating it;
  because `extendedRGplus = Ideal.span RGplusSet`, those generators
  may be chosen from `RGplusSet`.
  -/
  sorry

end RGplus_generators_S4


section RGplus_generators_S5

variable (k : Type u) [Field k]

/-
Here `A` should eventually be fixed subalgebra `R^G`,
and `RGplusA` should be the irrelevant ideal `R₊^G` inside `A`.
-/
variable (A : Type*) [CommRing A] [Algebra k A]

/-
`R` is the ambient ring.
-/
variable (R : Type*) [CommRing R] [Algebra k R]
variable [Algebra A R] [IsScalarTower k A R]

/-
`toR` is the inclusion `A → R`,
and `ρ` is the Reynolds operator `R → A`.
-/
variable (toR : A →ₐ[k] R)
variable (ρ : R →ₗ[k] A)

/-
`RGplusA` is the ideal `R₊^G` in the fixed ring `A`,
and `extendedRGplus` is the ideal `R₊^G R` in `R`.
-/
variable (RGplusA : Ideal A)
variable (extendedRGplus : Ideal R)

/-
A finite set of generators chosen in Step 4.
-/
variable (s : Finset R)

/-- Step 5 (membership form):
If `f ∈ R₊^G`, then after viewing `f` inside `R`, it lies in the span
of the chosen generators; applying the Reynolds operator to the coefficients
shows that `f` is generated by the corresponding Reynolds images in `A`. -/
theorem mem_span_of_reynolds_generators
    (hs_mem : ∀ x ∈ s, x ∈ extendedRGplus)
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ a : A, ∀ r : R, ρ ((toR a) * r) = a * ρ r) :
    True := by
  /-
  Intended content:

  For `f ∈ RGplusA`, view `f` in `R`.
  Since `toR f ∈ extendedRGplus`, use `hs_span` to write
    toR f = Σ_i x_i * r_i
  with `x_i ∈ s`.

  Apply `ρ`:
    f = ρ (toR f) = Σ_i ρ (x_i * r_i).

  Then use the Reynolds compatibility to rewrite this as a combination
  of the Reynolds images of the generators, with coefficients in `A`.
  -/
  sorry

/-- Step 5 (final finite generation statement):
the irrelevant ideal `R₊^G` in the fixed ring is finitely generated. -/
theorem RGplusA_fg_of_reynolds
    (hs_mem : ∀ x ∈ s, x ∈ extendedRGplus)
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ a : A, ∀ r : R, ρ ((toR a) * r) = a * ρ r) :
    RGplusA.FG := by
  /-
  Intended proof:
  use the previous theorem to show that the finite family obtained from `s`
  (more precisely, their Reynolds images) generates `RGplusA`.
  -/
  sorry

end RGplus_generators_S5

/-
Step 6: Reynolds rewrite.

Mathematically, suppose `f ∈ A` and upstairs in `R` we have written

  `toR f = ∑ x∈s, x * coeff x`

where each `x ∈ s` actually comes from an element of `A`
(via `lift x hx : A` with `toR (lift x hx) = x`).

Apply the Reynolds operator `ρ : R → A` to both sides.
Since `ρ` is the identity on `A`, the left-hand side becomes `f`.
Since `ρ` is linear, it passes through the finite sum.
Finally, using the compatibility
  `ρ ((toR a) * r) = a * ρ r`,
each summand rewrites as

  `ρ (x * coeff x) = lift x hx * ρ (coeff x)`.

Therefore

  `f = ∑ x∈s, lift x hx * ρ (coeff x)`,

so `f` lies in the ideal of `A` generated by the lifted generators.
-/

section ReynoldsRewrite_S6

-- The `Algebra A R` / `IsScalarTower k A R` instances below are part of the
-- ambient Step-5 setup but are not used in the pure Reynolds-rewrite lemmas
-- here; silence the unused-section-variable linter for this blueprint.
set_option linter.unusedSectionVars false

variable (k : Type u) [Field k]

-- `A` is (eventually) the invariant subalgebra `R^G`.
variable (A : Type*) [CommRing A] [Algebra k A]

-- `R` is the ambient ring.
variable (R : Type*) [CommRing R] [Algebra k R]
variable [Algebra A R] [IsScalarTower k A R]

-- Inclusion `A → R` of the fixed subalgebra into the ambient ring.
variable (toR : A →ₐ[k] R)

-- Reynolds operator `R → A`, assumed `k`-linear.
variable (ρ : R →ₗ[k] A)

-- A finite family `s` of elements of `R` (e.g. the generators chosen
-- in Step 4). Each element is assumed below to come from an element of `A`.
variable (s : Finset R)

-- Chosen lifts of elements of `s` to `A`.
-- The hypothesis `hlift x hx : toR (lift x) = x` witnesses that
-- `lift x` really is a preimage of `x` under `toR`.
variable (lift : R → A)

/-- **Step 6 (rewrite form).**

Suppose `f ∈ A` and upstairs in `R` we have written
  `toR f = ∑ x ∈ s, x * coeff x`
where each `x ∈ s` lifts to `lift x ∈ A` with `toR (lift x) = x`.

Applying the Reynolds operator `ρ` to both sides yields
  `f = ∑ x ∈ s, lift x * ρ (coeff x)`.

Proof outline:
1. Apply `ρ` to both sides of `hf`.
2. `ρ (toR f) = f`                        — by `hρ_id`.
3. `ρ (∑ x ∈ s, x * coeff x)
     = ∑ x ∈ s, ρ (x * coeff x)`          — by `LinearMap.map_sum` / `map_sum`.
4. For each `x ∈ s`, rewrite `x = toR (lift x)` and use the
   Reynolds compatibility `ρ (toR a * r) = a * ρ r`:
   `ρ (x * coeff x) = ρ (toR (lift x) * coeff x) = lift x * ρ (coeff x)`.
-/
local notation "Rᴳ₊" => A

theorem reynolds_rewrite
    (f : Rᴳ₊) (a_f : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * a_f x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : Rᴳ₊, ρ (toR a) = a)
    (hρ_mul : ∀ (a : Rᴳ₊) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f = ∑ x ∈ s.attach, lift x.val * ρ (a_f x) := by
  -- (1) Apply ρ to both sides of `hf`:
  --     ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * coeff x).
  have hρf : ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * a_f x) := by
    rw [hf]
  -- (2) LHS collapses to `f` since `ρ` is the identity on the image of `toR`.
  rw [hρ_id] at hρf
  -- (3) `ρ` is `k`-linear, so it commutes with `Finset.sum`.
  rw [map_sum] at hρf
  -- Now `hρf : f = ∑ x ∈ s.attach, ρ (x.val * coeff x)`.
  rw [hρf]
  -- (4) Rewrite each summand using the lift and the Reynolds compatibility.
  refine Finset.sum_congr rfl ?_
  intro x hx
  -- Start from `ρ (toR (lift x.val) * coeff x) = lift x.val * ρ (coeff x)`
  -- (Reynolds compatibility), then use `toR (lift x.val) = x.val` to turn the
  -- LHS into `ρ (x.val * coeff x)`. Using the instantiated `hρ_mul` this way
  -- (rather than `rw [← hlift x.val x.property]` on the goal) avoids
  -- accidentally rewriting the `x.val` that appears inside `coeff x`.
  have hmul := hρ_mul (lift x.val) (a_f x)
  rw [hlift x.val x.property] at hmul
  exact hmul

/-- **Step 6 (ideal-membership form).**

Under the hypotheses of `reynolds_rewrite`, `f` lies in the ideal of `A`
generated by the chosen lifts `{ lift x | x ∈ s }`.

Proof outline:
• Use `reynolds_rewrite` to express `f = ∑ x ∈ s, lift x * ρ (coeff x)`.
• Each summand `lift x * ρ (coeff x)` is a multiple of the generator `lift x`,
  hence lies in `Ideal.span (lift '' s)`.
• A finite sum of ideal elements lies in the ideal (`Ideal.sum_mem`). -/
theorem mem_ideal_span_lift_of_reynolds
    (f : A) (coeff : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  -- Rewrite `f` as `∑ x ∈ s.attach, lift x.val * ρ (coeff x)` via Step 6.
  rw [reynolds_rewrite k A R toR ρ s lift f coeff hf hlift hρ_id hρ_mul]
  -- A finite sum of elements of an ideal lies in the ideal.
  refine Ideal.sum_mem _ ?_
  intro x hx
  -- `lift x.val * ρ (coeff x)` is a right-multiple of the generator `lift x.val`,
  -- and `lift x.val ∈ Ideal.span (lift '' s)` because `x.val ∈ s`.
  refine Ideal.mul_mem_right _ _ ?_
  refine Ideal.subset_span ?_
  exact Set.mem_image_of_mem lift x.property

/-- **Step 6 (ideal-generation corollary).**

If additionally every `f ∈ RGplusA` satisfies a presentation of the above
form (which is supplied by Steps 4–5), then `RGplusA` is contained in the
ideal of `A` generated by the lifts of the chosen generators.

This is the lemma that feeds into Step 7 (finite generation of `R₊^G`). -/
theorem RGplusA_le_span_lift_of_reynolds
    (RGplusA : Ideal A)
    (present : ∀ f ∈ RGplusA, ∃ coeff : s → R,
      toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    RGplusA ≤ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  -- Pointwise: pick the presentation given by `present`, then apply Step 6.
  intro f hf
  obtain ⟨coeff, hcoeff⟩ := present f hf
  exact mem_ideal_span_lift_of_reynolds k A R toR ρ s lift
    f coeff hcoeff hlift hρ_id hρ_mul

end ReynoldsRewrite_S6

/-
Step 7: Finite generation of `A = R^G` as a `k`-algebra.

This is the conclusion of the Hilbert finiteness argument. The previous steps
provide:

* (Step 5) The irrelevant ideal `R₊^G` of `A` is finitely generated as an ideal
  of `A` — `RGplusA_fg_of_reynolds`.
* (Step 1) `A` decomposes as `⨁ d, (𝒜 d ∩ A)`, i.e. `A` carries an `ℕ`-grading
  `𝒜G` inherited from `R` — `fixedSubalgebra_decomposes`.
* (Step 2) For any positively graded `k`-algebra whose irrelevant ideal is
  finitely generated and whose degree-`0` piece is finitely generated as a
  `k`-algebra, the whole algebra is finitely generated as a `k`-algebra —
  `finiteType_of_finitely_generated_irrelevant_ideal`.

Combining these gives `FiniteType k A`. In the GIT setting one typically has
`(𝒜G) 0 = k`, so the `FiniteType k ((𝒜G) 0)` hypothesis is automatic.
-/

section FixedSubalgebra_FiniteType_S7

variable (k : Type u) [Field k]
variable (R : Type*) [CommRing R] [Algebra k R]
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

-- `A = R^G` together with its inherited `ℕ`-grading `𝒜G`.
variable (A : Type*) [CommRing A] [Algebra k A]
variable (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Step 7.**
The fixed subalgebra `A = R^G` is finitely generated as a `k`-algebra,
provided:

* its degree-`0` piece `(𝒜G) 0` is finitely generated as a `k`-algebra
  (automatic when `𝒜G 0 = k`), and
* its irrelevant ideal `R₊^G = ⨁_{d>0} (𝒜G) d` is finitely generated as an
  ideal of `A` — supplied by Step 5 (`RGplusA_fg_of_reynolds`). -/
theorem fixedSubalgebra_finiteType
    [FiniteType k (𝒜G 0)]
    (hfg : (irrelevant 𝒜G).toIdeal.FG) :
    FiniteType k A :=
  finiteType_of_finitely_generated_irrelevant_ideal k A 𝒜G hfg

end FixedSubalgebra_FiniteType_S7
