import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic

universe u

variable (k : Type u) [Field k] (R : Type*) [CommRing R] [Algebra k R]
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

open Algebra HomogeneousIdeal

/- internally ℕ-graded `k`-algebra -/
#check GradedAlgebra 𝒜

/- irrelevant ideal `R₊` (kernel of degree-0 projection); Mathlib also writes `𝒜₊` locally -/
#check irrelevant 𝒜

/- as an ordinary ideal of `R` (e.g. for `Ideal.FG`) -/
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
If `R₊` is finitely generated as an ideal and `𝒜 0` is finitely generated as a `k`-algebra
(often `𝒜 0 = k` in GIT), then `R` is finitely generated as a `k`-algebra.
-/
theorem finiteType_of_finitely_generated_irrelevant_ideal
    [FiniteType k (𝒜 0)] (h : (irrelevant 𝒜).toIdeal.FG) :
    FiniteType k R := sorry
