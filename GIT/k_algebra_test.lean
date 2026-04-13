import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic

universe u

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
