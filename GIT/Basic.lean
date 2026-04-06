import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Irreducible

universe u

variable {k : Type u} [Field k] (G : Type u) [Group G]

/- Ring of S_n invariants is given by symmetric polynomials -/
#check MvPolynomial.esymmAlgEquiv

/- The Reynolds operator for a finite group -/
#check LinearMap.equivariantProjection

/- A group `G` is linear-algebraic over a field `k` if it is isomorphic to
a subgroup of `GL_n(k)` for some `n` -/
def IsLinearAlgebraic := ∃ (n : Type*), ∃ _ : DecidableEq n, ∃ _ : Fintype n,
    ∃ H : Subgroup (GL n k), Nonempty (H ≃* G)

open Monoid MonoidAlgebra Representation

/- the category of G-representations over k -/
#check Rep k G

/- the Group algebra -/
#check k[G]

--the direct product of two representations
noncomputable
example (V W : Rep k G) : Rep k G := (V ⨯ W)

--morphisms in the representation category are coerced to functions
example (V W : Rep k G) (f : V ⟶ W) (v : V) : W := f v

noncomputable
example (V W : Rep k G) : V ⨯ W ⟶ V := CategoryTheory.Limits.prod.fst

--expressing a representation is finite-dimensional
example (M : Rep k G) : Prop := FiniteDimensional k M

--expressing a representation is an indexed product of representations
noncomputable
example {α : Type} (ι : α → Rep k G) : Rep k G := ∏ᶜ ι

--expressing a represesntation is irreductible
example (M : Rep k G) : Prop := IsIrreducible (Rep.ρ M)


/- Trying to express what it means for a group to be linearly reductive -/
/- Todos:
    ·How to express "V is a finite dimensional representation of G over k"
    ·How to express the direct sum "V ⊕ W" of two representations of G
    ·How to express an indexed direct sum "⊕ i, V_i" of representations of G
    ·How to express that a given representation "V" is a direct sum of indecomposable reps
    ·State the definition of a Reynold's operator
    ·Prove that a group with a Reynold's operator is linearly reductive
    ·Prove that GL_n, SL_n, etc are linearly reductive
-/
