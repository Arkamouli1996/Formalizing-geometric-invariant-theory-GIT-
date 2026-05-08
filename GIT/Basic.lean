import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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
-- use this one
#check Rep k G

/- the Group algebra -/
#check k[G]

--the direct product of two representations
noncomputable
example (V W : Rep k G) : Rep k G := (V ⨯ W)

--morphisms in the representation category are coerced to functions
-- use this representation
example (V W : Rep k G) (f : V ⟶ W) (v : V) : W := f v

noncomputable
example (V W : Rep k G) : V ⨯ W ⟶ V := CategoryTheory.Limits.prod.fst

--expressing a representation is finite-dimensional
example (M : Rep k G) : Prop := FiniteDimensional k M

--expressing a representation is an indexed product of representations
noncomputable
example {α : Type} (ι : α → Rep k G) : Rep k G := ∏ᶜ ι

--expressing a represesntation is irreductible
example (M : Rep k G) : Prop := IsIrreducible M.ρ
