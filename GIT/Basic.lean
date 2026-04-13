import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Rep
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Algebra.Ring.Action.Basic

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

-- 1. Reductive => ∃ Reynold's operator
--      - learn about natural transformations
-- 1.5 Reynolds operator on k-alg R-> R^G shatring from reynolds oeprator
--     on vector spaces assuming locally finite
--      - express local finiteness
--      - define the projection locally, show well-definied
section LocallyFinite

variable {k : Type*} [CommSemiring k] {G : Type*} [Monoid G]
    {R : Type*} [AddCommMonoid R] [Module k R] [DistribMulAction G R]

/-- A `DistribMulAction` of `G` on a `k`-module `R` is locally finite if every element
of `R` is contained in a finite-dimensional `G`-stable `k`-submodule. -/
def Representation.IsLocallyFinite (k : Type*) [CommSemiring k] (G : Type*) [Monoid G]
    (R : Type*) [AddCommMonoid R] [Module k R] [DistribMulAction G R] : Prop :=
  ∀ r : R, ∃ V : Submodule k R, Module.Finite k V ∧
    (∀ (g : G) (v : V), (g • (v : R)) ∈ V) ∧ r ∈ V

/-- Every action of a finite monoid is locally finite: the orbit of any element
spans a finitely generated submodule. -/
theorem Representation.isLocallyFinite_of_finite (k : Type*) [CommSemiring k] (G : Type*)
    [Monoid G] [Finite G] (R : Type*) [AddCommMonoid R] [Module k R]
    [DistribMulAction G R] [SMulCommClass G k R] :
    Representation.IsLocallyFinite k G R := by
  intro r
  refine ⟨Submodule.span k (Set.range (fun g : G => g • r)), ?_, ?_, ?_⟩
  · exact Module.Finite.span_of_finite k (Set.finite_range _)
  · intro g v
    change g • (v : R) ∈ Submodule.span k (Set.range (fun g' : G => g' • r))
    have hv : (v : R) ∈ Submodule.span k (Set.range (fun g' : G => g' • r)) := v.property
    exact Submodule.span_induction
      (mem := fun x ⟨g', hg'⟩ => hg' ▸ Submodule.subset_span ⟨g * g', mul_smul g g' r⟩)
      (zero := by simp)
      (add := fun x y _ _ hx hy => by rw [smul_add]; exact Submodule.add_mem _ hx hy)
      (smul := fun a x _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ a hx)
      hv
  · exact Submodule.subset_span ⟨1, one_smul G r⟩

end LocallyFinite

section ReynoldsOperator

variable (k : Type*) [CommSemiring k] (G : Type*) [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (R : Type*) [AddCommMonoid R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]

/-- The Reynolds operator for a finite group `G` acting on a `k`-module `R`.
This is the `k`-linear projection `R →ₗ[k] R` onto the submodule of `G`-invariants,
defined as `(1/|G|) ∑ g, ρ(g)`. -/
noncomputable def reynoldsOperator : R →ₗ[k] R :=
  (Representation.ofDistribMulAction k G R).averageMap

/-- The Reynolds operator maps every element into the submodule of `G`-invariants. -/
theorem reynoldsOperator_mem_invariants (r : R) :
    reynoldsOperator k G R r ∈ (Representation.ofDistribMulAction k G R).invariants :=
  (Representation.ofDistribMulAction k G R).averageMap_invariant r

/-- The Reynolds operator fixes every `G`-invariant element. -/
theorem reynoldsOperator_id (r : R)
    (hr : r ∈ (Representation.ofDistribMulAction k G R).invariants) :
    reynoldsOperator k G R r = r :=
  (Representation.ofDistribMulAction k G R).averageMap_id r hr

end ReynoldsOperator

section GeneralReynolds

universe uV

/-- A group `G` is linearly reductive over `k` if every finite-dimensional representation
is completely reducible (every subrepresentation has a complement). -/
class IsLinearlyReductive (k : Type*) [Field k] (G : Type*) [Group G] : Prop where
  isSemisimple : ∀ (V : Type uV) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), IsSemisimpleRepresentation ρ

/-- Finite groups with invertible cardinality are linearly reductive. -/
instance IsLinearlyReductive.of_fintype (k : Type*) [Field k] (G : Type*) [Group G]
    [Fintype G] [Invertible (Fintype.card G : k)] :
    IsLinearlyReductive k G where
  isSemisimple V _ _ _ ρ := by
    haveI : NeZero (Nat.card G : k) := by
      rw [Nat.card_eq_fintype_card]
      exact ⟨Invertible.ne_zero (Fintype.card G : k)⟩
    exact ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule.mpr inferInstance

variable (k : Type*) [Field k] (G : Type*) [Group G]

/-- The invariants of a representation form a subrepresentation. -/
noncomputable def Representation.invariantSubrepresentation
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv ⊢
    intro g'; simp [hv]

/-- A linearly reductive group admits a `k`-linear projection onto the invariants
of any finite-dimensional representation, with the projection being `G`-equivariant. -/
theorem IsLinearlyReductive.exists_reynolds_projection
    (hlr : IsLinearlyReductive.{uV} k G)
    {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) :
    ∃ π : V →ₗ[k] V, LinearMap.IsProj ρ.invariants π ∧
      ∀ (g : G) (v : V), π (ρ g v) = π v := by
  have hss : IsSemisimpleRepresentation ρ := hlr.isSemisimple V ρ
  obtain ⟨W, hW⟩ := hss.exists_isCompl ρ.invariantSubrepresentation
  sorry

/-- Given a linearly reductive group `G` acting locally finitely on a `k`-module `R`,
there exists a `k`-linear projection `R →ₗ[k] R` onto the `G`-invariants. -/
theorem exists_reynolds_of_locallyFinite
    (R : Type*) [AddCommGroup R] [Module k R] [DistribMulAction G R] [SMulCommClass G k R]
    [IsLinearlyReductive k G]
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : R →ₗ[k] R, LinearMap.IsProj (Representation.ofDistribMulAction k G R).invariants π ∧
      ∀ (g : G) (r : R), π ((Representation.ofDistribMulAction k G R) g r) = π r :=
  sorry

end GeneralReynolds

-- 2. If R is a graded k-algebra, R_+ is a finite generated ideal,
--    then R finitely generated as a k-algebra
--      - facts about graded algebras
--      - is R_+ in Mathlib as ideal? as graded?
-- 3. Group acting on a graded k-algebra
--      - looks for group acting on a graded k-algebra
--      - R^G is a graded k-algebra?
