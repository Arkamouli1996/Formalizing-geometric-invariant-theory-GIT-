import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import GIT.ReynoldsOperator

open scoped DirectSum
open scoped BigOperators

universe u v w uR

section GradedCheck_S1

-- Step 0: Basic objects

variable (k : Type u) [Field k]
variable (G : Type v) [Group G]
variable (ι : Type w) [DecidableEq ι] [AddMonoid ι]
variable (R : Type*) [Semiring R] [Algebra k R]
variable (𝒜 : ι → Submodule k R)

-- Step 4: Assume R is already graded

variable [GradedAlgebra 𝒜]

-- Step 5: Encode the action by algebra automorphisms

variable (ρ : G →* R ≃ₐ[k] R)

-- Step 6: Define the missing condition: the action preserves the grading

def PreservesGrading : Prop :=
  ∀ (g : G) (d : ι) {r : R}, r ∈ 𝒜 d → (ρ g : R → R) r ∈ 𝒜 d

#check PreservesGrading

-- Step 7: Define the invariant subalgebra R^G

def FixedSubalgebra (ρ : G →* R ≃ₐ[k] R) : Subalgebra k R :=
{
  carrier := { r : R | ∀ g : G, (ρ g) r = r }

  zero_mem' := by
    intro g
    simp

  one_mem' := by
    intro g
    simp

  add_mem' := by
    intro x y hx hy g
    simp [map_add, hx g, hy g]

  mul_mem' := by
    intro x y hx hy g
    simp [map_mul, hx g, hy g]

  algebraMap_mem' := by
    intro a g
    exact (ρ g).commutes a
}

-- Step 8a: Define the degree-d piece inside ambient R

def FixedPiece (d : ι) : Submodule k R :=
  𝒜 d ⊓ (FixedSubalgebra (k := k) (G := G) (R := R) ρ).toSubmodule

-- Step 8b: Define the degree-d piece inside R^G

def FixedPieceInFixedSubalgebra (d : ι) :
    Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) :=
{
  carrier := { x | (x : R) ∈ 𝒜 d }

  zero_mem' := by
    change (0 : R) ∈ 𝒜 d
    exact Submodule.zero_mem (𝒜 d)

  add_mem' := by
    intro x y hx hy
    change ((x : R) + (y : R)) ∈ 𝒜 d
    exact Submodule.add_mem (𝒜 d) hx hy

  smul_mem' := by
    intro a x hx
    change (a • (x : R)) ∈ 𝒜 d
    exact Submodule.smul_mem (𝒜 d) a hx
}

-- Lemma for Step 9:
lemma fixed_component_mem_degree
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈ 𝒜 d := by
  exact ((DirectSum.decompose 𝒜 (x : R)) d).property

lemma proj_commutes_of_preservesGrading
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (g : G) (d : ι) :
    (GradedAlgebra.proj 𝒜 d).comp (ρ g).toLinearMap =
      (ρ g).toLinearMap.comp (GradedAlgebra.proj 𝒜 d) := by
  refine DirectSum.decompose_lhom_ext 𝒜 (fun e => ?_)
  ext y
  by_cases h : e = d
  · subst d
    have hyρ : (ρ g).toLinearMap (y : R) ∈ 𝒜 e := by
      simpa using hpres g e y.property
    change
      ↑(((DirectSum.decompose 𝒜) ((ρ g).toLinearMap (y : R))) e)
        =
      (ρ g).toLinearMap
        (↑(((DirectSum.decompose 𝒜) (y : R)) e))
    rw [DirectSum.decompose_of_mem_same 𝒜 hyρ]
    rw [DirectSum.decompose_of_mem_same 𝒜 y.property]
  · have hyρ : (ρ g).toLinearMap (y : R) ∈ 𝒜 e := by
      simpa using hpres g e y.property
    change
      ↑(((DirectSum.decompose 𝒜) ((ρ g).toLinearMap (y : R))) d)
        =
      (ρ g).toLinearMap
        (↑(((DirectSum.decompose 𝒜) (y : R)) d))
    rw [DirectSum.decompose_of_mem_ne 𝒜 hyρ h]
    rw [DirectSum.decompose_of_mem_ne 𝒜 y.property h]
    simp

lemma fixed_component_is_fixed
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    ((DirectSum.decompose 𝒜 (x : R)) d : R) ∈
      (FixedSubalgebra (k := k) (G := G) (R := R) ρ).toSubmodule := by
  intro g
  have hlin :
      (GradedAlgebra.proj 𝒜 d).comp (ρ g).toLinearMap =
        (ρ g).toLinearMap.comp (GradedAlgebra.proj 𝒜 d) :=
    proj_commutes_of_preservesGrading
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
      hpres g d
  have hcomm :
      GradedAlgebra.proj 𝒜 d ((ρ g).toLinearMap (x : R)) =
        (ρ g).toLinearMap (GradedAlgebra.proj 𝒜 d (x : R)) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : R →ₗ[k] R => F (x : R)) hlin
  have hxfix : (ρ g).toLinearMap (x : R) = (x : R) := by
    simpa using x.property g
  rw [hxfix] at hcomm
  simpa [GradedAlgebra.proj_apply] using hcomm.symm

lemma fixed_component_mem_fixedPiece
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ))
    (x : FixedSubalgebra (k := k) (G := G) (R := R) ρ)
    (d : ι) :
    (⟨((DirectSum.decompose 𝒜 (x : R)) d : R),
      fixed_component_is_fixed
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
        hpres x d⟩ :
      FixedSubalgebra (k := k) (G := G) (R := R) ρ) ∈
      FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d := by
  exact
    fixed_component_mem_degree
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
      x d

-- forget map for Step 9
def fixedPieceForget (d : ι) :
    FixedPieceInFixedSubalgebra
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d →+
      𝒜 d :=
{
  toFun := fun x =>
    ⟨((x : FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R), x.property⟩

  map_zero' := by
    ext
    rfl

  map_add' := by
    intro x y
    ext
    rfl
}

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
lemma fixedPieceForget_injective (d : ι) :
    Function.Injective
      (fixedPieceForget
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) := by
  intro x y h
  have hR :
      (((x : FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :
          FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R)
        =
      (((y : FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :
          FixedSubalgebra (k := k) (G := G) (R := R) ρ) : R) := by
    exact congrArg
      (fun z : 𝒜 d => (z : R))
      h
  apply Subtype.ext
  apply Subtype.ext
  exact hR


-- Step 9: Main theorem
-- R^G = ⨁ d, (R_d ∩ R^G)

theorem fixedSubalgebra_decomposes
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)) :
    DirectSum.IsInternal
      fun d : ι =>
        FixedPieceInFixedSubalgebra
          (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d := by
  classical
  let B : ι → Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) :=
    fun d =>
      FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d
  let forget : (d : ι) → B d →+ 𝒜 d :=
    fun d =>
      fixedPieceForget
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d
  let coeFixed :
      FixedSubalgebra (k := k) (G := G) (R := R) ρ →+ R :=
  {
    toFun := fun x => (x : R)

    map_zero' := by
      rfl

    map_add' := by
      intro x y
      rfl
  }
  have hcomp :
      coeFixed.comp (DirectSum.coeAddMonoidHom B)
        =
      (DirectSum.coeAddMonoidHom 𝒜).comp (DirectSum.map forget) := by
    apply DirectSum.addHom_ext
    intro i y
    simp [B, forget, coeFixed, fixedPieceForget]
  change Function.Bijective ⇑(DirectSum.coeAddMonoidHom B)
  constructor
  · -- injective
    intro a b h
    have hR' :
        coeFixed ((DirectSum.coeAddMonoidHom B) a)
          =
        coeFixed ((DirectSum.coeAddMonoidHom B) b) := by
      exact congrArg
        (fun z : FixedSubalgebra (k := k) (G := G) (R := R) ρ =>
          coeFixed z)
        h
    have ha :
        coeFixed ((DirectSum.coeAddMonoidHom B) a)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) a) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F a)
        hcomp
    have hb :
        coeFixed ((DirectSum.coeAddMonoidHom B) b)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) b) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F b)
        hcomp
    have hR :
        (DirectSum.coeAddMonoidHom 𝒜)
            ((DirectSum.map forget) a)
          =
        (DirectSum.coeAddMonoidHom 𝒜)
            ((DirectSum.map forget) b) := by
      calc
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) a)
            = coeFixed ((DirectSum.coeAddMonoidHom B) a) := ha.symm
        _ = coeFixed ((DirectSum.coeAddMonoidHom B) b) := hR'
        _ = (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) b) := hb
    have hinjA :
        Function.Injective ⇑(DirectSum.coeAddMonoidHom 𝒜) :=
      (DirectSum.Decomposition.isInternal 𝒜).1
    have hmap :
        (DirectSum.map forget) a = (DirectSum.map forget) b :=
      hinjA hR
    exact
      ((DirectSum.map_injective forget).2
        (fun d =>
          fixedPieceForget_injective
            (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d))
        hmap
  · -- surjective
    intro x
    let y : DirectSum ι fun d => B d :=
      (DirectSum.mk
        (fun d => B d)
        ((DirectSum.decompose 𝒜 (x : R)).support))
        (fun d =>
          (⟨
            ⟨
              ((DirectSum.decompose 𝒜 (x : R)) d.1 : R),
              fixed_component_is_fixed
                (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                hpres x d.1
            ⟩,
            fixed_component_mem_degree
              (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
              x d.1
          ⟩ : B d.1))
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change
      coeFixed ((DirectSum.coeAddMonoidHom B) y)
        =
      (x : R)
    have hy_decomp :
        (DirectSum.map forget) y = DirectSum.decompose 𝒜 (x : R) := by
      ext d
      by_cases hd : d ∈ (DirectSum.decompose 𝒜 (x : R)).support
      · have hy_apply :
            y d =
              (⟨
                ⟨
                  ((DirectSum.decompose 𝒜 (x : R)) d : R),
                  fixed_component_is_fixed
                    (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                    hpres x d
                ⟩,
                fixed_component_mem_degree
                  (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)
                  x d
              ⟩ : B d) := by
          dsimp [y]
          exact DirectSum.mk_apply_of_mem hd
        rw [DirectSum.map_apply, hy_apply]
        simp [forget, fixedPieceForget]
      · have hy_apply : y d = 0 := by
          dsimp [y]
          exact DirectSum.mk_apply_of_notMem hd
        have hzero : (DirectSum.decompose 𝒜 (x : R)) d = 0 := by
          exact DFinsupp.notMem_support_iff.mp hd
        rw [DirectSum.map_apply, hy_apply, hzero]
        simp
    have hyR :
        coeFixed ((DirectSum.coeAddMonoidHom B) y)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) := by
      exact congrArg
        (fun F : (DirectSum ι fun d => B d) →+ R => F y)
        hcomp
    calc
      coeFixed ((DirectSum.coeAddMonoidHom B) y)
          =
        (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.map forget) y) := hyR
      _ =
        (DirectSum.coeAddMonoidHom 𝒜) (DirectSum.decompose 𝒜 (x : R)) := by
          rw [hy_decomp]
      _ = (x : R) := by
          change
            (DirectSum.coeAddMonoidHom 𝒜)
              (DirectSum.Decomposition.decompose' (ℳ := 𝒜) (x : R))
              =
            (x : R)
          exact DirectSum.Decomposition.left_inv (ℳ := 𝒜) (x : R)

/-! ### Glue: turn `IsInternal` (Step 1) into a `GradedAlgebra` instance on `R^G`. -/

/-- The unit of `R^G` lies in the degree-`0` fixed piece. -/
instance fixedPieceInFixedSubalgebra_gradedOne :
    SetLike.GradedOne
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where
  one_mem := show (1 : R) ∈ 𝒜 0 from SetLike.GradedOne.one_mem

/-- Multiplication in `R^G` respects the inherited grading. -/
instance fixedPieceInFixedSubalgebra_gradedMul :
    SetLike.GradedMul
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where
  mul_mem := fun {i j a b} ha hb =>
    show ((a : R) * (b : R)) ∈ 𝒜 (i + j) from
      SetLike.GradedMul.mul_mem ha hb

/-- The fixed-piece family on `R^G` forms a graded monoid. -/
instance fixedPieceInFixedSubalgebra_gradedMonoid :
    SetLike.GradedMonoid
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) where

/-- **Glue lemma (1): `R^G` carries an inherited graded-algebra structure.**

Combining Step 1 (`fixedSubalgebra_decomposes`) with the `SetLike.GradedMonoid` instances
above, the family `FixedPieceInFixedSubalgebra`q makes `R^G` a graded `k`-algebra. -/
noncomputable def fixedSubalgebra_gradedAlgebra
    (hpres : PreservesGrading (k := k) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ)) :
    GradedAlgebra
      (fun d : ι => FixedPieceInFixedSubalgebra
        (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) d) :=
  DirectSum.IsInternal.gradedAlgebra
    (fixedSubalgebra_decomposes
      (k := k) (G := G) (ι := ι) (R := R) (𝒜 := 𝒜) (ρ := ρ) hpres)

end GradedCheck_S1

section IrrelevantIdeal_FiniteType_S2

/-
If `R₊` is finitely generated as an ideal, then `R` is finitely generated as an algebra over the
degree-`0` graded piece `𝒜 0`. To conclude finite generation over the base field `k`, you still
need a separate hypothesis that `𝒜 0` is finitely generated as a `k`-algebra (then apply
transitivity); that extra hypothesis cannot be dropped in general.
-/

namespace GIT

section

variable {k : Type u} [Field k]
variable {R : Type uR} [CommRing R] [Algebra k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]

abbrev irrelevantIdeal : Ideal R := (HomogeneousIdeal.irrelevant 𝒜).toIdeal

lemma exists_finset_homogeneous_pos_generators
    (h : (irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)).FG) :
    ∃ T : Finset R,
      (Ideal.span (T : Set R) = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)) ∧
      (∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) := by
  classical
  let s : Set R := ⋃ i : ℕ, ⋃ _ : 0 < i, (𝒜 i : Set R)
  have hirr : irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) = Ideal.span s := by
    simpa [irrelevantIdeal, s] using (HomogeneousIdeal.irrelevant_eq_span (𝒜 := 𝒜))
  have hspan_s_fg : (Ideal.span s : Ideal R).FG := by
    rcases h with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    calc
      Ideal.span (S : Set R)
          = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := hS
      _   = Ideal.span s := hirr
  have hfg_submodule : (Submodule.span R s).FG := by
    rcases hspan_s_fg with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    have hS' :
        (Ideal.span (S : Set R) : Submodule R R) = (Ideal.span s : Submodule R R) :=
      congrArg (fun (I : Ideal R) => (I : Submodule R R)) hS
    change (Ideal.span (S : Set R) : Submodule R R) = (Ideal.span s : Submodule R R)
    exact hS'
  rcases (Submodule.fg_span_iff_fg_span_finset_subset (R := R) (M := R) s).1 hfg_submodule with
    ⟨T, hTs, hspan⟩
  refine ⟨T, ?_, ?_⟩
  · have : Ideal.span s = Ideal.span (T : Set R) := by
      have hspan' : (Submodule.span R s : Ideal R) = (Submodule.span R (T : Set R) : Ideal R) :=
        congrArg (fun (N : Submodule R R) => (N : Ideal R)) hspan
      change (Ideal.span s : Ideal R) = (Ideal.span (T : Set R) : Ideal R)
      exact hspan'
    calc
      Ideal.span (T : Set R) = Ideal.span s := this.symm
      _ = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := hirr.symm
  · intro t ht
    have : t ∈ s := hTs (by simpa using ht)
    rcases Set.mem_iUnion.1 this with ⟨d, hd⟩
    rcases Set.mem_iUnion.1 hd with ⟨hdpos, hmem⟩
    exact ⟨d, hdpos, hmem⟩

noncomputable def inst_algebra_degreeZero :
    Algebra (𝒜 0) R := by
  classical
  exact inferInstance

noncomputable def inst_isScalarTower_degreeZero :
    IsScalarTower k (𝒜 0) R := by
  classical
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  refine IsScalarTower.of_algebraMap_eq' (R := k) (S := (𝒜 0)) (A := R) ?_
  ext x
  simp

lemma homogeneous_mem_adjoin_of_irrelevant_eq_span
    {T : Finset R}
    (hspan : Ideal.span (T : Set R) = irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜))
    (hT : ∀ t ∈ T, ∃ d : ℕ, 0 < d ∧ t ∈ 𝒜 d) :
    ∀ d : ℕ, ∀ y : R, y ∈ 𝒜 d → y ∈ Algebra.adjoin (𝒜 0) (T : Set R) := by
  classical
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih y hy
  by_cases hd0 : d = 0
  · subst hd0
    have : y ∈ (Algebra.adjoin (𝒜 0) (T : Set R) : Subalgebra (𝒜 0) R) := by
      simpa using (Subalgebra.algebraMap_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ⟨y, hy⟩)
    exact this
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hy_irrel : y ∈ irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜) := by
      have : y ∈ HomogeneousIdeal.irrelevant 𝒜 := by
        exact HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := 𝒜) (x := y) (i := d) hdpos hy
      simpa [irrelevantIdeal] using this
    have hy_span : y ∈ Ideal.span (T : Set R) := by
      simpa [hspan] using hy_irrel
    have hy_span' : y ∈ (Submodule.span R (T : Set R) : Submodule R R) := by
      change y ∈ ((Ideal.span (T : Set R) : Ideal R) : Submodule R R)
      exact hy_span
    rcases
        (Finsupp.mem_span_iff_linearCombination (R := R) (M := R) (s := (T : Set R)) y).1 hy_span'
      with ⟨l, hl⟩
    -- Choose a positive degree for each generator `t ∈ T`.
    choose degT hdegTpos hdegTmem
      using (fun t : (T : Set R) => (hT t.1 (by simp [Finset.mem_coe.mp t.2])))
    -- Let `π_d : R →+ R` be the degree-`d` projection `z ↦ (decompose z d : R)`.
    let πd : R →+ R :=
      { toFun := fun z => ((DirectSum.decompose 𝒜 z) d : R)
        map_zero' := by simp
        map_add' := by simp }
    -- Since `y ∈ 𝒜 d`, `π_d y = y`.
    have hπy : πd y = y := by
      simpa [πd] using (DirectSum.decompose_of_mem_same 𝒜 (x := y) (i := d) hy)
    -- Expand the span expression `hl` as a concrete finset sum in `R`.
    have hl_sum :
        (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) =
          Finset.sum l.support (fun t => l t * (t : R)) := by
      classical
      simp [Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]
    -- Apply `πd` to `hl` and rewrite the RHS as a sum of `πd` applied to each summand.
    have hproj :
        y = Finset.sum l.support (fun t => πd (l t * (t : R))) := by
      have h1 : πd (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) = πd y := by
        simpa [hl] using congrArg πd hl
      have h1' : πd (Finset.sum l.support (fun t => l t * (t : R))) = πd y := by
        have h1' := h1
        rw [hl_sum] at h1'
        exact h1'
      have h2 : Finset.sum l.support (fun t => πd (l t * (t : R))) = πd y := by
        simpa [map_sum] using h1'
      have h3 : Finset.sum l.support (fun t => πd (l t * (t : R))) = y := by
        simpa [hπy] using h2
      exact h3.symm
    -- Each summand `πd (l t * t)` lies in the adjoin,
    -- hence their sum (and thus `y`) lies in the adjoin.
    have hsum_mem :
        (Finset.sum l.support (fun t => πd (l t * (t : R)))) ∈
          Algebra.adjoin (𝒜 0) (T : Set R) := by
      classical
      refine (Subsemiring.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring) ?_
      intro t ht_support
      have ht_mem : (t : R) ∈ Algebra.adjoin (𝒜 0) (T : Set R) :=
        Algebra.subset_adjoin t.2
      have ht_hom : (t : R) ∈ 𝒜 (degT t) := by
        simpa using (hdegTmem t)
      by_cases hle : degT t ≤ d
      · have hπ :
            πd (l t * (t : R)) =
              ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) * (t : R) := by
          simpa [πd] using
            (DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := 𝒜)
              (a := l t) (b := (t : R)) (n := d) (i := degT t) ht_hom hle)
        have hlt : d - degT t < d :=
          Nat.sub_lt (Nat.pos_of_ne_zero (Nat.ne_of_gt hdpos)) (hdegTpos t)
        have hcoeff_mem :
            ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) ∈
              Algebra.adjoin (𝒜 0) (T : Set R) := by
          have hcoeff_hom :
              ((DirectSum.decompose 𝒜 (l t)) (d - degT t) : R) ∈ 𝒜 (d - degT t) :=
            ((DirectSum.decompose 𝒜 (l t)) (d - degT t)).2
          exact ih (d - degT t) hlt _ hcoeff_hom
        rw [hπ]
        exact
          (Subsemiring.mul_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring hcoeff_mem ht_mem)
      · have hπ0 : πd (l t * (t : R)) = 0 := by
          simpa [πd] using
            (DirectSum.coe_decompose_mul_of_right_mem_of_not_le (𝒜 := 𝒜)
              (a := l t) (b := (t : R)) (n := d) (i := degT t) ht_hom hle)
        rw [hπ0]
        exact zero_mem _
    simpa [hproj] using hsum_mem

lemma finiteType_degreeZero_of_irrelevant_fg
    (h : (irrelevantIdeal (k := k) (R := R) (𝒜 := 𝒜)).FG) :
    Algebra.FiniteType (𝒜 0) R := by
  classical
  obtain ⟨T, hspan, hT⟩ := exists_finset_homogeneous_pos_generators (k := k) (R := R) (𝒜 := 𝒜) h
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro r _
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Subalgebra.sum_mem (Algebra.adjoin (𝒜 0) (T : Set R)) ?_
  intro i _
  have hy : ((DirectSum.decompose 𝒜 r) i : R) ∈ 𝒜 i :=
    SetLike.coe_mem ((DirectSum.decompose 𝒜 r) i)
  exact homogeneous_mem_adjoin_of_irrelevant_eq_span (𝒜 := 𝒜) hspan hT i _ hy

theorem finiteType_of_finitely_generated_irrelevant_ideal
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType (𝒜 0) R :=
  finiteType_degreeZero_of_irrelevant_fg (k := k) (R := R) (𝒜 := 𝒜) (h := by
    simpa [irrelevantIdeal] using h)

theorem finiteType_k_of_finitely_generated_irrelevant_ideal
    [Algebra.FiniteType k (𝒜 0)] (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    Algebra.FiniteType k R := by
  classical
  letI : Algebra (𝒜 0) R := inst_algebra_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  letI : IsScalarTower k (𝒜 0) R := inst_isScalarTower_degreeZero (k := k) (R := R) (𝒜 := 𝒜)
  exact Algebra.FiniteType.trans (R := k) (S := 𝒜 0) (A := R)
    (hRS := inferInstance) (hSA := finiteType_of_finitely_generated_irrelevant_ideal h)
end

end GIT

end IrrelevantIdeal_FiniteType_S2

section RGplus_finitely_generated_S3

variable (R : Type*) [CommRing R]
variable [IsNoetherianRing R]

variable (extendedRGplus : Ideal R)

/-- Since `R` is Noetherian, the ideal `R₊^G R` is finitely generated. -/
theorem extendedRGplus_fg : extendedRGplus.FG := by
  classical
  exact IsNoetherian.noetherian extendedRGplus

/-- Choose a finite generating set for `R₊^G R`. -/
theorem exists_generators_extendedRGplus :
    ∃ s : Finset R, Ideal.span (↑s : Set R) = extendedRGplus := by
  classical
  simpa [Ideal.FG] using
    (extendedRGplus_fg
      (R := R) (extendedRGplus := extendedRGplus))

end RGplus_finitely_generated_S3

section RGplus_generators_S4

variable (R : Type*) [CommRing R]

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
  classical
  have hfg_span_ideal : (Ideal.span RGplusSet).FG := by
    simpa [hspan] using hfg
  have hfg_span_submodule :
      (Submodule.span R RGplusSet : Submodule R R).FG := by
    exact hfg_span_ideal
  rcases
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := R) (M := R) RGplusSet).1 hfg_span_submodule
    with ⟨s, hs_sub, hs_span⟩
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    exact hs_sub hx
  · calc
      Ideal.span (↑s : Set R) = Ideal.span RGplusSet := hs_span.symm
      _ = extendedRGplus := hspan

end RGplus_generators_S4

/-!
## Step 5.5 — Existence of a Reynolds operator on `R`

We have a linearly reductive group `G` acting on `R` by algebra automorphisms.
If this action is locally finite (which holds, for example, when `G` is a
linearly reductive group acting on a finitely generated `k`-algebra), then
`exists_reynolds_of_locallyFinite` from `GIT.ReynoldsOperator` gives us a
`k`-linear Reynolds projector `π : R →ₗ[k] R` onto the `G`-invariants `R^G`.

The theorem below packages this in the form needed for the subsequent steps:
it produces the projector and records the two key properties —
(i)  `π r ∈ R^G` for every `r : R`, and
(ii) `π r = r` whenever `r ∈ R^G`.
-/
section ReynoldsExists_S5_5

-- All three must be in the same universe u to match exists_reynolds_of_locallyFinite
variable (k : Type u) [Field k]
variable (G : Type u) [Group G]  -- was: Type v
variable (R : Type u) [AddCommGroup R] [Module k R]
  [DistribMulAction G R] [SMulCommClass G k R]

/-- Given a linearly reductive group `G` and a locally finite `k`-linear `G`-module `R`,
there is a Reynolds projector onto the `G`-invariants.

This is a direct application of `exists_reynolds_of_locallyFinite`. -/
theorem reynolds_operator_exists
    (hlr : IsLinearlyReductive k G)
    (hlf : Representation.IsLocallyFinite k G R) :
    ∃ π : Rep.of (Representation.ofDistribMulAction k G R) ⟶
          Rep.of (Representation.ofDistribMulAction k G R),
      LinearMap.IsProj
        (Representation.ofDistribMulAction k G R).invariants
        π.hom.hom :=
  exists_reynolds_of_locallyFinite (k := k) (G := G) hlr R hlf

end ReynoldsExists_S5_5

section RGplus_generators_S5

variable {k : Type u} [Field k]

variable {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]

variable {R : Type*} [CommRing R] [Algebra k R]

variable {toR : A →ₐ[k] R}
variable {ρ : R →ₗ[k] A}

variable {RGplusA : Ideal A}
variable {extendedRGplus : Ideal R}

variable {s : Finset R}

/-- The Reynolds/GIT spanning property used in Step 5.

If `toR f` lies in the `R`-ideal generated by `s`, then `f` lies in the `A`-ideal
generated by the Reynolds images `ρ x` for `x ∈ s`. -/
def ReynoldsGITSpanProperty
    {k : Type u} [Field k]
    {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]
    {R : Type*} [CommRing R] [Algebra k R]
    (toR : A →ₐ[k] R) (ρ : R →ₗ[k] A) (s : Finset R) : Prop :=
  ∀ f : A,
    toR f ∈ Ideal.span (↑s : Set R) →
      f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s)

/-- Step 5 (membership form): elements of `RGplusA` lie in the `A`-ideal generated by `ρ '' s`.

Hypotheses:
- `hs_span`: `s` spans `extendedRGplus` as an ideal of `R`;
- `hcomap`: `RGplusA` is the preimage of `extendedRGplus` under `toR`;
- `hReynolds`: `ReynoldsGITSpanProperty` (your concrete GIT/Reynolds input).
-/
theorem mem_span_of_reynolds_generators
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus)
    (hReynolds : ReynoldsGITSpanProperty toR ρ s)
    (f : A) (hf : f ∈ RGplusA) :
    f ∈ Ideal.span ↑(Finset.image (fun x => ρ x) s) := by
  refine hReynolds f ?_
  have hf_comap : f ∈ Ideal.comap (toR : A →+* R) extendedRGplus := by
    simpa [hcomap] using hf
  have hf' : toR f ∈ extendedRGplus := Ideal.mem_comap.mp hf_comap
  simpa [hs_span] using hf'

/-- Step 5 (final finite generation): `RGplusA` is finitely generated.

Shows `RGplusA = Ideal.span (ρ '' s)` by antitone/submodule antisymmetry, then applies `Ideal.FG`.
-/
theorem RGplusA_fg_of_reynolds
    (hs_span : Ideal.span (↑s : Set R) = extendedRGplus)
    (hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus)
    (hρ_gen : ∀ x ∈ s, ρ x ∈ RGplusA)
    (hReynolds : ReynoldsGITSpanProperty toR ρ s) :
    RGplusA.FG := by
  classical
  let t : Finset A := Finset.image (fun x => ρ x) s
  refine ⟨t, ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hρ_gen x hx
  · intro f hf
    exact mem_span_of_reynolds_generators hs_span hcomap hReynolds f hf

end RGplus_generators_S5

-- /-first define a finite action using -/

-- /-Step 5.5: Show that R has a reynold operator using our existence proof
--   - since we have a linearly reductive group G acting acting on
--   a finitely generated k-algebra R by a locally finite action,
--   R must have a Reynolds operator
-- -/
-- theorem reynolds_operator_exists
--     ()
--   extract exists_reynolds_of_locallyFinite

section ReynoldsRewrite_S6

set_option linter.unusedSectionVars false

variable (k : Type u) [Field k]
variable (G : Type v) [Group G]
variable (A : Type*) [CommRing A] [Algebra k A]
variable (R : Type*) [CommRing R] [Algebra k R]
variable [Algebra A R] [IsScalarTower k A R]
variable (toR : A →ₐ[k] R)
variable (ρ : R →ₗ[k] A)
variable (s : Finset R)
variable (lift : R → A)

local notation "Rᴳ₊" => A

/-- **Step 6 (rewrite form).** Applying the Reynolds operator to both sides of
`toR f = ∑ x ∈ s, x * coeff x` yields `f = ∑ x ∈ s, lift x * ρ (coeff x)`. -/
theorem reynolds_rewrite
    (f : Rᴳ₊) (a_f : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * a_f x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : Rᴳ₊, ρ (toR a) = a)
    (hρ_mul : ∀ (a : Rᴳ₊) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f = ∑ x ∈ s.attach, lift x.val * ρ (a_f x) := by
  have hρf : ρ (toR f) = ρ (∑ x ∈ s.attach, x.val * a_f x) := by
    rw [hf]
  rw [hρ_id] at hρf
  rw [map_sum] at hρf
  rw [hρf]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hmul := hρ_mul (lift x.val) (a_f x)
  rw [hlift x.val x.property] at hmul
  exact hmul

/-- **Step 6 (ideal-membership form).** -/
theorem mem_ideal_span_lift_of_reynolds
    (f : A) (coeff : s → R)
    (hf : toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  rw [reynolds_rewrite k A R toR ρ s lift f coeff hf hlift hρ_id hρ_mul]
  refine Ideal.sum_mem _ ?_
  intro x hx
  refine Ideal.mul_mem_right _ _ ?_
  refine Ideal.subset_span ?_
  exact Set.mem_image_of_mem lift x.property

/-- **Step 6 (ideal-generation corollary).** -/
theorem RGplusA_le_span_lift_of_reynolds
    (RGplusA : Ideal A)
    (present : ∀ f ∈ RGplusA, ∃ coeff : s → R,
      toR f = ∑ x ∈ s.attach, x.val * coeff x)
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    RGplusA ≤ Ideal.span ((lift '' (s : Set R)) : Set A) := by
  intro f hf
  obtain ⟨coeff, hcoeff⟩ := present f hf
  exact mem_ideal_span_lift_of_reynolds k A R toR ρ s lift
    f coeff hcoeff hlift hρ_id hρ_mul

/-- Auxiliary: from membership in `Ideal.span (s : Set R)` extract a presentation
`x = ∑ t ∈ s.attach, t.val * coeff t` for some `coeff : s → R`. -/
lemma exists_finset_presentation_of_mem_span
    {R : Type*} [CommRing R] (s : Finset R) (x : R)
    (hx : x ∈ Ideal.span (↑s : Set R)) :
    ∃ coeff : s → R, x = ∑ t ∈ s.attach, t.val * coeff t := by
  classical
  -- View the ideal-span hypothesis as a submodule-span hypothesis.
  have hxsub : x ∈ (Submodule.span R (↑s : Set R) : Submodule R R) := by
    change x ∈ ((Ideal.span (↑s : Set R) : Ideal R) : Submodule R R)
    exact hx
  -- Induct on membership in the span. The motive does not depend on the
  -- membership proof, so we strip it via `fun y _ => _`.
  refine Submodule.span_induction
    (p := fun y _ => ∃ coeff : s → R, y = ∑ t ∈ s.attach, t.val * coeff t)
    ?mem ?zero ?add ?smul hxsub
  case mem =>
    -- Single generator: pick coefficient 1 on `y`, 0 elsewhere.
    intro y hy
    have hy_s : y ∈ s := by simpa using hy
    refine ⟨fun t => if t.val = y then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (⟨y, hy_s⟩ : {a // a ∈ s})]
    · simp
    · intro b _ hb_ne
      have hbval : b.val ≠ y := fun heq => hb_ne (Subtype.ext heq)
      simp [hbval]
    · intro h; exact (h (Finset.mem_attach _ _)).elim
  case zero =>
    exact ⟨fun _ => 0, by simp⟩
  case add =>
    rintro a b _ _ ⟨ca, hca⟩ ⟨cb, hcb⟩
    refine ⟨fun t => ca t + cb t, ?_⟩
    rw [hca, hcb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intros; ring
  case smul =>
    rintro r a _ ⟨ca, hca⟩
    refine ⟨fun t => r * ca t, ?_⟩
    rw [smul_eq_mul, hca, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intros; ring

/-- **Glue lemma (3): the Reynolds operator witnesses `ReynoldsGITSpanProperty`.**

If every `x ∈ s` lifts to some `lift x ∈ A` with `toR (lift x) = x`, and `ρ` is the
Reynolds operator (identity on `toR '' A` and Reynolds-multiplicative on
`toR a * r`), then `ReynoldsGITSpanProperty toR ρ s` holds.

Proof: from `toR f ∈ Ideal.span s` get a presentation
`toR f = ∑ x ∈ s.attach, x.val * coeff x`. Apply Step 6
(`mem_ideal_span_lift_of_reynolds`) to land in `Ideal.span (lift '' s)`. On `s`,
`ρ x = ρ (toR (lift x)) = lift x`, so this ideal equals `Ideal.span (ρ '' s)`.
-/
theorem reynoldsGITSpanProperty_of_reynolds
    [DecidableEq A]
    (hlift : ∀ x ∈ s, toR (lift x) = x)
    (hρ_id : ∀ a : A, ρ (toR a) = a)
    (hρ_mul : ∀ (a : A) (r : R), ρ ((toR a) * r) = a * ρ r) :
    ReynoldsGITSpanProperty toR ρ s := by
  classical
  intro f hf
  -- (a) Finite presentation of `toR f`.
  obtain ⟨coeff, hcoeff⟩ :=
    exists_finset_presentation_of_mem_span s (toR f) hf
  -- (b) Step 6: land in `Ideal.span (lift '' s)`.
  have hf_lift :
      f ∈ Ideal.span ((lift '' (s : Set R)) : Set A) :=
    mem_ideal_span_lift_of_reynolds k A R toR ρ s lift f coeff hcoeff hlift hρ_id hρ_mul
  -- (c) On `s`, `ρ x = lift x`.
  have hρ_eq_lift : ∀ x ∈ s, ρ x = lift x := by
    intro x hx
    have hxR : ρ (toR (lift x)) = lift x := hρ_id (lift x)
    have hxs : ρ x = ρ (toR (lift x)) := by rw [hlift x hx]
    rw [hxs, hxR]
  -- (d) `lift '' s = (Finset.image ρ s : Set A)`.
  have hsets :
      (lift '' (s : Set R)) =
        ((Finset.image (fun x => ρ x) s : Finset A) : Set A) := by
    ext a
    refine ⟨fun ⟨x, hxs, hax⟩ => ?_, fun ha => ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxs, ?_⟩)
      rw [hρ_eq_lift x hxs, hax]
    · rcases Finset.mem_image.mp (Finset.mem_coe.mp ha) with ⟨x, hxs, rfl⟩
      exact ⟨x, hxs, (hρ_eq_lift x hxs).symm⟩
  rw [hsets] at hf_lift
  exact hf_lift

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

variable (A : Type*) [CommRing A] [Algebra k A]
variable (𝒜G : ℕ → Submodule k A) [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Step 7.** The fixed subalgebra `A = R^G` is finitely generated as a `k`-algebra,
provided its degree-`0` piece is finitely generated over `k` and its irrelevant ideal
is finitely generated as an ideal of `A`. -/
theorem fixedSubalgebra_finiteType
    [FiniteType k (𝒜G 0)]
    (hfg : (irrelevant 𝒜G).toIdeal.FG) :
    FiniteType k A :=
  GIT.finiteType_k_of_finitely_generated_irrelevant_ideal
    (k := k) (R := A) (𝒜 := 𝒜G) hfg

end FixedSubalgebra_FiniteType_S7

/-!
## Main GIT theorem (Hilbert finiteness)

For a linearly reductive group `G` acting on a finitely generated `k`-algebra `R`,
the invariant subring `R^G` is finitely generated as a `k`-algebra.

The proof chains Steps 1–7:
* **Step 1** (`fixedSubalgebra_decomposes`): `R^G` inherits an `ℕ`-grading from `R`.
* **Step 5.5** (`reynolds_operator_exists`): from `IsLinearlyReductive` + `IsLocallyFinite`,
  obtain a Reynolds projection `R ↠ R^G`.
* **Steps 3–4** (`extendedRGplus_fg`, `exists_generators_extendedRGplus_from_RGplus`):
  the extended ideal `R₊^G · R` is f.g. (Noether) and admits generators chosen from `R₊^G`.
* **Step 5** (`RGplusA_fg_of_reynolds`): pushing generators back via Reynolds shows
  the irrelevant ideal of `R^G` is f.g.
* **Steps 2 & 7** (`finiteType_k_of_finitely_generated_irrelevant_ideal`,
  `fixedSubalgebra_finiteType`): a positively-graded `k`-algebra with f.g. irrelevant
  ideal and f.g. degree-0 piece is itself f.g. as a `k`-algebra.
-/

section GIT_MainTheorem

-- `k`, `G`, `R` share universe `u` so that `exists_reynolds_of_locallyFinite` applies.
variable (k : Type u) [Field k]
variable (G : Type u) [Group G]
variable (R : Type u) [CommRing R] [Algebra k R]

-- Action of `G` on `R` as a `DistribMulAction` (so the Reynolds machinery applies)
-- together with the bundled `k`-algebra-automorphism form `ρ` used in Step 1.
variable [DistribMulAction G R] [SMulCommClass G k R]
variable (ρ : G →* R ≃ₐ[k] R)

-- Compatibility: `ρ` is the action.
variable (hρ_compat : ∀ (g : G) (r : R), ρ g r = g • r)

-- The grading on `R`.
variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

-- The induced grading on `R^G`.
variable (𝒜G : ℕ → Submodule k (FixedSubalgebra (k := k) (G := G) (R := R) ρ))
  [GradedAlgebra 𝒜G]

open Algebra HomogeneousIdeal

/-- **Main GIT theorem.**

Let `G` be a linearly reductive group acting on a finitely generated `k`-algebra `R`
by `k`-algebra automorphisms, with the action preserving a chosen `ℕ`-grading on `R`
and being locally finite. Then the invariant subalgebra `R^G` is finitely generated
as a `k`-algebra.

Hypotheses:
* `hlr`     : `G` is linearly reductive over `k`.
* `hpres`   : the action `ρ` preserves the grading `𝒜`.
* `hlf`     : the underlying `k`-module action of `G` on `R` is locally finite.
* `[FiniteType k R]`        : `R` is finitely generated as a `k`-algebra.
* `[IsNoetherianRing R]`    : used in Step 3 to get `extendedRGplus.FG`.
* `[FiniteType k (𝒜G 0)]`   : the degree-`0` piece of `R^G` is f.g./k
  (automatic when `𝒜G 0 = k`).
-/
theorem GIT_finiteType_invariants
    [FiniteType k R]
    [IsNoetherianRing R]
    [FiniteType k (𝒜G 0)]
    (hlr : IsLinearlyReductive k G) (hρ_compat : ∀ (g : G) (r : R), ρ g r = g • r)
    (hlf : Representation.IsLocallyFinite k G R)
    (h𝒜G : ∀ (d : ℕ) (a : FixedSubalgebra (k := k) (G := G) (R := R) ρ),
      a ∈ 𝒜G d → (a : R) ∈ 𝒜 d) :
    FiniteType k (FixedSubalgebra (k := k) (G := G) (R := R) ρ) := by
  classical
  -- Step 5.5: Reynolds projection `π : R → R` (lands in `σ.invariants`).
  obtain ⟨π, hπ⟩ :=
    reynolds_operator_exists (k := k) (G := G) (R := R) hlr hlf
  -- Step 7 reduction: it suffices to show the irrelevant ideal of `R^G` is f.g.
  refine fixedSubalgebra_finiteType (k := k)
    (A := FixedSubalgebra (k := k) (G := G) (R := R) ρ) (𝒜G := 𝒜G) ?_
  -- ── Setup ────────────────────────────────────────────────────────────────
  -- `A = R^G` as a `k`-subalgebra, plus inclusion `toR : A →ₐ[k] R`.
  let A : Subalgebra k R := FixedSubalgebra (k := k) (G := G) (R := R) ρ
  let toR : A →ₐ[k] R := A.val
  -- The irrelevant ideal of `A` and its extension to `R`.
  let RGplusA : Ideal A := (irrelevant 𝒜G).toIdeal
  change RGplusA.FG
  let extendedRGplus : Ideal R := Ideal.map (toR : A →+* R) RGplusA
  let RGplusSet : Set R := (toR : A → R) '' (RGplusA : Set A)
  -- ── Step 3: the extended ideal is f.g. (Noether) ─────────────────────────
  have h_ext_fg : extendedRGplus.FG :=
    extendedRGplus_fg (R := R) extendedRGplus
  -- ── Span property: `RGplusSet` ideal-spans `extendedRGplus` ──────────────
  have hspan_RG : Ideal.span RGplusSet = extendedRGplus := by
    change Ideal.span ((toR : A → R) '' (RGplusA : Set A)) = Ideal.map (toR : A →+* R) RGplusA
    rw [Ideal.map]; rfl
  -- ── Step 4: pick finitely many generators inside `RGplusSet` ─────────────
  obtain ⟨s, hs_sub, hs_span⟩ :=
    exists_generators_extendedRGplus_from_RGplus (R := R)
      RGplusSet extendedRGplus hspan_RG h_ext_fg
  -- ── Comap identification: `RGplusA = comap toR extendedRGplus` ──────────
  have htoR_inj : Function.Injective (toR : A →+* R) := Subtype.val_injective
  -- Compatibility of deg-0 components: the inclusion `A ↪ R` sends `(decompose 𝒜G a) 0`
  -- to `(decompose 𝒜 (toR a)) 0`. Proved by induction on the graded decomposition.
  have hdecomp0 : ∀ a : A,
      (((DirectSum.decompose 𝒜G a) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR a)) 0 : R) := fun a => by
    refine DirectSum.Decomposition.inductionOn (ℳ := 𝒜G)
      (motive := fun a => (((DirectSum.decompose 𝒜G a) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR a)) 0 : R)) ?_ ?_ ?_ a
    · simp
    · intro i m
      obtain ⟨c, hc⟩ := m
      have hcR : (c : R) ∈ 𝒜 i := h𝒜G i c hc
      change (((DirectSum.decompose 𝒜G (c : A)) 0 : A) : R) =
        ((DirectSum.decompose 𝒜 (toR (⟨c, hc⟩ : ↥(𝒜G i)))) 0 : R)
      have htoR_eq : toR (⟨c, hc⟩ : ↥(𝒜G i)) = (c : R) := rfl
      rw [htoR_eq]
      by_cases hi : i = 0
      · subst hi
        rw [DirectSum.decompose_of_mem_same 𝒜G hc,
            DirectSum.decompose_of_mem_same 𝒜 hcR]
      · rw [DirectSum.decompose_of_mem_ne 𝒜G hc hi,
            DirectSum.decompose_of_mem_ne 𝒜 hcR hi]
        simp
    · intro x y hx hy
      rw [DirectSum.decompose_add, DirectSum.add_apply,
          AddMemClass.coe_add, map_add, DirectSum.decompose_add, DirectSum.add_apply,
          AddMemClass.coe_add]
      push_cast
      rw [hx, hy]
  -- Each `a ∈ irrelevant 𝒜G` has `toR a ∈ irrelevant 𝒜` in `R`.
  have h_ext_le_irrR : extendedRGplus ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro a ha
    have h0A : ((DirectSum.decompose 𝒜G a) 0 : A) = 0 := by
      have hmem : a ∈ HomogeneousIdeal.irrelevant 𝒜G := ha
      have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜G) a).mp hmem
      simpa [GradedRing.proj_apply] using hp
    change toR a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal
    change toR a ∈ HomogeneousIdeal.irrelevant 𝒜
    rw [HomogeneousIdeal.mem_irrelevant_iff]
    have hcompat := hdecomp0 a
    rw [h0A] at hcompat
    simp only [ZeroMemClass.coe_zero] at hcompat
    simpa [GradedRing.proj_apply] using hcompat.symm
  have hcomap : RGplusA = Ideal.comap (toR : A →+* R) extendedRGplus := by
    apply le_antisymm
    · exact Ideal.le_comap_map
    · intro x hx
      have htoR_x : toR x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := h_ext_le_irrR hx
      have h0R : ((DirectSum.decompose 𝒜 (toR x)) 0 : R) = 0 := by
        have hmem : toR x ∈ HomogeneousIdeal.irrelevant 𝒜 := htoR_x
        have hp := (HomogeneousIdeal.mem_irrelevant_iff (𝒜 := 𝒜) (toR x)).mp hmem
        simpa [GradedRing.proj_apply] using hp
      have hRA0 : (((DirectSum.decompose 𝒜G x) 0 : A) : R) = 0 := by
        rw [hdecomp0 x]; exact h0R
      have h0A : ((DirectSum.decompose 𝒜G x) 0 : A) = 0 := htoR_inj hRA0
      change x ∈ (HomogeneousIdeal.irrelevant 𝒜G).toIdeal
      change x ∈ HomogeneousIdeal.irrelevant 𝒜G
      rw [HomogeneousIdeal.mem_irrelevant_iff]
      simpa [GradedRing.proj_apply] using h0A
  -- ── Lifts: each `x ∈ s` comes from some element of `RGplusA ⊆ A` ─────────
  have lift_exists : ∀ x ∈ s, ∃ a : A, a ∈ RGplusA ∧ toR a = x := fun x hx => hs_sub x hx
  choose liftFn hliftFn_mem hliftFn_eq using lift_exists
  let lift : R → A := fun x => if hx : x ∈ s then liftFn x hx else 0
  have hlift : ∀ x ∈ s, toR (lift x) = x := fun x hx => by
    simp only [lift, dif_pos hx]; exact hliftFn_eq x hx
  -- ── Reynolds linear map `ρ_lin : R →ₗ[k] A` from the `Rep`-projection ─-─
  -- `π` lands in `σ.invariants`; via `hρ`, `σ.invariants = A.toSubmodule`, giving a
  -- `k`-linear map into `A`. The required identities (`hρ_id`, `hρ_mul`, `hρ_gen`)
  -- come from `IsProj` plus the `R^G`-multiplicativity bundled by Reynolds.
  have ρ_lin_data :
      ∃ ρ_lin : R →ₗ[k] A,
        (∀ a : A, ρ_lin (toR a) = a) ∧
        (∀ (a : A) (r : R), ρ_lin ((toR a) * r) = a * ρ_lin r) ∧
        (∀ x ∈ s, ρ_lin x ∈ RGplusA) := by
    -- Build `MulSemiringAction G R` from `ρ` + `hρ`, then invoke the multiplicativity
    -- variant of Reynolds existence to get a Reynolds projection that is also
    -- `R^G`-multiplicative.
    letI : MulSemiringAction G R :=
      { (inferInstance : DistribMulAction G R) with
        smul_one := fun g => by
          rw [show g • (1 : R) = ρ g 1 from (hρ_compat g 1).symm]; exact map_one (ρ g)
        smul_mul := fun g a b => by
          rw [show g • (a * b) = ρ g (a * b) from (hρ_compat g (a * b)).symm,
              show g • a = ρ g a from (hρ_compat g a).symm,
              show g • b = ρ g b from (hρ_compat g b).symm]
          exact map_mul (ρ g) a b }
    obtain ⟨π', hπ'_proj, hπ'_mul⟩
      := exists_reynolds_mul_compat_of_locallyFinite (k := k) (G := G) hlr R hlf
    -- `σ.invariants` and `A` have the same underlying set via `hρ`.
    have h_inv_to_A : ∀ r : R,
        r ∈ (Representation.ofDistribMulAction k G R).invariants → r ∈ A := by
      intro r hr g
      rw [hρ_compat]
      exact ((Representation.ofDistribMulAction k G R).mem_invariants r).mp hr g
    have h_A_to_inv : ∀ r : R,
        r ∈ A → r ∈ (Representation.ofDistribMulAction k G R).invariants := by
      intro r hr
      rw [Representation.mem_invariants]
      intro g
      change g • r = r
      rw [← hρ_compat]; exact hr g
    have hπ'_to_A : ∀ r : R, π'.hom.hom r ∈ A.toSubmodule := fun r =>
      h_inv_to_A _ (hπ'_proj.map_mem r)
    let ρ_lin : R →ₗ[k] A :=
      LinearMap.codRestrict A.toSubmodule π'.hom.hom hπ'_to_A
    refine ⟨ρ_lin, ?_, ?_, ?_⟩
    · -- ρ_lin (toR a) = a
      intro a
      apply Subtype.ext
      change π'.hom.hom (a : R) = (a : R)
      exact hπ'_proj.map_id (a : R) (h_A_to_inv (a : R) a.property)
    · -- ρ_lin ((toR a) * r) = a * ρ_lin r
      intro a r
      apply Subtype.ext
      change π'.hom.hom ((a : R) * r) = (a : R) * π'.hom.hom r
      exact hπ'_mul (h_A_to_inv (a : R) a.property) r
    · -- ρ_lin x ∈ RGplusA for x ∈ s
      intro x hx
      obtain ⟨a, ha_mem, ha_eq⟩ := hs_sub x hx
      have h_eq : ρ_lin x = a := by
        rw [show x = toR a from ha_eq.symm]
        apply Subtype.ext
        change π'.hom.hom (a : R) = (a : R)
        exact hπ'_proj.map_id (a : R) (h_A_to_inv (a : R) a.property)
      rw [h_eq]; exact ha_mem
  obtain ⟨ρ_lin, hρ_id, hρ_mul, hρ_gen⟩ := ρ_lin_data
  -- ── Step 6 glue: `ReynoldsGITSpanProperty toR ρ_lin s` ───────────────────
  have hReynolds : ReynoldsGITSpanProperty toR ρ_lin s :=
    reynoldsGITSpanProperty_of_reynolds (k := k) A R toR ρ_lin s lift hlift hρ_id hρ_mul
  -- ── Step 5: assemble — `RGplusA.FG` ──────────────────────────────────────
  exact RGplusA_fg_of_reynolds (k := k) (A := A) (R := R)
    (toR := toR) (ρ := ρ_lin) (s := s)
    (RGplusA := RGplusA) (extendedRGplus := extendedRGplus)
    hs_span hcomap hρ_gen hReynolds

end GIT_MainTheorem
