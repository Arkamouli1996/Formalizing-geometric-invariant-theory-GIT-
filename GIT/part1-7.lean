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

    choose degT hdegTpos hdegTmem using (fun t : (T : Set R) => (hT t.1 (by simpa using t.2)))

    let πd : R →+ R :=
      { toFun := fun z => ((DirectSum.decompose 𝒜 z) d : R)
        map_zero' := by simp
        map_add' := by simp }

    have hπy : πd y = y := by
      simpa [πd] using (DirectSum.decompose_of_mem_same 𝒜 (x := y) (i := d) hy)

    have hl_sum :
        (Finsupp.linearCombination R (fun t : (T : Set R) => (t : R)) l) =
          Finset.sum l.support (fun t => l t * (t : R)) := by
      classical
      simp [Finsupp.linearCombination_apply, smul_eq_mul, Finsupp.sum]

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
        simpa using (Subsemiring.zero_mem (Algebra.adjoin (𝒜 0) (T : Set R)).toSubsemiring)

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

variable [Algebra A R] [IsScalarTower k A R]
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

/-- Step 5 (membership form). -/
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

/-- Step 5 (finite generation of `RGplusA`). -/
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

end ReynoldsRewrite_S6

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
