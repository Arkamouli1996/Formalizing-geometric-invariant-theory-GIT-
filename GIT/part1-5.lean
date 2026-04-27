import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps

open scoped DirectSum

universe u v w

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

variable (R : Type*) [CommRing R]
variable [IsNoetherianRing R]

/- Placeholder for the extended ideal `R₊^G R` inside `R`. -/
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


section RGplus_generators_S5

variable {k : Type u} [Field k]

variable {A : Type*} [CommRing A] [Algebra k A] [DecidableEq A]

variable {R : Type*} [CommRing R] [Algebra k R]

/-
`toR` is the inclusion `A → R`,
and `ρ` is the Reynolds operator `R → A`.

These imply `[Algebra A R]` and `[IsScalarTower k A R]`; we state them so that
`A →ₐ[k] R` and the ` comap` along `toR` elaborate as in the informal setup.
-/
variable [Algebra A R] [IsScalarTower k A R]
variable {toR : A →ₐ[k] R}
variable {ρ : R →ₗ[k] A}

/-
`RGplusA` is the ideal `R₊^G` in the fixed ring `A`,
and `extendedRGplus` is the ideal `R₊^G R` in `R`.
-/
variable {RGplusA : Ideal A}
variable {extendedRGplus : Ideal R}

/-
A finite set of generators chosen in Step 4.
-/
variable {s : Finset R}

/--
Step 5 spanning property (GIT Reynolds step).

If `toR f` lies in the `R`-ideal generated by `s`, then `f` lies in the `A`-ideal
generated by the Reynolds images `ρ(x)` for `x ∈ s`.

This implication is the genuine algebraic content of Step 5: one cannot derive it from
`ρ (toR a) = a` and `ρ ((toR a) * r) = a * ρ r` alone, because `toR f ∈ Ideal.span s`
only pins down an **R**-linear combination of `s`, and commuting `ρ` past arbitrary
`R`-coefficients needs the further Reynolds/graded input from your concrete setup.
Supply this when you instantiate `ρ` from averaging or a projector.
-/
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
