import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection

variable (k : Type*) [Field k]
variable (G : Type*) [Group G]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- Invariants submodule V^G -/
noncomputable def invariants : Submodule k V := ρ.invariants

/-
STEP 1: Use linear reductivity to obtain a decomposition
        V = V^G ⊕ W'
-/
/-- Linearly reductive means: every representation splits as V = V^G ⊕ W' -/
class LinearlyReductive (k G : Type*) [Field k] [Group G] where
  split_invariants :
    ∀ (V : Type*) [AddCommGroup V] [Module k V]
      (ρ : Representation k G V),
      ∃ W' : Submodule k V, IsCompl ρ.invariants W'

/-- Extract complement given linear reductivity -/
noncomputable def getComplement
    [LinearlyReductive k G] (ρ : Representation k G V) :
    { W' : Submodule k V // IsCompl ρ.invariants W' } :=
  ⟨_, (LinearlyReductive.split_invariants V ρ).choose_spec⟩

/-
STEP 2: Define projection and inclusion:
        π : V → V^G  (projection along W')
        ι : V^G → V   (inclusion map)
        R_V := ι ∘ π
-/
noncomputable def reynoldsOperator
    [LinearlyReductive k G] (ρ : Representation k G V) : V →ₗ[k] V :=
by
  classical
  let C := getComplement k G V ρ
  let π : V →ₗ[k] ρ.invariants :=
    ρ.invariants.linearProjOfIsCompl C.1 C.2
  let ι : ρ.invariants →ₗ[k] V :=
    ρ.invariants.subtype
  exact ι ∘ₗ π

/-
STEP 3: R_V(v) lies in V^G

Reason:
π(v) ∈ V^G by construction, and ι includes V^G into V.
-/
theorem reynoldsOperator_mem_invariants
    [LinearlyReductive k G] (ρ : Representation k G V) (v : V) :
    reynoldsOperator k G V ρ v ∈ ρ.invariants := by
  classical
  unfold reynoldsOperator
  simp only [LinearMap.comp_apply]
  exact Submodule.coe_mem _

/-
STEP 4: R_V is identity on invariants

If v ∈ V^G, then in the decomposition V = V^G ⊕ W',
v has no W' component, so projection returns v.
-/
theorem reynoldsOperator_id_on_invariants
    [LinearlyReductive k G] (ρ : Representation k G V)
    (v : V) (hv : v ∈ ρ.invariants) :
    reynoldsOperator k G V ρ v = v := by
  classical
  unfold reynoldsOperator
  simp only [LinearMap.comp_apply]
  let C := getComplement k G V ρ
  have hproj :
      ρ.invariants.linearProjOfIsCompl C.1 C.2 v = ⟨v, hv⟩ :=
    Submodule.linearProjOfIsCompl_apply_left C.2 ⟨v, hv⟩
  simpa using congrArg ρ.invariants.subtype hproj

/-!
FINAL RESULT:

We package the construction:
R_V = ι ∘ π satisfies:
  (a) lands in invariants
  (b) fixes invariants
-/
structure ReynoldsOperator [LinearlyReductive k G]
    (ρ : Representation k G V) where
  toLinearMap : V →ₗ[k] V
  mem_invariants : ∀ v, toLinearMap v ∈ ρ.invariants
  id_on_invariants : ∀ v, v ∈ ρ.invariants → toLinearMap v = v

noncomputable def reynoldsOperatorExists
    [LinearlyReductive k G] (ρ : Representation k G V) :
    ReynoldsOperator k G V ρ :=
by
  classical
  refine
  { toLinearMap := reynoldsOperator k G V ρ
    mem_invariants := reynoldsOperator_mem_invariants k G V ρ
    id_on_invariants := reynoldsOperator_id_on_invariants k G V ρ }

/- Show uniqueness of Reynolds operators -/
theorem reynoldsOperator_unique
    [LinearlyReductive k G] (ρ : Representation k G V)
    (R1 R2 : ReynoldsOperator k G V ρ)
    (h_ker : R1.toLinearMap.ker = R2.toLinearMap.ker) :
    R1.toLinearMap = R2.toLinearMap := by
  ext v
  /- Use the fact that V = ker(R1) + im(R1) because R1 is a projection -/
  have h_proj (R : ReynoldsOperator k G V ρ) (x : V) :
      R.toLinearMap (R.toLinearMap x) = R.toLinearMap x := by
    apply R.id_on_invariants
    apply R.mem_invariants

  /- Every v can be written as (v - Rv) + Rv, where (v - Rv) ∈ ker R -/
  let v_inv := R1.toLinearMap v
  let v_ker := v - v_inv

  have hv : v = v_ker + v_inv := by rw [sub_add_cancel]

  have m_ker : v_ker ∈ R1.toLinearMap.ker := by
    rw [LinearMap.mem_ker, LinearMap.map_sub, h_proj R1 v, sub_self]

  /- Now evaluate R1 and R2 on the decomposition -/
  calc R1.toLinearMap v
    _ = R1.toLinearMap v_ker + R1.toLinearMap v_inv := by rw [hv, LinearMap.map_add]
    _ = 0 + v_inv := by
        rw [LinearMap.mem_ker.mp m_ker, R1.id_on_invariants v_inv (R1.mem_invariants v)]
    _ = R2.toLinearMap v_ker + R2.toLinearMap v_inv := by
        rw [h_ker] at m_ker
        rw [LinearMap.mem_ker.mp m_ker, R2.id_on_invariants v_inv (R1.mem_invariants v), zero_add]
    _ = R2.toLinearMap (v_ker + v_inv) := by rw [LinearMap.map_add]
    _ = R2.toLinearMap v := by rw [hv]
