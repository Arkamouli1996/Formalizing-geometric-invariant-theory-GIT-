import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Zorn
import Mathlib.Algebra.Module.Submodule.Lattice

variable (k : Type*) [Field k]
variable (G : Type*) [Group G]
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

-- ================================================================
-- DEFINITIONS
-- ================================================================

/-- G-stability of a submodule W.
    In the proof, we need subspaces W ⊆ V that are "G-stable", meaning
    ρ(g)(W) ⊆ W for all g ∈ G. -/
def IsGStable (ρ : Representation k G V) (W : Submodule k V) : Prop :=
  ∀ g : G, W ≤ Submodule.comap (ρ g) W

/-- Rationality of the G-action on V.
    Bertram's notes require the action to be "rational",
    meaning every single vector v ∈ V already lives inside some
    finite-dimensional G-stable subspace W ⊆ V. -/
def IsRational (ρ : Representation k G V) : Prop :=
  ∀ v : V, ∃ W : Submodule k V,
    v ∈ W ∧ Module.Finite k W ∧ IsGStable k G V ρ W

/-- Linear reductivity of G.
    given any finite-dimensional G-stable subspace W ⊆ V, we can split
    W = W^G ⊕ W' for some G-stable complement W'.-/
class LinearlyReductive (k G : Type*) [Field k] [Group G] where
  split_invariants :
    ∀ (V : Type*) [AddCommGroup V] [Module k V]
      (ρ : Representation k G V),
      ∃ W' : Submodule k V,
        IsCompl ρ.invariants W' ∧ IsGStable k G V ρ W'

-- ================================================================
-- PART 1a: CONSTRUCTING V_G VIA ZORN'S LEMMA
-- ================================================================
-- The proof constructs a "complement" V_G to V^G by:
--   (1) defining a poset S of candidate complements
--   (2) showing every chain in S has an upper bound in S
--   (3) applying Zorn's lemma to get a maximal element V_G ∈ S
--   (4) showing this maximal V_G actually satisfies V = V^G ⊕ V_G

/-- The poset S from the proof of Lemma 1.1.
    We define S = { T ⊆ V | T is G-stable and T ∩ V^G = 0 }.
    These are the "candidate complements" to V^G: they are G-stable
    (so that we stay in the world of G-representations) and disjoint
    from V^G (so that V^G + T is a direct sum, not just a sum).
    S is ordered by inclusion. We want a maximal element — that will
    be our V_G. -/
def GStableDisjoint (ρ : Representation k G V) : Set (Submodule k V) :=
  { T | IsGStable k G V ρ T ∧ T ⊓ ρ.invariants = ⊥ }

/-- Step 1 of the Zorn argument: S is nonempty.
    The zero subspace {0} is always in S:
    - It is G-stable because ρ(g)(0) = 0 for all g (linearity of ρ g).
    - It is disjoint from V^G because {0} ∩ V^G = {0} = ⊥.
    This is needed by Zorn's lemma, which requires the poset to be nonempty. -/
lemma bot_mem_GStableDisjoint :
    (⊥ : Submodule k V) ∈ GStableDisjoint k G V ρ :=
  -- G-stability: bot_le gives ⊥ ≤ comap (ρ g) ⊥ for any g
  -- Disjointness: bot_inf_eq gives ⊥ ⊓ ρ.invariants = ⊥
  ⟨fun g => bot_le, bot_inf_eq⟩

/-- Step 2a: the union of a chain in S is G-stable, hence in S.
    In the proof, we need to show every chain c ⊆ S has an upper bound
    in S. We use sSup c (the union of the chain) as that upper bound.
    Here we verify G-stability of sSup c:
    If v ∈ sSup c, then by definition of sSup for submodules,
    v lives in some T ∈ c. Since T ∈ S, T is G-stable, so ρ(g)(v) ∈ T.
    Since T ⊆ sSup c, we get ρ(g)(v) ∈ sSup c. -/
lemma sSup_chain_isGStable
    (c : Set (Submodule k V))
    (hc_sub : c ⊆ GStableDisjoint k G V ρ) :
    IsGStable k G V ρ (sSup c) := by
  sorry

/-- Step 2b: the union of a chain in S is disjoint from V^G, hence in S.
    We verify the second condition for sSup c to be in S:
    Suppose x ∈ sSup c ∩ V^G. Then x ∈ T for some T ∈ c, and x ∈ V^G.
    But T ∈ S means T ∩ V^G = 0, so x = 0.
    Therefore sSup c ∩ V^G = 0. -/
lemma sSup_chain_disjoint
    (c : Set (Submodule k V))
    (hc_sub : c ⊆ GStableDisjoint k G V ρ) :
    sSup c ⊓ ρ.invariants = ⊥ := by
  sorry

/-- Step 3: Zorn's lemma gives a maximal element V_G ∈ S.
    We have shown:
    - S is nonempty (bot_mem_GStableDisjoint)
    - every chain in S has sSup as an upper bound in S (Steps 2a, 2b)-/
lemma exists_maximal_GStableDisjoint :
    ∃ VG ∈ GStableDisjoint k G V ρ,
      ∀ T ∈ GStableDisjoint k G V ρ, VG ≤ T → T = VG := by
  apply zorn_le₀
  intro c hc_sub hc_chain
  obtain rfl | ⟨T, hT⟩ := c.eq_empty_or_nonempty
  · -- empty chain: ⊥ is a trivial upper bound
    exact ⟨⊥, bot_mem_GStableDisjoint k G V ρ, by simp⟩
  · -- nonempty chain: sSup c is the upper bound, which lies in S by Steps 2a+2b
    -- le_sSup (Mathlib): every T ∈ c satisfies T ≤ sSup c
    exact ⟨sSup c,
      ⟨sSup_chain_isGStable k G V ρ c hc_sub,
       sSup_chain_disjoint k G V ρ c hc_sub⟩,
      fun W hW => le_sSup hW⟩

-- ================================================================
-- PART 1b: THE MAXIMAL V_G IS A TRUE COMPLEMENT — V = V^G ⊕ V_G
-- ================================================================
-- Zorn gave us a maximal V_G ∈ S. We now need to show V = V^G ⊕ V_G,
-- i.e. that V^G and V_G together span all of V.
-- This splits into two sub-goals matching the definition of IsCompl:
--   (disjoint)    V^G ∩ V_G = 0         ← easy, already in the definition of S
--   (codisjoint)  V^G + V_G = V         ← hard, this is where we use
--                                           rationality + linear reductivity

/-- Disjoint half of IsCompl: V^G ∩ V_G = 0.
    This is immediate: V_G ∈ S means by definition that V_G ∩ V^G = 0.
    We just need to repackage this as Lean's Disjoint predicate. -/
lemma maximal_disjoint
    (VG : Submodule k V)
    (hVG : VG ∈ GStableDisjoint k G V ρ) :
    Disjoint ρ.invariants VG := by
  -- hVG.2 : VG ⊓ ρ.invariants = ⊥
  -- Disjoint p q in a lattice means p ⊓ q ≤ ⊥
  -- We swap order with disjoint_comm since hVG gives VG ⊓ V^G = ⊥
  rw [disjoint_comm]
  exact Submodule.disjoint_def.mpr (fun x hx hinv => by
    have : x ∈ VG ⊓ ρ.invariants := ⟨hx, hinv⟩
    rw [hVG.2] at this
    exact Submodule.mem_bot.mp this)

/-- Codisjoint half of IsCompl: V^G + V_G = V.
    Suppose for contradiction that V^G ⊔ V_G ≠ ⊤, i.e. there exists
    some v ∈ V with v ∉ V^G + V_G.

    Step A (rationality): Since the action is rational, v lives in some
    finite-dimensional G-stable subspace W ⊆ V.

    Step B (intersect with current span): Consider
       W₀ = W ∩ (V^G ⊔ V_G)
    This is G-stable (intersection of two G-stable spaces) and finite-dimensional.
    Since v ∈ W but v ∉ V^G + V_G, we know W₀ ≠ W, i.e. W₀ is a proper subspace of W.

    Step C (linear reductivity): Apply LinearlyReductive to the restricted
    representation on W. This gives a G-stable complement W'' to W₀ inside W:
       W = W₀ ⊕ W''
    Since W₀ ≠ W, we have W'' ≠ 0.

    Step D (W'' extends V_G in S): We claim V_G + W'' ∈ S, i.e.:
    - G-stable: V_G and W'' are both G-stable, so their sum is G-stable.
    - Disjoint from V^G: if x ∈ (V_G + W'') ∩ V^G, write x = y + z
      with y ∈ V_G, z ∈ W''. Then z = x - y ∈ (V^G + V_G) ∩ W'' = W₀ ∩ W'' = 0,
      so z = 0, then x = y ∈ V_G ∩ V^G = 0.

    Step E (contradiction): V_G ⊊ V_G + W'' and both are in S,
    contradicting the maximality of V_G. -/
lemma maximal_codisjoint
    [LinearlyReductive k G]
    (hrat : IsRational k G V ρ)
    (VG : Submodule k V)
    (hVG : VG ∈ GStableDisjoint k G V ρ)
    (hmax : ∀ T ∈ GStableDisjoint k G V ρ, VG ≤ T → T = VG) :
    Codisjoint ρ.invariants VG := by
  sorry

lemma maximal_isCompl
    [LinearlyReductive k G]
    (hrat : IsRational k G V ρ)
    (VG : Submodule k V)
    (hVG : VG ∈ GStableDisjoint k G V ρ)
    (hmax : ∀ T ∈ GStableDisjoint k G V ρ, VG ≤ T → T = VG) :
    IsCompl ρ.invariants VG :=
  ⟨maximal_disjoint k G V ρ VG hVG,
   maximal_codisjoint k G V ρ hrat VG hVG hmax⟩

-- ================================================================
-- Results from Lemma 1.1
-- ================================================================

/-- Main result of Part 1 of Lemma 1.1:
    If G is linearly reductive and acts rationally on V, then there
    exists a G-stable subspace V_G ⊆ V such that V = V^G ⊕ V_G.
    This is what Bertram calls "V splits as V^G ⊕ W'". -/
theorem exists_isCompl_invariants
    [LinearlyReductive k G]
    (hrat : IsRational k G V ρ) :
    ∃ VG : Submodule k V,
      IsCompl ρ.invariants VG ∧ IsGStable k G V ρ VG := by
  obtain ⟨VG, hVG_mem, hVG_max⟩ := exists_maximal_GStableDisjoint k G V ρ
  exact ⟨VG,
    maximal_isCompl k G V ρ hrat VG hVG_mem hVG_max,
    hVG_mem.1⟩

-- ================================================================
-- PART 2: THE REYNOLDS OPERATOR E — EXISTENCE AND UNIQUENESS
-- ================================================================
-- Given the splitting V = V^G ⊕ V_G from Part 1, Lemma 1.1 says
-- there is a UNIQUELY DEFINED linear operator E : V → V that
-- projects V onto V^G. We construct it as E = ι ∘ π where:
--   π : V → V^G  is the projection along V_G  (from the splitting)
--   ι : V^G → V  is the inclusion
-- Uniqueness follows because V_G = ker(E) is forced: any G-equivariant
-- projection onto V^G must have a G-stable kernel disjoint from V^G,
-- and the maximal such kernel is V_G.

/-- Existence of E: construct the Reynolds operator as ι ∘ π.
    Given the splitting V = V^G ⊕ V_G, we get for free from Mathlib:
    - linearProjOfIsCompl : V →ₗ[k] V^G   (the projection π)
    - subtype              : V^G →ₗ[k] V   (the inclusion ι)
    Their composition E = ι ∘ π is the Reynolds operator. -/
noncomputable def reynoldsOperator
    [LinearlyReductive k G]
    (hrat : IsRational k G V ρ) : V →ₗ[k] V :=
  let ⟨VG, hcompl, _⟩ := exists_isCompl_invariants k G V ρ hrat
  -- ι ∘ π: first project onto V^G, then include back into V
  ρ.invariants.subtype ∘ₗ ρ.invariants.linearProjOfIsCompl VG hcompl

/-- E(v) ∈ V^G for all v ∈ V.
    This holds because π(v) ∈ V^G by construction (it's the projection
    onto V^G), and ι just includes V^G into V without leaving V^G.
    In Lean: image of linearProjOfIsCompl lands in ρ.invariants,
    and subtype.coe_mem confirms the coercion stays in the submodule. -/
theorem reynolds_mem_invariants
    [LinearlyReductive k G] (hrat : IsRational k G V ρ) (v : V) :
    reynoldsOperator k G V ρ hrat v ∈ ρ.invariants := by
  simp [reynoldsOperator, Submodule.coe_mem]

/-- E(v) = v for all v ∈ V^G (E is the identity on invariants).
    In the splitting V = V^G ⊕ V_G, any v ∈ V^G has V_G-component zero,
    so the projection π sends v to itself: π(v) = v.
    Then E(v) = ι(π(v)) = ι(v) = v.
    Mathlib: Submodule.linearProjOfIsCompl_apply_left says exactly this —
    if v ∈ p then linearProjOfIsCompl q h v = ⟨v, hv⟩. -/
theorem reynolds_id_on_invariants
    [LinearlyReductive k G] (hrat : IsRational k G V ρ)
    (v : V) (hv : v ∈ ρ.invariants) :
    reynoldsOperator k G V ρ hrat v = v := by
  sorry

/-- Uniqueness of E.
    Bertram says E is "uniquely defined". Here is why:
    Suppose E and E' are both linear projections onto V^G, equivariant
    for the G-action. For any v ∈ V, write v = v⁺ + v⁻ with
    v⁺ = E(v) ∈ V^G and v⁻ = v - E(v) ∈ V_G (= ker E).
    Then:
      E(v)  = E(v⁺) + E(v⁻) = v⁺ + 0 = v⁺
      E'(v) = E'(v⁺) + E'(v⁻) = v⁺ + 0 = v⁺
    where E'(v⁻) = 0 because v⁻ ∈ V_G, E'(v⁻) ∈ V^G, and V^G ∩ V_G = 0.
    So E = E'. -/
theorem reynolds_unique
    [LinearlyReductive k G] (hrat : IsRational k G V ρ)
    (E E' : V →ₗ[k] V)
    (hE_inv  : ∀ v, E v ∈ ρ.invariants)
    (hE_id   : ∀ v, v ∈ ρ.invariants → E v = v)
    (hE'_inv : ∀ v, E' v ∈ ρ.invariants)
    (hE'_id  : ∀ v, v ∈ ρ.invariants → E' v = v) :
    E = E' := by
  sorry

-- ================================================================
-- PART 3: NATURALITY OF E — E COMMUTES WITH G-LINEAR MAPS
-- ================================================================
-- The second statement of Lemma 1.1: if u : V → V' is G-linear
-- (i.e. u ∘ ρ(g) = ρ'(g) ∘ u for all g), then E' ∘ u = u ∘ E,
-- where E, E' are the Reynolds operators for V, V' respectively.
-- Proof: it suffices to check on V^G and V_G separately.
--   On V^G: u sends V^G into (V')^G (Step A below),
--           so E'(u(v)) = u(v) = u(E(v)) for v ∈ V^G.
--   On V_G: u sends V_G into (V')_G (Step B below),
--           so E'(u(v)) = 0 = u(0) = u(E(v)) for v ∈ V_G.

/-- Step A: G-linear maps send V^G into (V')^G.
    If v ∈ V^G (i.e. ρ(g)(v) = v for all g) and u is G-linear, then
    ρ'(g)(u(v)) = u(ρ(g)(v)) = u(v) for all g, so u(v) ∈ (V')^G.
    This goes through immediately from Representation.mem_invariants. -/
lemma glinear_maps_invariants
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V')
    (u : V →ₗ[k] V')
    (hu : ∀ g v, u (ρ g v) = ρ' g (u v))  -- u is G-linear
    (v : V) (hv : v ∈ ρ.invariants) :
    u v ∈ ρ'.invariants := by
  rw [Representation.mem_invariants]
  intro g
  -- ρ'(g)(u(v)) = u(ρ(g)(v))   by G-linearity of u
  -- u(ρ(g)(v))  = u(v)          because v ∈ V^G
  rw [← hu, (Representation.mem_invariants ρ v).mp hv]

/-- Step B: G-linear maps send V_G into (V')_G.
    This is harder. If v ∈ V_G (i.e. v is in the complement of V^G),
    we need u(v) ∈ (V')_G (the complement of (V')^G).
    Proof: V_G has no nonzero invariant vectors (since V_G ∩ V^G = 0),
    so any finite-dim G-stable W ⊆ V_G also has W^G = 0.
    The image u(W) is G-stable, and by G-linearity, (u(W))^G maps back
    to W^G = 0, so u(W) ∩ (V')^G = 0, meaning u(v) ∈ (V')_G. -/
lemma glinear_maps_complement
    [LinearlyReductive k G]
    (hrat  : IsRational k G V ρ)
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V')
    (hrat' : IsRational k G V' ρ')
    (u : V →ₗ[k] V')
    (hu : ∀ g v, u (ρ g v) = ρ' g (u v))
    (VG  : Submodule k V)  (hVG  : IsCompl ρ.invariants VG)
    (VG' : Submodule k V') (hVG' : IsCompl ρ'.invariants VG') :
    ∀ v ∈ VG, u v ∈ VG' := by
  sorry

/-- Naturality: E' ∘ u = u ∘ E.
    For any v = v⁺ + v⁻ ∈ V^G ⊕ V_G:
      (E' ∘ u)(v) = E'(u(v⁺) + u(v⁻))
                  = E'(u(v⁺)) + E'(u(v⁻))
                  = u(v⁺) + 0              (by Steps A and B)
                  = u(v⁺)
                  = u(E(v))
                  = (u ∘ E)(v)
    So the two sides agree on all of V = V^G ⊕ V_G. -/
theorem reynolds_natural
    [LinearlyReductive k G]
    (hrat  : IsRational k G V ρ)
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ' : Representation k G V')
    (hrat' : IsRational k G V' ρ')
    (u : V →ₗ[k] V')
    (hu : ∀ g v, u (ρ g v) = ρ' g (u v)) :
    reynoldsOperator k G V' ρ' hrat' ∘ₗ u =
    u ∘ₗ reynoldsOperator k G V ρ hrat := by
  sorry
