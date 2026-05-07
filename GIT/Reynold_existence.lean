import Mathlib

open Submodule

universe u

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {R : Type u} [AddCommGroup R] [Module k R] [Module G R]

--------------------------------------------------------------------------------
-- 1. Reynolds Operator Typeclass
--------------------------------------------------------------------------------

/--
A Reynolds operator is a projection onto invariants
that is linear and G-equivariant.
-/
class ReynoldsOperator (k G R : Type u)
  [Field k] [Group G]
  [AddCommGroup R] [Module k R] [Module G R] where

  ρ : R →ₗ[k] R

  mem_invariants :
    ∀ x : R, ρ x ∈ (Submodule.fixedPoints G R)

  fixed :
    ∀ x : R, x ∈ (Submodule.fixedPoints G R) → ρ x = x

  equivariant :
    ∀ (g : G) (x : R),
      ρ (g • x) = g • (ρ x)

--------------------------------------------------------------------------------
-- 2. Finite-dimensional Reynolds operator (Lemma 1.1)
--------------------------------------------------------------------------------

class LinearlyReductive (k G : Type u)
  [Field k] [Group G] : Prop where
  exists_projection :
    ∀ (V : Type u)
      [AddCommGroup V] [Module k V] [Module G V]
      [FiniteDimensional k V],
      ∃ p : V →ₗ[k] V,
        (∀ v, p v ∈ Submodule.fixedPoints G V) ∧
        (∀ v ∈ Submodule.fixedPoints G V, p v = v) ∧
        (∀ g v, p (g • v) = g • p v)

noncomputable def reynolds_finite
  (k G V : Type u)
  [Field k] [Group G]
  [AddCommGroup V] [Module k V] [Module G V]
  [FiniteDimensional k V]
  [LinearlyReductive k G] :
  V →ₗ[k] V :=
by
  classical
  have h := LinearlyReductive.exists_projection (k := k) (G := G) V
  choose p hp using h
  exact p

--------------------------------------------------------------------------------
-- 3. Locally finite action hypothesis
--------------------------------------------------------------------------------

class LocallyFinite (G R : Type u)
  [Group G] [AddCommGroup R] [Module k R] [Module G R] : Prop where
  exists_finite_submodule :
    ∀ r : R,
      ∃ V : Submodule k R,
        r ∈ V ∧
        FiniteDimensional k V ∧
        IsStableUnderAction G V

--------------------------------------------------------------------------------
-- 4. Choose finite submodule containing r
--------------------------------------------------------------------------------

noncomputable def V_of
  (r : R)
  [LocallyFinite G R] :
  { V : Submodule k R //
      r ∈ V ∧
      FiniteDimensional k V ∧
      IsStableUnderAction G V } :=
by
  classical
  exact Classical.choose (LocallyFinite.exists_finite_submodule r)

--------------------------------------------------------------------------------
-- 5. Local Reynolds operator on R
--------------------------------------------------------------------------------

noncomputable def rho_local
  (r : R)
  [LinearlyReductive k G]
  [LocallyFinite G R] : R :=
by
  classical
  let V := (V_of r).val
  let hv := (V_of r).property.1
  exact (reynolds_finite k G V) ⟨r, hv⟩

--------------------------------------------------------------------------------
-- 6. Key structural lemma (well-definedness principle)
--------------------------------------------------------------------------------

/--
Uniqueness principle for equivariant projections:
any two Reynolds projections agree on overlaps.
(This replaces your incorrect intersection argument.)
-/
lemma reynolds_unique
  {V W : Submodule k R}
  [FiniteDimensional k V] [FiniteDimensional k W]
  [IsStableUnderAction G V] [IsStableUnderAction G W]
  (pV : V →ₗ[k] V) (pW : W →ₗ[k] W)
  (hV : ∀ v ∈ Submodule.fixedPoints G V, pV v = v)
  (hW : ∀ w ∈ Submodule.fixedPoints G W, pW w = w)
  (hVeq : ∀ g v, pV (g • v) = g • pV v)
  (hWeq : ∀ g w, pW (g • w) = g • pW w) :
  ∀ x ∈ V ⊓ W,
    (pV ⟨x, by simpa using ‹x ∈ V ⊓ W›⟩ : R) =
    (pW ⟨x, by simpa using ‹x ∈ V ⊓ W›⟩ : R) :=
by
  classical
  intro x hx
  -- conceptual proof:
  -- both are projections onto same invariant subspace
  -- uniqueness from semisimplicity
  sorry

--------------------------------------------------------------------------------
-- 7. Global Reynolds operator
--------------------------------------------------------------------------------

noncomputable def Reynolds
  (k G R : Type u)
  [Field k] [Group G]
  [AddCommGroup R] [Module k R] [Module G R]
  [LinearlyReductive k G]
  [LocallyFinite G R] : R →ₗ[k] R :=
{
  toFun := fun r => rho_local r

  map_add' := by
    intro x y
    classical
    -- both lie in a common finite-dimensional stable submodule
    -- use uniqueness lemma to compare
    sorry

  map_smul' := by
    intro a x
    classical
    sorry
}

--------------------------------------------------------------------------------
-- 8. ReynoldsOperator instance (final packaging)
--------------------------------------------------------------------------------

noncomputable instance ReynoldsOperator.of_local_finite
  [LinearlyReductive k G]
  [LocallyFinite G R] :
  ReynoldsOperator k G R :=
{
  ρ := Reynolds k G R

  mem_invariants := by
    intro x
    classical
    -- follows from finite-dimensional projection property
    sorry

  fixed := by
    intro x hx
    classical
    -- restriction to finite V containing x
    sorry

  equivariant := by
    intro g x
    classical
    -- follows from local equivariance + uniqueness lemma
    sorry
}
