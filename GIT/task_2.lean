/- Reynolds operator:
  MvPolynomial.IsInvariant and Algebra.invariantSubalgebra

Noetherian ring:  IsNoetherian R M

Noetherian ring has explicit generators t1...tn:
Submodule.fg_iff_exists_fin_generating_family

The existence of finite generators:

finitely generated ideal:
Ideal.FG

finitely generated submodule:
Submodule.FG
-/

import Mathlib

variable (k G R : Type*)
  [Field k] -- field
  [Group G]  -- group
  [CommRing R]  -- cummutative ring
  [Algebra k R] -- R is k-algebra
  [MulSemiringAction G R] -- group action
  [IsNoetherian R R] -- Noetherian ring

-- The invariant subring
-- R^G = { f ∈ R | g • f = f for all g ∈ G }
def R_G := (MulSemiringAction.invariantSubring G R)

-- R^G_+ : the irrelevant ideal (positive degree part)
def R_G_plus : Ideal R_G := sorry

-- Main theorem: R^G_+ is finitely generated
theorem R_G_plus_fg :
    (R_G_plus G R).FG := by
  -- Step 1: Since R is Noetherian, R^G_+·R is a finitely generated ideal of R
  have h1 : (R_G_plus G R • ⊤ : Submodule R_G R).FG := by
    sorry
  -- Step 2: Extract generators s={t1,...,tn} from h1
  obtain ⟨s, hs⟩ := h1
  -- Step 3: Reynolds operator argument
  have reynolds : ∀ f ∈ R_G_plus G R,
      f = ∑ i in s, (i : R_G) * sorry := by
    sorry
  -- Step 4: Conclude generators of R^G_+·R generate R^G_+
  exact sorry
