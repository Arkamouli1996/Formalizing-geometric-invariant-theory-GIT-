import Mathlib.CategoryTheory.Action.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine

universe u

variable (G : Type*) [Group G]

open AlgebraicGeometry CategoryTheory

/-- **Definition 8.1.1 (Good Quotient).**
    A good quotient of a G-scheme `X` bundles the target scheme `Y`,
    the G-invariant morphism `π : X → Y`, and the two axioms. -/
structure GoodQuotient (X : Action Scheme G) where
  /-- The target scheme (the quotient). -/
  Y : Scheme
  /-- The quotient map. G-invariance is automatic from the typing:
      `π` is a morphism in `Action Scheme G` to the trivially-acted `Y`. -/
  π : X ⟶ Action.trivial G Y
  /-- (1) `π` is affine. -/
  isAffine : IsAffineHom π.hom
  /-- (2) `𝒪_Y → (π_* 𝒪_X)^G` is an isomorphism.
      Concretely: for every open `U ⊆ Y`, the pullback
      `π* : Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_X)^G` is an isomorphism.
      Locally this is the statement that `π` looks like `Spec A → Spec A^G`. -/
  invariantSections : sorry


/-Helper method: -/
/-- A subset `W ⊆ X` is G-invariant if it is stable under every `g : G`. -/
def IsGInvariantSubset {X : Action Scheme G} (W : Set X.V) : Prop :=
  ∀ (g : G), (X.ρ g).val.base '' W ⊆ W

variable {G} {X : Action Scheme G} (q : GoodQuotient G X)

/-- **Proposition 8.1.3(1a).** A good quotient is surjective.

by link
-/
theorem GoodQuotient.surjective : Function.Surjective q.π.hom.base := by
  sorry

/-- **Proposition 8.1.3(1b).** The image of a closed G-invariant subset is closed. -/
theorem GoodQuotient.image_isClosed
    {W : Set X.V} (hW : IsClosed W) (hWG : IsGInvariantSubset G W) :
    IsClosed (q.π.hom.base '' W) := by
  sorry

/-- **Proposition 8.1.3(2).** For closed G-invariant subsets `Z₁ Z₂ ⊆ X`,
    `im(Z₁ ∩ Z₂) = im(Z₁) ∩ im(Z₂)`.
    Equivalently: `π(x₁) = π(x₂)` if and only if `G·x₁ ∩ G·x₂ ≠ ∅`. -/
theorem GoodQuotient.image_inter
    {Z₁ Z₂ : Set X.V}
    (hZ₁ : IsClosed Z₁) (hZ₁G : IsGInvariantSubset G Z₁)
    (hZ₂ : IsClosed Z₂) (hZ₂G : IsGInvariantSubset G Z₂) :
    q.π.hom.base '' (Z₁ ∩ Z₂) = q.π.hom.base '' Z₁ ∩ q.π.hom.base '' Z₂ := by
  sorry
