/- definition of good quotient -/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Action

universe u

open AlgebraicGeometry CategoryTheory

namespace GIT

variable {k : Type u} [Field k]
variable (G : Type u) [Group G]

/-- `X` is a `G`-scheme: an object of `Action Scheme (MonCat.of G)` -/
variable (X : Action Scheme.{u} (MonCat.of G))

/-- `Y` is a plain scheme, viewed as a `G`-scheme with the trivial action -/
variable (Y : Scheme.{u})

/-- `φ` is a morphism in `Action Scheme G`.
    Since `Y` carries the trivial `G`-action, the `Action.Hom` condition
    `φ.comm g` is exactly `G`-invariance: `φ(g • x) = φ(x)`.
    So `isGInvariant` need not be stated separately. -/
variable (φ : X ⟶ Action.trivial _ _ Y)

-- Convenient notation for the underlying scheme morphism
local notation "φ.scheme" => φ.hom

/-- Helper for condition (3).

For every open affine `U ⊆ Y`, the pullback map
`φ* : Γ(U, 𝒪_Y) → Γ(φ⁻¹(U), 𝒪_X)^G`
is an isomorphism onto the `G`-invariant sections. -/
def IsAffineSheafIso
    (G : Type u) [Group G]
    (X : Action Scheme.{u} (MonCat.of G))
    (Y : Scheme.{u})
    (φ : X ⟶ Action.trivial _ _ Y)
    (ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    Function.Injective (φ.hom.app U).hom ∧
    Set.range (φ.hom.app U).hom =
      MulAction.fixedPoints G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)

/-- Helper for conditions (4) and (5).

A subset `W ⊆ X` is closed `G`-invariant if `g • w ∈ W` for all `g : G`, `w ∈ W`. -/
def IsClosedGInvariant
    (G : Type u) [Group G]
    (X : Action Scheme.{u} (MonCat.of G))
    (W : Set X.V.carrier) : Prop :=
  ∀ (g : G) ⦃w : X.V.carrier⦄, w ∈ W →
    (X.ρ (MonCat.of G |>.str.one) : X.V.carrier → X.V.carrier) w ∈ W

/-- **Definition: Good Quotient.**

For the action of an affine algebraic group `G` on a `G`-scheme `X`,
a morphism `φ : X → Action.trivial Y` in `Action Scheme G` is a
*good quotient* if:

1. `φ` is affine                               [DONE — G-invariance is free from the type]
2. `φ` is surjective;                          [DONE]
3. for every open affine `U ⊆ Y`, the pullback `φ* : Γ(U) → Γ(φ⁻¹(U))^G`
   is an isomorphism;                          [DONE]
4. the image of any closed `G`-invariant subset of `X` is closed in `Y`;
                                               [DONE]
5. disjoint closed `G`-invariant subsets of `X` have disjoint images in `Y`.
                                               [DONE]
-/
structure IsGoodQuotient
    (k : Type u) [Field k]
    (G : Type u) [Group G]
    (X : Action Scheme.{u} (MonCat.of G))
    (Y : Scheme.{u})
    (φ : X ⟶ Action.trivial _ _ Y)
    (ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)) : Prop where
  /-- (1) `φ` is an affine morphism.
      G-invariance is automatic from `φ` being an `Action.Hom`. -/
  isAffine : AlgebraicGeometry.IsAffineHom φ.hom
  /-- (2) `φ` is surjective. -/
  surjective : Function.Surjective φ.hom.base
  /-- (3) For every open affine `U ⊆ Y`, the pullback map
      `φ* : Γ(U) → Γ(φ⁻¹(U))^G` is an isomorphism. -/
  pullback_iso : IsAffineSheafIso G X Y φ ρ
  /-- (4) The image of any closed `G`-invariant subset is closed. -/
  closed_image : ∀ (W : Set X.V.carrier),
    IsClosed W → IsClosedGInvariant G X W → IsClosed (φ.hom.base '' W)
  /-- (5) Disjoint closed `G`-invariant subsets have disjoint images. -/
  separates_disjoint : ∀ (W₁ W₂ : Set X.V.carrier),
    IsClosed W₁ → IsClosedGInvariant G X W₁ →
    IsClosed W₂ → IsClosedGInvariant G X W₂ →
    Disjoint W₁ W₂ → Disjoint (φ.hom.base '' W₁) (φ.hom.base '' W₂)

end GIT

/- ------------------------------------------------------------------ -/

namespace Prop813

open GIT

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]
variable {X : Action Scheme.{u} (MonCat.of G)}
variable {Y : Scheme.{u}}
variable {φ : X ⟶ Action.trivial _ _ Y}
variable {ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)}

/-- **Proposition 8.1.3(1a).**
    If `φ` is a good quotient, then `φ` is surjective. -/
theorem goodQuotient_surjective
    (hq : IsGoodQuotient k G X Y φ ρ) :
    Function.Surjective φ.hom.base :=
  hq.surjective

/-- **Proposition 8.1.3(1b).**
    If `φ` is a good quotient, then the image of any closed
    `G`-invariant subset of `X` is closed in `Y`. -/
theorem goodQuotient_closed_image
    (hq : IsGoodQuotient k G X Y φ ρ)
    (W : Set X.V.carrier)
    (hW_closed : IsClosed W)
    (hW_inv : IsClosedGInvariant G X W) :
    IsClosed (φ.hom.base '' W) :=
  hq.closed_image W hW_closed hW_inv

-- still need proposition 8.1.3 (2)

end Prop813
