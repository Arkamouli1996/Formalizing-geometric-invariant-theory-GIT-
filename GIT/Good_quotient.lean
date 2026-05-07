/- definition of good quotient -/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
/- package for surjective morphisms -/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RepresentationTheory.Rep
import Mathlib.Algebra.Group.Action.Defs

universe u

open AlgebraicGeometry CategoryTheory

namespace GIT

variable {k : Type u} [Field k]
variable (G : Type u) [Group G]
variable (X Y : Scheme.{u})
variable [MulAction G X.carrier]
variable (φ : X ⟶ Y)

/-- Helper for condition (1) of the good-quotient definition.

A morphism `φ : X → Y` is `G`-invariant if it is constant on `G`-orbits,
i.e. `φ (g • x) = φ x` for all `g : G` and `x : X`.

This is factored out so that the proof that `φ` is `G`-invariant for a
specific `φ` can be written outside the `IsGoodQuotient` structure. -/
def IsGInvariant (G : Type u) [Group G] (X Y : Scheme.{u})
    [MulAction G X.carrier] (φ : X ⟶ Y) : Prop := sorry

/-- Helper for condition (3) of the good-quotient definition.

For every open affine `U ⊆ Y`, the pullback map
`φ* : Γ(U, 𝒪_Y) → Γ(φ⁻¹(U), 𝒪_X)^G`
induced by `φ` is an isomorphism onto the `G`-invariant sections.

This is factored out so that the proof of property (3) for a specific `φ`
can be written outside the `IsGoodQuotient` structure. -/
def IsAffineSheafIso
    (G : Type u) [Group G]
    (X Y : Scheme.{u})
    [MulAction G X.carrier]
    (φ : X ⟶ Y) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
  (sorry : Prop)

/-- Helper for conditions (4) and (5) of the good-quotient definition.

A subset `W ⊆ X` is (closed) `G`-invariant if it is closed under the
`G`-action: `g • w ∈ W` for every `g : G` and `w ∈ W`.

This is factored out so that the hypotheses of properties (4) and (5)
can be stated and discharged outside the `IsGoodQuotient` structure. -/
def IsClosedGInvariant (G : Type u) [Group G] (X : Scheme.{u})
    [MulAction G X.carrier] (W : Set X.carrier) : Prop := sorry


/-- **Definition 1.2.1 (Good Quotient).**

For the action of an affine algebraic group `G` on a variety `X`, a morphism
`φ : X → Y` is a *good quotient* if:

1. `φ` is affine and `G`-invariant;            [TODO: `IsGInvariant` still `sorry`]
2. `φ` is surjective;                          [DONE]
3. for every open affine `U ⊆ Y`, the pullback `φ* : Γ(U) → Γ(φ⁻¹(U))^G`
   is an isomorphism;                          [TODO]
4. the image of any closed `G`-invariant subset of `X` is closed in `Y`;
                                               [DONE (modulo `IsClosedGInvariant`)]
5. disjoint closed `G`-invariant subsets of `X` have disjoint images in `Y`.
                                               [DONE (modulo `IsClosedGInvariant`)]
-/
structure IsGoodQuotient
    (k : Type u) [Field k]
    (G : Type u) [Group G]
    (X Y : Scheme.{u})
    [MulAction G X.carrier]
    (φ : X ⟶ Y) : Prop where
  /-- (1a) `φ` is an affine morphism. -/
  isAffine : AlgebraicGeometry.IsAffineHom φ
  /-- (1b) `φ` is `G`-invariant. (TODO) -/
  isGInvariant : IsGInvariant G X Y φ
  /-- (2) `φ` is surjective. -/
  surjective : Function.Surjective φ.base
  /-- (3) For every open affine `U ⊆ Y`, the pullback map
      `φ* : Γ(U) → Γ(φ⁻¹(U))^G` is an isomorphism. (TODO) -/
  pullback_iso : IsAffineSheafIso G X Y φ
  /-- (4) The image of any closed `G`-invariant subset is closed. -/
  closed_image : ∀ (W : Set X.carrier),
    IsClosed W → IsClosedGInvariant G X W → IsClosed (φ.base '' W)
  /-- (5) Disjoint closed `G`-invariant subsets have disjoint images. -/
  separates_disjoint : ∀ (W₁ W₂ : Set X.carrier),
    IsClosed W₁ → IsClosedGInvariant G X W₁ →
    IsClosed W₂ → IsClosedGInvariant G X W₂ →
    Disjoint W₁ W₂ → Disjoint (φ.base '' W₁) (φ.base '' W₂)

end GIT
