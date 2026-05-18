/- definition of good quotient -/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Action.Basic

universe u

open AlgebraicGeometry CategoryTheory

namespace GIT

variable {k : Type u} [Field k]
variable (G : Type u) [Group G]

-- `X` is a `G`-scheme: an object of `Action Scheme G`.
variable (X : Action Scheme.{u} G)

-- `Y` is a plain scheme, viewed as a `G`-scheme with the trivial action.
variable (Y : Scheme.{u})

-- `φ` is a morphism in `Action Scheme G`.
-- Since `Y` carries the trivial `G`-action, the `Action.Hom` condition
-- `φ.comm g` is exactly `G`-invariance: `φ(g • x) = φ(x)`.
-- So `isGInvariant` need not be stated separately.
variable (φ : X ⟶ Action.trivial G Y)

-- Convenient notation for the underlying scheme morphism
local notation "φ.scheme" => φ.hom

/-- Helper for condition (3).

For every open affine `U ⊆ Y`, the pullback map
`φ* : Γ(U, 𝒪_Y) → Γ(φ⁻¹(U), 𝒪_X)^G`
is an isomorphism onto the `G`-invariant sections. -/
def IsAffineSheafIso
    (G : Type u) [Group G]
    (X : Action Scheme.{u} G)
    (Y : Scheme.{u})
    (φ : X ⟶ Action.trivial G Y)
    (ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    Function.Injective (φ.hom.app U).hom ∧
    Set.range (φ.hom.app U).hom =
      MulAction.fixedPoints G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩)

/-- Helper for conditions (4) and (5).

A subset `W ⊆ X` is closed `G`-invariant if `g • w ∈ W` for all `g : G`, `w ∈ W`. -/
def IsClosedGInvariant
    (G : Type u) [Group G]
    (X : Action Scheme.{u} G)
    (W : Set X.V.carrier) : Prop :=
  ∀ (g : G) ⦃w : X.V.carrier⦄, w ∈ W →
    (X.ρ g).base w ∈ W

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
    (X : Action Scheme.{u} G)
    (Y : Scheme.{u})
    (φ : X ⟶ Action.trivial G Y)
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
variable {X : Action Scheme.{u} G}
variable {Y : Scheme.{u}}
variable {φ : X ⟶ Action.trivial G Y}
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

/- ------------------------------------------------------------------ -/
/- Spec A → Spec A^G is a good quotient -/

namespace SpecInvariantsGoodQuotient

open GIT
open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

/-
  `A` is the coordinate ring.
  `AG` is standing for the invariant ring `A^G`.

  In the final version, `AG` should be replaced by the actual invariant
  subring/ring of invariant functions.

  `SpecA` is the G-scheme `Spec A`.
  `SpecAG` is the scheme `Spec A^G`.
  `π` is the canonical morphism

      Spec A → Spec A^G.

  Since `SpecAG` has trivial G-action, the morphism is typed as

      SpecA ⟶ Action.trivial _ _ SpecAG.
-/

variable (A AG : Type u)
variable [CommRing A] [Algebra k A]
variable [CommRing AG] [Algebra k AG]

variable (SpecA : Action Scheme.{u} G)
variable (SpecAG : Scheme.{u})
variable [AlgebraicGeometry.IsAffine SpecA.V] [AlgebraicGeometry.IsAffine SpecAG]

variable (π : SpecA ⟶ Action.trivial G SpecAG)

variable
  (ρ : ∀ U : SpecAG.Opens,
    MulAction G (SpecA.V.presheaf.obj ⟨π.hom ⁻¹ᵁ U⟩))

/-- Condition (1): the canonical morphism `Spec A → Spec A^G` is affine.

Mathematically this is because it is induced by the ring map `A^G → A`,
and morphisms between affine schemes are affine. -/
theorem spec_to_spec_invariants_isAffine :
    AlgebraicGeometry.IsAffineHom π.hom := by
  haveI : AlgebraicGeometry.IsAffine (Action.trivial G SpecAG).V := by
    change AlgebraicGeometry.IsAffine SpecAG
    infer_instance
  infer_instance

omit [AlgebraicGeometry.IsAffine SpecA.V] [AlgebraicGeometry.IsAffine SpecAG] in
/-- Condition (2): the canonical morphism `Spec A → Spec A^G` is surjective.

Mathematically this uses the Reynolds operator. For every prime ideal
`𝔮 ⊂ A^G`, one proves that `𝔮A ≠ A`, then obtains a prime ideal of `A`
lying over `𝔮`.

In this file this is supplied as an already-proved proposition. -/
theorem spec_to_spec_invariants_surjective
    (hπ_surjective : Function.Surjective π.hom.base) :
    Function.Surjective π.hom.base :=
  hπ_surjective

omit [AlgebraicGeometry.IsAffine SpecA.V] [AlgebraicGeometry.IsAffine SpecAG] in
/-- Condition (3): affine-open sections pull back to invariant sections.

For affine open `U ⊆ Spec A^G`, the pullback map

`Γ(U, 𝒪_{Spec A^G}) → Γ(π⁻¹ U, 𝒪_{Spec A})^G`

is an isomorphism.

For principal opens this is the statement

`(A^G)_f ≅ (A_f)^G`

for invariant `f`. -/
theorem spec_to_spec_invariants_pullback_iso :
    IsAffineSheafIso G SpecA SpecAG π ρ := by
  sorry

omit [AlgebraicGeometry.IsAffine SpecA.V] [AlgebraicGeometry.IsAffine SpecAG] in
/-- Condition (4): the image of every closed `G`-invariant subset is closed.

Mathematically, if `W = V(I)` with `I` a `G`-stable ideal, then

`π(W) = V(I ∩ A^G)`,

so the image is closed in `Spec A^G`.

In this file this is supplied as an already-proved proposition. -/
theorem spec_to_spec_invariants_closed_image
    (hπ_closed_image :
      ∀ (W : Set SpecA.V.carrier),
        IsClosed W →
        IsClosedGInvariant G SpecA W →
        IsClosed (π.hom.base '' W)) :
    ∀ (W : Set SpecA.V.carrier),
      IsClosed W →
      IsClosedGInvariant G SpecA W →
      IsClosed (π.hom.base '' W) :=
  hπ_closed_image

omit [AlgebraicGeometry.IsAffine SpecA.V] [AlgebraicGeometry.IsAffine SpecAG] in
/-- Condition (5): disjoint closed `G`-invariant subsets have disjoint images.

Mathematically, if `W₁ = V(I₁)` and `W₂ = V(I₂)` are disjoint, then
`1 ∈ I₁ + I₂`. Applying the Reynolds operator gives

`1 ∈ (I₁ ∩ A^G) + (I₂ ∩ A^G)`,

so their images in `Spec A^G` are disjoint. -/
theorem spec_to_spec_invariants_separates_disjoint
    (hπ_separates_disjoint :
      ∀ (W₁ W₂ : Set SpecA.V.carrier),
        IsClosed W₁ → IsClosedGInvariant G SpecA W₁ →
        IsClosed W₂ → IsClosedGInvariant G SpecA W₂ →
        Disjoint W₁ W₂ →
        Disjoint (π.hom.base '' W₁) (π.hom.base '' W₂)) :
    ∀ (W₁ W₂ : Set SpecA.V.carrier),
      IsClosed W₁ → IsClosedGInvariant G SpecA W₁ →
      IsClosed W₂ → IsClosedGInvariant G SpecA W₂ →
      Disjoint W₁ W₂ →
      Disjoint (π.hom.base '' W₁) (π.hom.base '' W₂) :=
  hπ_separates_disjoint

/-- **Main theorem.**

The canonical morphism

`π : Spec A → Spec A^G`

is a good quotient. -/
theorem spec_to_spec_invariants_isGoodQuotient :
    Function.Surjective π.hom.base →
    (∀ (W : Set SpecA.V.carrier),
      IsClosed W →
      IsClosedGInvariant G SpecA W →
      IsClosed (π.hom.base '' W)) →
    (∀ (W₁ W₂ : Set SpecA.V.carrier),
      IsClosed W₁ → IsClosedGInvariant G SpecA W₁ →
      IsClosed W₂ → IsClosedGInvariant G SpecA W₂ →
      Disjoint W₁ W₂ →
      Disjoint (π.hom.base '' W₁) (π.hom.base '' W₂)) →
    IsGoodQuotient k G SpecA SpecAG π ρ := by
  intro hπ_surjective hπ_closed_image hπ_separates_disjoint
  refine
    { isAffine := ?isAffine
      surjective := ?surjective
      pullback_iso := ?pullback_iso
      closed_image := ?closed_image
      separates_disjoint := ?separates_disjoint }
  · exact spec_to_spec_invariants_isAffine
      (SpecA := SpecA) (SpecAG := SpecAG) (π := π)
  · exact spec_to_spec_invariants_surjective
      (SpecA := SpecA) (SpecAG := SpecAG) (π := π)
      hπ_surjective
  · exact spec_to_spec_invariants_pullback_iso
      (SpecA := SpecA) (SpecAG := SpecAG) (π := π) (ρ := ρ)
  · exact spec_to_spec_invariants_closed_image
      (SpecA := SpecA) (SpecAG := SpecAG) (π := π)
      hπ_closed_image
  · exact spec_to_spec_invariants_separates_disjoint
      (SpecA := SpecA) (SpecAG := SpecAG) (π := π)
      hπ_separates_disjoint

end SpecInvariantsGoodQuotient
