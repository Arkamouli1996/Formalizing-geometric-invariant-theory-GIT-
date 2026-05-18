/- definition of good quotient -/

import Mathlib.CategoryTheory.Action.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine

universe u

open AlgebraicGeometry CategoryTheory

namespace GIT

variable (G : Type u) [Group G]

/-- **Helper predicate: local `Spec A → Spec A^G` structure.**

For a morphism `π : X ⟶ Action.trivial G Y` in `Action Scheme G` and a per-open
`G`-action `ρ` on the local sections of `X.V` over preimages `π⁻¹U`, this
predicate asserts that for every affine open `U ⊆ Y`, the structure-sheaf
pullback `π.hom.app U : Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_X)` is injective and its image
is exactly the `G`-invariant sections.

This is the substantive content of "good quotient" beyond just being an affine
`G`-invariant morphism — locally `π` looks like `Spec A → Spec A^G`.

The `G`-action `ρ` on local sections is taken as a hypothesis here; in a
complete formalization it should be derived from `X.ρ` together with the
`G`-invariance of `π⁻¹U` (which follows from the equivariance of `π`). -/
def IsInvariantSections
    {G : Type u} [Group G]
    {X : Action Scheme.{u} G} {Y : Scheme.{u}}
    (π : X ⟶ Action.trivial G Y)
    (ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨π.hom ⁻¹ᵁ U⟩)) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    Function.Injective (π.hom.app U).hom ∧
    Set.range (π.hom.app U).hom =
      MulAction.fixedPoints G (X.V.presheaf.obj ⟨π.hom ⁻¹ᵁ U⟩)

/-- **Definition: Good Quotient (skeleton).**

For a `G`-scheme `X : Action Scheme G`, a *good quotient* of `X` is the data of:

* a scheme `Y`,
* a morphism `π : X ⟶ Action.trivial G Y` in `Action Scheme G` (since `Y`
  carries the trivial `G`-action, the morphism's equivariance condition
  `X.ρ g ≫ π.hom = π.hom ≫ (trivial G Y).ρ g` simplifies to
  `X.ρ g ≫ π.hom = π.hom`, i.e. `π` is automatically `G`-invariant),
* a per-open `G`-action `ρ` on local sections of `X.V` over preimages `π⁻¹U`,

satisfying:

1. **`isAffine`** — `π` is an affine morphism;
2. **`invariantSections`** — locally `π` looks like `Spec A → Spec A^G`;
   see `IsInvariantSections`.

The classical full definition adds three further conditions — surjectivity,
closed-image of `G`-invariant closed subsets, and separation of disjoint
closed `G`-invariant subsets — which can be added as additional fields when
needed. -/
structure GoodQuotient (X : Action Scheme.{u} G) where
  /-- The underlying quotient scheme. -/
  Y : Scheme.{u}
  /-- The quotient morphism, as a morphism in `Action Scheme G` to the
  trivially-acted-on `Y`. The category structure encodes `G`-equivariance,
  which (given the trivial action on `Y`) is `G`-invariance of the underlying
  scheme map. -/
  π : X ⟶ Action.trivial G Y
  /-- Per-open `G`-action on local sections. Should be derivable from `X.ρ`
  plus the `G`-invariance of `π⁻¹U`; taken as a hypothesis here. -/
  ρ : ∀ U : Y.Opens, MulAction G (X.V.presheaf.obj ⟨π.hom ⁻¹ᵁ U⟩)
  /-- `π` is an affine morphism (G-invariance comes for free from the category). -/
  affine : IsAffineHom π.hom
  /-- Locally, `π` looks like `Spec A → Spec A^G`: for every affine open
  `U ⊆ Y`, the pullback `π* : Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_X)^G` is an isomorphism. -/
  invariantSections : IsInvariantSections π ρ

end GIT
