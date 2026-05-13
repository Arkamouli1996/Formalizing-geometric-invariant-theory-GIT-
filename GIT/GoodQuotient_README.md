# Variables Defined
- k : field (this will be the base field)
- G : group (the acting group)
- X : Action Scheme (MonCat.of G) (Scheme with G-action)
- Y : Scheme (plain Scheme with trivial actions)
- phi : X ⟶ Action.trivial _ _ Y (Morphism in Action Scheme G)
- rho: ∀ U, MulAction G (X.V.presheaf.obj ⟨φ.hom ⁻¹ᵁ U⟩) (G-action on sections)

# Theorems

## goodQuotient_surjective — Proposition 8.1.3 (1a)
If φ is a good quotient, then φ is surjective.

Proof: Direct projection of the surjective field out of IsGoodQuotient.

## goodQuotient_closed_image — Proposition 8.1.3 (1b)
If φ is a good quotient and W ⊆ X is a closed G-invariant subset,
then φ(W) is closed in Y.

Hypotheses required:
- hW_closed : IsClosed W
- hW_inv : IsClosedGInvariant G X W

Proof: Direct projection of the closed_image field out of IsGoodQuotient.

Good Quotient Skeleton

This Lean file sets up the definition of a good quotient for a group action on schemes and states the theorem that the canonical morphism

SpecA→SpecA
G

is a good quotient.

Main Definitions

The file defines IsAffineSheafIso, IsClosedGInvariant, and IsGoodQuotient.

IsGoodQuotient k G X Y φ ρ means that the morphism

φ : X ⟶ Action.trivial _ _ Y

satisfies the five conditions of a good quotient:

φ is affine.
φ is surjective.
Pullback on affine opens identifies functions on Y with G-invariant functions on X.
Images of closed G-invariant subsets are closed.
Disjoint closed G-invariant subsets have disjoint images.
Main Theorem

The second part proves, with sorry placeholders, that

π:SpecA→SpecA
G

is a good quotient.

In the current skeleton, Spec A, Spec A^G, and π are represented abstractly as:

SpecA : Action Scheme.{u} (MonCat.of G)
SpecAG : Scheme.{u}
π : SpecA ⟶ Action.trivial _ _ SpecAG

The main theorem is:

theorem spec_to_spec_invariants_isGoodQuotient :
    IsGoodQuotient k G SpecA SpecAG π ρ := by

It is proved by filling in the five fields of IsGoodQuotient:

isAffine
surjective
pullback_iso
closed_image
separates_disjoint

Each field is currently proved by a separate theorem with sorry.

Mathematical Idea

The proof relies on the Reynolds operator

R:A→A
G

which is used to prove:

surjectivity of Spec A → Spec A^G,
equality of invariant localized sections,
closedness of images of invariant closed subsets,
separation of disjoint invariant closed subsets.
Current Status

This is a proof skeleton. The main structure is set up, but the difficult algebraic geometry arguments are left as sorry.
