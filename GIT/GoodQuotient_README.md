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
