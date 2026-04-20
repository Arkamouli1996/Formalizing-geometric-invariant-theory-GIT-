/- Here I am trying to formalize if a group is linearly reductive
  then there exists a Reynolds operator -/

/- Definitions we need:
1. Linear action: An action of a group G on a vector space V
  over a field k is LINEAR if for all c ∈ k, g ∈ G, v,v₁,v₂ ∈ V:
    (i)  g • (c • v) = c • (g • v)
    (ii) g • (v₁ + v₂) = g • v₁ + g • v₂

2. G representation: A vector space V with a linear G-action.
  We write V = W ⊕ W' if:
    (i)  every v ∈ V can be written as v = w + w' with w ∈ W, w' ∈ W'
    (ii) W ∩ W' = {0}

3. Invariants: Given a G-representation V, the invariants are:
  V^G = { f ∈ V | g • f = f for all g ∈ G }

4. Linearly Reductive: G is linearly reductive if
  for every finite-dimensional V with a linear G-action, and every
  G-stable subspace W ⊆ V (i.e. g • w ∈ W for all g ∈ G, w ∈ W),
  there exists a G-stable complement W' such that:
    V = W ⊕ W'   as G-representations

5. Reynolds operator: A Reynolds operator is a NATURAL TRANSFORMATION  R : Id ⟹ (-)^G.
  (Note assumption: not assuming G is finite, or the characteristic of k does not divide the order of G)

    5.1. Two functors on Rep(G):
            1. Identity functor    Id      : M ↦ M
            2. Invariants functor  (-)^G   : M ↦ M^G

            This means: for each representation M, there is a linear map
            R_M : M → M^G such that for every G-equivariant map f : M → N,
            the square commutes:

                    M  ---f--->  N
                    |            |
                   R_M          R_N
                    |            |
                    ↓            ↓
                  M^G --f-->     N^G

            i.e.  R_N ∘ f = f ∘ R_M
            no matter if you do projection and then f or do f then projection,
            you will get the same result

    5.2. Naturality condition: R_N ∘ f = f ∘ R_M
    5.3. The map R_M must also satisfy:
        (a) R_M(m) ∈ M^G  for all m ∈ M
        - whatever vector you put in, the outcome satisfies the invariance condition
        (b) R_M(m) = m    for all m ∈ M^G
        - if you put in something that exists in the invariant, it comes out unchanged

        ex) Together,R_M is a projection onto M^G
        (x,y) -> (x,0) so whatever is on x is fixed and it's still on the x-axis.
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Group.Basic
import Mathlib.RingTheory.FiniteType

-- k is the field, G is the group
variable (k : Type*) [Field k]
variable (G : Type*) [Group G]
-- V is a vector space with a G-action
variable (V : Type*) [AddCommGroup V] [Module k V]

/-LINEAR ACTION-/
-- check g • (c • v) = c • (g • v)
#check @SMulCommClass G k V
-- check g • (v₁ + v₂) = g • v₁ + g • v₂
#check @DistribMulAction G V

/-G Representation-/
-- In mathlib, a representation is a group homomorphism
-- from G into the endomorphism of V
variable (ρ : Representation k G V)

/-Invariants-/
-- invariants defined as the submodule of vectors fixed by the group action

/-noncomputable: a marker for definitions that rely on
  non-constructive principles-/
noncomputable def invariants : Submodule k V :=
  ρ.invariants

/-Linearly reductive group-/
class LinearlyReductive (k G : Type*) [Field k] [Group G] where
  split_invariants :
  -- For every vector space V over k
    ∀ (V : Type*) [AddCommGroup V] [Module k V]
    -- choose a representation of G on V
      (ρ : Representation k G V),
      -- there exists some subspace
      ∃ W' : Submodule k V,
      -- such that V is the direct sum of the invariants and W'
        IsCompl ρ.invariants W'

-- projection v-> (w,w')-> w
