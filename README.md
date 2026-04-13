# Formalizing Geometric Invariant Theory (GIT)

This is a Lean formalization project, part of the Math AI Lab at the University of Washington, aiming to formalize different aspects of Geometric Invariant Theory (GIT).

The study of taking quotients in algebraic geometry, unlike in general topology, has the additional burden of having to define an algebraic structure (such as a variety or a scheme structure) on the quotient. GIT gives us one possible route to tackle this.

## Directions

There are two main directions of formalization, each building on a common starting point.

**i) Commutative Algebra**

We want to formalize and prove the following theorem: given a linearly reductive group G acting on a finitely generated k-algebra R, the invariant ring R^G is a finitely generated k-algebra. For a quick exposition, see [here](https://amathew.wordpress.com/2011/09/03/invariant-theory-for-reductive-groups/).

**ii) Geometry**

We want to formalize the definition of an "affine good quotient" and prove the first main theorem of GIT: if G is a linearly reductive group acting on an affine k-variety X = Spec A, then Spec A^G is an affine good quotient (where A^G is the ring of invariants). For quick reference, see [here](https://drive.google.com/file/d/1HxKrLlUn7sDAUW2AqJ_-z_DcEkpnLV_1/view?usp=drive_link).

## Common Starting Point

The first step is to formalize the definition of a **linearly reductive group** ( see [here](https://github.com/Arkamouli1996/Formalizing-geometric-invariant-theory-GIT-/blob/main/Basics%20of%20reductive%20groups.md)). Once this is done, we should do sanity checks by proving that a finite group is an example when the underlying field has characterestic 0. A natural next step would be to prove that GL_n and SL_n are also examples.