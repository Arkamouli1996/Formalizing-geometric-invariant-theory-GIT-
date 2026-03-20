# Formalizing-geometric-invariant-theory-GIT-
This is a Lean formalization project, part of Math AI Lab at the University of Washington, aiming to formalize different aspects of geometric invariant theory aka GIT.

The study of taking quotients in algebraic geometry, unlike in general topology, has the additional burden of having to define an algebraic structure (such as a variety or a scheme structure) on the quotient. GIT gives us one possible route to tackle this.

In this project there are two main directions of formalization and one central starting point to tackle both directions. The two directions are:
i) commutative algebra: We want to formalize and prove the theorem - Given a linearly reductive group G acting on a finitely generated k-algebra R, the invariant ring R^G is a finitely generated k-algebra (reader can refer to https://amathew.wordpress.com/2011/09/03/invariant-theory-for-reductive-groups/ for a quick exposition)

ii) geometry: We want to formalize the defintion of an "affine good quotient" and formalize and prove the first main theorem of GIT - If G is a linearly reductive group acting on an affine k-variety X = Spec A, then Spec A^G is an affine good quotient (where A^G is the ring of invariants) (reader can refer to https://drive.google.com/file/d/1HxKrLlUn7sDAUW2AqJ_-z_DcEkpnLV_1/view?usp=drive_link )

The common starting point : 
The first thing to do is formalize the definition of a linearly reductive group. Once this is done, we should do sanity checks by proving that a finite group is an example. A next step would be to attempt to prove that GLn and SLn are also examples.
