Short summary of reductive groups. The diagram below is taken from Jarod Alper's book [here](https://sites.math.washington.edu//~jarod/expository.html)


<img width="937" height="127" alt="Screenshot 2026-03-19 213735" src="https://github.com/user-attachments/assets/82d96480-6f48-49f4-b8b6-333bfea223cd" />

## Background: What is a Group Action on a Vector Space?

A **representation** of a group G is simply a vector space V together with a group 
homomorphism G → GL(V), i.e. each group element acts as an invertible linear map on V.
A **subrepresentation** is a subspace W ⊆ V that is sent to itself by every g ∈ G.
A representation is **irreducible** if it has no subrepresentations other than {0} and V itself.
A representation is **completely reducible** if it decomposes as a direct sum of irreducible 
subrepresentations.

---
## Definitions

Let $G$ be a linear algebraic group over a field $k$.

**Linearly reductive.** $G$ is linearly reductive if every finite-dimensional representation
of $G$ is completely reducible.

**Geometrically reductive.** $G$ is geometrically reductive if for every finite-dimensional
representation $V$ of $G$ and every nonzero fixed vector $v \in V^G$, there exists a
homogeneous $G$-invariant polynomial

$$f \in \mathrm{Sym}^d(V^\ast)^G$$

for some $d \ge 1$ such that $f(v) \neq 0$.

**Reductive.** $G$ is reductive if its unipotent radical is trivial; equivalently, $G$ has
no nontrivial connected normal unipotent subgroup.
