# Propositions

## goodQuotient_surjective — Proposition 8.1.3 (1a)

Let $G$ be a linearly reductive group acting on a scheme $U$, and let $\pi : U \to X$ be a good quotient. Then $\pi$ is surjective.

**Proof.**
Since $\pi$ is affine, surjectivity may be checked locally on $X$. 
Let $V = \text{Spec}(A) \subseteq X$ be an affine open subset and write $\pi^{-1}(V) = \text{Spec}(B)$. 
By definition of a good quotient, $A \cong B^G$, so it suffices to show $\text{Spec}(B) \to \text{Spec}(B^G)$ is surjective.

Let $\mathfrak{p} \subset B^G$ be a prime ideal. 
Since $G$ is linearly reductive, there exists a Reynolds operator $R : B \to B^G$, which is $B^G$-linear and satisfies $R|_{B^G} = \mathrm{id}$. 
For any $f \in \mathfrak{p} \cdot B$, we can write $f = \sum_i f_i b_i$ with $f_i \in \mathfrak{p}$ and $b_i \in B$, so

$$R(f) = \sum_i f_i R(b_i) \in \mathfrak{p}.$$

Hence $R(\mathfrak{p} \cdot B) \subseteq \mathfrak{p} \subsetneq B^G$, which shows $\mathfrak{p} \cdot B \neq B$ (since $R(1) = 1 \notin \mathfrak{p}$).

Therefore $\mathfrak{p} \cdot B$ is a proper ideal of $B$, and by Zorn's lemma it is contained in some prime ideal $\mathfrak{q} \subset B$. 
This prime satisfies $\mathfrak{q} \cap B^G = \mathfrak{p}$, so $\mathfrak{p}$ is in the image of $\text{Spec}(B) \to \text{Spec}(B^G)$. $\blacksquare$

## goodQuotient_closed_image — Proposition 8.1.3 (1b)

If $\varphi$ is a good quotient and $W \subseteq X$ is a closed $G$-invariant subset, then $\varphi(W)$ is closed in $Y$.