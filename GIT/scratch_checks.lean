import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.FiniteType

open scoped DirectSum

namespace Scratch

variable {k : Type} [Field k]
variable {R : Type} [CommRing R] [Algebra k R]
variable {𝒜 : ℕ → Submodule k R} [GradedAlgebra 𝒜]

-- Quick lemma name discovery.

#check FiniteType
#check Algebra.FiniteType

#check DirectSum.decompose
#check DirectSum.decompose_of_mem_same
#check DirectSum.decompose_of_mem_ne

-- try to locate graded multiplication projection lemmas
#check DirectSum.coe_decompose_mul_of_right_mem_of_le
#check DirectSum.coe_decompose_mul_of_right_mem_of_not_le

-- Print them to find file/nearby helpers.
#print DirectSum.coe_decompose_mul_of_right_mem_of_le
#print DirectSum.coe_decompose_mul_of_right_mem_of_not_le

#check SetLike.GradedMul.mul_mem

end Scratch

