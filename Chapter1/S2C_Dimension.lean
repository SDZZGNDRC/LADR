import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.Module.Basic
import Aesop
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.Basic

-- TODO) 2.35 Basis length does not depend on basis
/-
Any two bases of a finite-dimensional vector space have the same length.
-/

-- 2.36 Definition: Dimension, dim V

/-
`Module.rank` in mathlib.
-/

#check Module.rank      -- The dimension of a module.

/-
The dimension of a finite-dimensional vector space is the length of
any basis of the vector space.
-/
#check FiniteDimensional.finrank_eq_card_basis'


section

variable (F M : Type*)
variable [Field F] [AddCommGroup M] [Module F M]

-- 2.37.a example
example {n : ℕ} : FiniteDimensional.finrank F (Fin n → F) = n := by
  aesop

-- TODO) 2.37.b example

#check Polynomial.basisMonomials

-- 2.38 Dimension of a subspace
/-
If V is finite-dimensional and U is a subspace of V, then dim U ≤ dim V.
-/

#check Submodule.finrank_le


-- TODO) 2.39 Linearly independent list of the right length is a basis
/-
Suppose V is finite-dimensional. Then every linearly independent list of
vectors in V with length dim V is a basis of V.
-/

-- TODO) 2.40 example: Show that the list (5,7),(4,3) is a basis of F².
def ex_2_40 : Basis (Fin 2) F (Fin 2 → F) := {
  repr := sorry
}


-- TODO) 2.41 example

-- TODO) 2.42 Spanning list of the right length is a basis
/-
Suppose V is finite-dimensional. Then every spanning list of vectors in V
with length dim V is a basis of V.
-/


-- 2.43 Dimension of a sum
/-
If U₁ and U₂ are subspaces of V, then dim (U₁ + U₂) = dim U₁ + dim U₂ - dim (U₁ ⊓  U₂).

This exactly showed by `Submodule.rank_sup_add_rank_inf_eq` in mathlib
-/

#check Submodule.rank_sup_add_rank_inf_eq

end
