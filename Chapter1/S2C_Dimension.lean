import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.Module.Basic
import Aesop
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.Basic

-- 2.35 Basis length does not depend on basis
/-
Any two bases of a finite-dimensional vector space have the same length.
-/

-- dimension theorem
#check mk_eq_mk_of_basis


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
-- may help:
#check linearIndependent_le_basis


-- TODO) 2.40 example: Show that the list (5,7),(4,3) is a basis of F².
noncomputable def ex_2_40 : Basis (Fin 2) F (Fin 2 → F) := Basis.ofEquivFun {
    toFun := fun v => fun x => match x with
      | 0 => 7 / 13 * (v 0) - 5 / 13 * (v 1)
      | 1 => -(3 / 13) * (v 0) + 4 / 13 * (v 1)
    map_add' := by sorry
    map_smul' := sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
  }

-- FIXME: Can we remove [LinearOrder F]
-- Show that list (1,1), (1,-1) is a basis of F².
noncomputable example : Basis (Fin 2) ℝ (Fin 2 → ℝ) := Basis.ofEquivFun {
  toFun := fun v => fun x => match x with
    | 0 => (v 0 + v 1) / 2
    | 1 => (v 0 - v 1) / 2
  map_add' := by
    intro a b
    ext x
    fin_cases x
    · simp_all
      linarith
    · simp_all
      linarith
  map_smul' := by
    intro r a
    ext x
    fin_cases x
    · simp_all
      linarith
    · simp_all
      linarith
  invFun := fun v => fun x => match x with
    | 0 => v 0 + v 1
    | 1 => v 0 - v 1
  left_inv := by
    simp_all
    dsimp [Function.LeftInverse]
    intro v
    ext x
    fin_cases x
    · simp_all
      linarith
    · simp_all
      linarith
  right_inv := by
    simp_all
    dsimp [Function.RightInverse]
    intro v
    ext x
    fin_cases x
    · simp_all
    · simp_all
}

-- may help:
#check Basis.ofEquivFun
#check Basis.finTwoProd
#check LinearEquiv.finTwoArrow
#check LinearEquiv
#check LinearMap
#check AddEquiv
  #check Equiv

-- TODO) 2.41 example

-- 2.42 Spanning list of the right length is a basis
/-
Suppose V is finite-dimensional. Then every spanning list of vectors in V
with length dim V is a basis of V.
TODO: Need to show that the rank is dim V.
-/
#check Basis.mk   -- A linear independent family of vectors spanning the whole module is a basis.

-- 2.43 Dimension of a sum
/-
If U₁ and U₂ are subspaces of V, then dim (U₁ + U₂) = dim U₁ + dim U₂ - dim (U₁ ⊓  U₂).

This exactly showed by `Submodule.rank_sup_add_rank_inf_eq` in mathlib
-/

#check Submodule.rank_sup_add_rank_inf_eq

end
