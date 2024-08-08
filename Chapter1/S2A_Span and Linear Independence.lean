import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.Module.Basic
import Aesop
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation



section
variable (F M : Type*)
variable [Field F] [AddCommGroup M] [Module F M]

variable (a₁ a₂ a₃ a₄ : F)
variable (v₁ v₂ v₃ v₄: M)

-- 2.3 Definition: linear combination
#check a₁ • v₁ + a₂ • v₂ + a₃ • v₃ + a₄ • v₄


-- 2.4 example
example : ![17, -4, 2] = (6 : ℝ) • ![(2 : ℝ), 1, -3] + (5 : ℝ) • ![(1 : ℝ), -2, 4] := by
  ext x
  fin_cases x
  · simp; linarith
  · simp; linarith
  · simp; linarith


example : ¬∃ (a₁ : ℝ) (a₂ : ℝ), ![(17 : ℝ), -4, 5] = a₁ • ![2, 1, -3] + a₂ • ![1, -2, 4] := by
  intro ⟨a₁, a₂, h⟩
  have h₁ : 17 = a₁ * 2 + a₂ * 1 := congrFun h 0
  have h₂ : -4 = a₁ * 1 + a₂ * -2 := congrFun h 1
  have h₃ : 5 = a₁ * -3 + a₂ * 4 := congrFun h 2
  linarith


-- 2.5 Definition: Span
-- In mathlib, we have `Submodule.span` which is corresponding to the definition of span.
#check Submodule.span

-- The span of the empty list () is defined to be {0}.
#check Submodule.span_empty

-- Beside, mathlib introduce the notation `R • v` for the span of a singleton, `Submodule.span R {v}`.

-- 2.6 example
-- FIXME: There must be a more concise solution. The following is too foolish.
example : ![17, -4, 2] ∈ Submodule.span ℝ {![(2 : ℝ), 1, -3], ![1, -2, 4]} := by
  rw [mem_span_set]
  let c : (Fin 3 → ℝ) →₀ ℝ := {
    support := {![2, 1, -3], ![1, -2, 4]}
    toFun := fun v => if v = ![2, 1, -3] then 6 else if v = ![1, -2, 4] then 5 else 0
    mem_support_toFun := by
      intro a
      constructor <;> intro h
      · intro h'; aesop
      · simp; aesop
  }
  use c; simp at *; constructor
  · rfl
  · ext x
    fin_cases x
    · unfold Finsupp.sum
      simp_all
      have : {![2, 1, -3], ![1, -2, 4]} = ({![2, 1, -3]} : Finset (Fin 3 → ℝ)) ∪ {![1, -2, 4]} := by aesop
      have h' : ![(1 : ℝ), -2, 4] ≠ ![2, 1, -3] := by
        intro h
        have : (1 : ℝ) = 2 := by
          calc
            1 = ![(1 : ℝ), -2, 4] 0 := by rfl
            _ = ![(2 : ℝ), 1, -3] 0 := by rw [h]
            _ = 2 := by rfl
        linarith
      rw [this, Finset.sum_union]
      dsimp [c]
      simp_all
      norm_num
      rw [Finset.disjoint_singleton]
      aesop
    · unfold Finsupp.sum
      simp_all
      have : {![2, 1, -3], ![1, -2, 4]} = ({![2, 1, -3]} : Finset (Fin 3 → ℝ)) ∪ {![1, -2, 4]} := by aesop
      have h' : ![(1 : ℝ), -2, 4] ≠ ![2, 1, -3] := by
        intro h
        have : (1 : ℝ) = 2 := by
          calc
            1 = ![(1 : ℝ), -2, 4] 0 := by rfl
            _ = ![(2 : ℝ), 1, -3] 0 := by rw [h]
            _ = 2 := by rfl
        linarith
      rw [this, Finset.sum_union]
      dsimp [c]
      simp_all
      norm_num
      rw [Finset.disjoint_singleton]
      aesop
    · unfold Finsupp.sum
      simp_all
      have : {![2, 1, -3], ![1, -2, 4]} = ({![2, 1, -3]} : Finset (Fin 3 → ℝ)) ∪ {![1, -2, 4]} := by aesop
      have h' : ![(1 : ℝ), -2, 4] ≠ ![2, 1, -3] := by
        intro h
        have : (1 : ℝ) = 2 := by
          calc
            1 = ![(1 : ℝ), -2, 4] 0 := by rfl
            _ = ![(2 : ℝ), 1, -3] 0 := by rw [h]
            _ = 2 := by rfl
        linarith
      rw [this, Finset.sum_union]
      dsimp [c]
      simp_all
      norm_num
      rw [Finset.disjoint_singleton]
      aesop


example : ![17, -4, 5] ∉ Submodule.span ℝ {![(2 : ℝ), 1, -3], ![1, -2, 4]} := by
  intro h
  rw [mem_span_set] at h
  rcases h with ⟨c ,hc, h⟩
  simp at c
  unfold Finsupp.sum at h
  sorry

-- 2.7 Span is the smallest containing subspace
-- `Submodule.span_le` and `Submodule.subset_span` in mathlib together describe this fact.
#check Submodule.subset_span
#check Submodule.span_le




#check Pi.basisFun ℝ (Fin 2)

example : DFunLike.coe (Pi.basisFun ℝ (Fin 2)) = ![![1, 0], ![0, 1]] := by
  ext i j
  sorry



-- 2.8 Definitions: Spans
-- In mathlib, we can express `span(v₁,...,vₙ) equals V` as follows (because `Submodule.top_coe`):
example : Submodule.span ℝ {![(1 : ℝ), 0], ![0, 1]} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  simp at x
  by_cases h : x = 0
  · sorry
  -- x ≠ 0 now
  rw [mem_span_set]
  let c : (Fin 2 → ℝ) →₀ ℝ := {
    support := {![(1 : ℝ), 0], ![0, (1 : ℝ)]}
    toFun := fun v => if v = ![(1 : ℝ), 0] then x 0 else if v = ![0, (1 : ℝ)] then x 1 else 0
    mem_support_toFun := by
      intro a
      sorry
  }
  use c
  simp_all
  constructor
  · apply subset_rfl
  · unfold Finsupp.sum
    simp_all
    have : {![1, 0], ![0, 1]} = ({![1, 0]} : Finset (Fin 2 → ℝ)) ∪ {![0, 1]} := by aesop
    rw [this, Finset.sum_union]
    dsimp [c]
    have : ![(0 : ℝ), 1] ≠ ![(1 : ℝ), 0] := by sorry
    funext i
    fin_cases i <;> simp_all
    rw [Finset.disjoint_singleton]
    intro h
    have h₁ : 1 = 0 := congrFun h 0
    linarith

-- 2.9 example
-- In mathlib, the canonical basis is packed up as `Pi.basisFun`
#check Pi.basisFun

example (n : ℕ) : (⨆ k, F ∙ (Pi.basisFun F (Fin n) k)) = ⊤ := by
  rw [← Submodule.span_range_eq_iSup, (Pi.basisFun F (Fin n)).span_eq]

-- 2.10 Definition: finite-dimensional vector space
-- `FiniteDimensional` in mathlib captures this property.
-- `FiniteDimensional.finrank` is exactly the dimension of a finite-dimensional vector space.

#check FiniteDimensional
#check FiniteDimensional.finrank

-- `FiniteDimensional.of_fintype_basis` is exactly the definition of finite-dimensional vector space in the book.

#check FiniteDimensional.of_fintype_basis


-- *example 2.9* show that `Fⁿ` is finite-dimensional with dimension `n`

example {n : ℕ} : FiniteDimensional F (Fin n → F) := by
  apply FiniteDimensional.of_fintype_basis (Pi.basisFun F (Fin n))

example {n : ℕ} : FiniteDimensional.finrank F (Fin n → F) = n := by
  aesop

-- 2.11 Definition: polynomial
-- `Polynomial` in Mathlib

-- 2.12 Definition: Degree of a polynomial
-- `Polynomial.degree` in Mathlib

#check Polynomial.degree

-- 2.13 Definition: the set of all polynomials with degree at most `n`
-- `Polynomial.degreeLE` in Mathlib
variable (n : WithBot ℕ) (R : Type _) [Semiring R]
#check Polynomial.degreeLE R n


#check Polynomial.mem_degreeLE


-- 2.14 example
-- `Polynomial.degreeLE R n` have type `Submodule R (Polynomial R)` show that Pₙ(R) is vector space over R
-- Below show that `Polynomial.degreeLE R n` is `n`-dim

example (n : ℕ) (R : Type _) [Field R] : FiniteDimensional.finrank R (Polynomial.degreeLE R n) = n := by
  sorry

-- 2.15 Definition: infinite-dimensional vector space

#check ¬FiniteDimensional F M


-- TODO) 2.16 example: `P(F)` is infinite-dimensional


-- 2.17 Definition: linearly independent
-- In mathlib, `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

#check LinearIndependent

-- `linearIndependent_iff` shows that `LinearIndependdent` is equal to the definition in the book.
#check linearIndependent_iff
  #check Finsupp.total
    #check Finsupp.lsum
    #check LinearMap.id

-- The empty list `()` is also declared to be linearly independent.
#check linearIndependent_empty_type


-- TODO) 2.18.a example
-- use `LinearIndependent.ne_zero` to prove one direction

-- TODO) 2.18.b example

-- TODO) 2.18.c example

-- TODO) 2.18.d example

/-
TODO:
If some vectors are removed from a linearly independent list, the remaining
list is also linearly independent, as you should verify.
-/

-- 2.19 Definition: linearly dependent
-- Exactly `¬LinearIndependent`

#check not_linearIndependent_iff

-- TODO) 2.20.a example
-- TODO) 2.20.b example
-- TODO) 2.20.c example
-- TODO) 2.20.d example


-- TODO) 2.21 Linear Dependence lemma


-- TODO) 2.23 Length of linearly independent list ≤ length of spanning list

-- TODO) 2.24 example
-- Prove this using 2.23

-- TODO) 2.25 example
-- Prove this using 2.23

-- 2.26 Finite-dimensional subspaces
/-
Every subspace of a finite-dimensional vector space is finite-dimensional.
-/

#check FiniteDimensional.finiteDimensional_submodule


end
