import Mathlib.Tactic
import Chapter1.Tuple
-- import Chapter1.Vector
variable (a b : ℝ) [Field F]
open Complex Real

namespace LADR

variable {V : Type _} [AddCommGroup V] [Module F V]

example : ∀ v : V, -(-v) = v := by
  intro v
  have h₀ : -v + v = 0 := by simp
  have : -(-v) + (-v) = 0 := by simp
  rw [←h₀] at this
  have : -(-v) + (-v) + v = -v + v + v := by
    rw [this]
  have h₁ : -(-v) + (-v) + v = -(-v) + ((-v) + v) := by
    simp
  rw [h₁, h₀] at this
  have h₀: -(-v) + 0 = -(-v) := by simp
  have h₁: 0 + v = v := by simp
  rw [h₀, h₁] at this
  exact this

example {a : F} {v : V} : a • v = 0 → a = 0 ∨ v = 0 := by
  intro av_eq_zero
  by_cases h : a = 0
  · exact Or.inl h
  · right
    have : a = 0 ∨ v = 0 := by  apply smul_eq_zero.mp av_eq_zero
    exact (or_iff_right h).mp this

example {a : F} {v w : V} (h : a ≠ 0)
        : ∃! x, v + a • x = w := by
  dsimp [ExistsUnique]
  use (1/a) • (w - v)
  constructor
  · simp
    rw [←mul_smul, mul_inv_cancel, one_smul]
    simp; exact h
  · rintro u h'
    rw [←h']
    simp
    rw [←mul_smul, inv_mul_cancel, one_smul]; exact h

-- 4. prove that the empty set is not a vector space

-- 5. alternative definition of vector space

-- 6. ℝ∪{∞, -∞} is a vector space given the addition involved ∞ or -∞.
#check EReal
