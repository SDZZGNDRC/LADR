import Mathlib.Tactic
import Chapter1.Tuple
variable (a b : ℝ) [Field F]
open Complex Real Tuple


-- exercise 1.A

example : ∃ c d :ℝ, 1 / ({re := a, im := b} : ℂ) = ({re := c, im := d} : ℂ) := by
  use a / (a^2 + b^2)
  use (-1 * b) / (a^2 + b^2)
  simp
  apply Complex.ext_iff.mpr
  constructor
  · simp; ring
  · simp; ring

example : ({re := -1, im := sqrt 3} / 2) ^ 3 = ({re := 1, im := 0} : ℂ) := by
  apply Complex.ext_iff.mpr
  have cp2 : {re := -1, im := sqrt 3} ^ 2 = {re := -1, im := sqrt 3} * {re := -1, im := sqrt 3  : ℂ} := by
    ring_nf
  have cp3: {re := -1, im := sqrt 3} ^ 3 = {re := -1, im := sqrt 3} ^ 2 * {re := -1, im := sqrt 3  : ℂ} := by
    ring_nf
  constructor
  · ring_nf; norm_num
    rw [cp3, Complex.mul_re]
    ring_nf
    rw [cp2, Complex.mul_re]
    simp; ring_nf; norm_num
  · ring_nf
    rw [cp3, cp2]
    simp; ring_nf

example : ∃ m n : ℂ, m ≠ n → m ^ 2 = {re := 0, im := 1} ∧ n ^ 2 = {re := 0, im := 1} := by
  -- 1st.      ((sqrt 2) / 2 ) * (1 + i)
  -- 2st. -1 * ((sqrt 2) / 2 ) * (1 + i)
  sorry

example : ∀ m n : ℂ, m + n = n + m := by
  apply add_comm

example : ∀ i j k : ℂ, (i + j) + k = i + (j + k) := by
  apply add_assoc

example : ∀ i j k : ℂ, (i * j) * k = i * (j * k) := by
  apply mul_assoc

example : ∀ α : ℂ, ∃! β, α + β = 0 := by
  intro α
  dsimp [ExistsUnique]
  use -α
  constructor
  · ring
  · rintro β αβ_eq_zero
    apply add_neg_eq_zero.mp
    ring_nf
    rw [add_comm β α]
    exact αβ_eq_zero

example : ∀ (α : ℂ), α ≠ 0 → ∃! β, α * β = 1 := by
  rintro α α_nonzero
  dsimp [ExistsUnique]
  use α⁻¹
  constructor
  · apply (mul_inv_eq_one₀ α_nonzero).mpr
    rfl
  · rintro β β_eq_α_inv
    rw [mul_comm] at β_eq_α_inv
    apply (mul_eq_one_iff_eq_inv₀ α_nonzero).mp β_eq_α_inv

example : ∀ γ α β : ℂ, γ * (α + β) = γ * α + γ * β := by
  rintro γ α β
  exact mul_add γ α β

example : ∃ x : Tuple ℝ 4, ![4, -3, 1, 7] + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  use ![1/2, 6, -(7/2), 1/2]
  ext x
  simp at x
  match x with
  | (0 : Fin 4) => simp; norm_num
  | (1 : Fin 4) => simp; norm_num
  | (2 : Fin 4) => simp; norm_num
  | (3 : Fin 4) =>
    simp
    have h₀ : ![4, -3, 1, 7] 3 = (7 : ℝ) := by rfl
    have h₁: ![2⁻¹, 6, -(7 / 2), 2⁻¹] 3 = (2⁻¹ : ℝ) := by rfl
    have h₂ : ![5, 9, -6, 8] 3 = (8 : ℝ) := by rfl
    rw [h₀, h₁, h₂]; ring_nf

example : ¬∃ α : ℂ, α • ![{re := 2, im := -3 : ℂ}, {re := 5, im := 4}, {re := -6, im := 7}] = ![{re := 12, im := -5 : ℂ}, {re := 7, im := 22}, {re := -32, im := 9}] := by
  sorry

example {n : ℕ} : ∀ x y z : Tuple F n, (x + y) + z = x + (y + z) := by
  apply add_assoc

example {n : ℕ} : ∀ x : Tuple F n, ∀ a b : F, (a*b) • x = a • (b • x) := by
  rintro x a b
  rw [smul_smul]

example {n : ℕ} : ∀ x : Tuple F n, 1 • x = x := by
  intro x
  exact one_smul _ x

example {n : ℕ} : ∀ α : F, ∀ x y : Tuple F n, α • (x + y) = α • x + α • y := by
  exact smul_add

example {n : ℕ} : ∀ a b : F, ∀ x : Tuple F n, (a + b) • x = a • x + b • x := by
  rintro a b x
  exact add_smul a b x
