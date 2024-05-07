import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.VecNotation

@[reducible]
def Tuple (α : Type _) (n : ℕ) := Fin n → α

namespace Tuple

variable {F : Type _} [Field F]
variable {n : ℕ} (x y : Tuple F n)

example : ![2, 3] + ![5, 7] = ![7, 10] := by simp

@[simp]
theorem add_def : x + y = fun i => x i + y i :=
  rfl

theorem tuple_add_comm : x + y = y + x := by
  funext i
  simp
  apply add_comm


instance : Zero (Tuple F n) :=
  ⟨fun _ => 0⟩


@[simp]
theorem zero_def : (0 : Tuple F n) = fun _ => 0 :=
  rfl

example : 0 = ![(0 : ℝ), 0] := by
  funext i
  rw [zero_def]
  cases' i with val property
  interval_cases val
  · simp
  simp

variable (v : Tuple F n)

theorem add_zero : v + 0 = v := by simp

theorem zero_add : 0 + v = v := by simp

-- 1.16  Definition  additive inverse in F^n
instance : Neg (Tuple F n) :=
  ⟨fun v i => -v i⟩

@[simp]
theorem neg_neg {v : Tuple F n} : -v = fun i => -v i :=
  rfl

theorem add_neg : v + -v = 0 := by simp

theorem neg_add : -v + v = 0 := by simp

instance : SMul F (Tuple F n) :=
  ⟨fun a v i => a * v i⟩

@[simp]
theorem smul_mul {a : F} : a • v = fun i => a * v i :=
  rfl

end Tuple
