import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.Module.Basic
import Aesop
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation


-- Definition 1.32 Subspace
-- The definition in mathlib is `Submodule R M`
#check Submodule

-- Example 1.33 {(x₁,x₂,0): x₁, x₂ ∈ 𝔽} is a subspace of 𝔽³
def subspace_ex1_33 : Submodule ℝ (Fin 3 → ℝ) where
  carrier := { ![x₁, x₂, (0 : ℝ)] | (x₁ : ℝ) (x₂ : ℝ)}
  zero_mem' := by simp
  add_mem' := by aesop
  smul_mem' := by aesop

-- 1.34 Conditions for a subspace
-- The three conditions are corresponding to `zero_mem`, `add_mem` and `smul_mem` in `Submodule`
#check Submodule.zero_mem
#check Submodule.add_mem
#check Submodule.smul_mem


-- 1.35 example in `exercise_1C.lean`

-- 1.36 Definition: sum of subspaces
-- The standard notation in mathlib is `U ⊔ V` (or `U + V` in Pointwise)
-- Of course we can prove the following
section
variable (F M : Type*)
variable [Semiring F] [AddCommMonoid M] [Module F M]

example {U V : Submodule F M} : (U + V).carrier = { x | ∃ a ∈ U, ∃ b ∈ V, a + b = x} := by
  simp
  ext x; simp [Set.mem_add]
  constructor <;> intro h
  · apply Submodule.mem_sup.mp h
  · aesop

end

-- 1.37 example
open Pointwise
def subspace_ex1_37_U : Submodule ℝ (Fin 3 → ℝ) where
  carrier :=  { ![x₁, 0, 0] | (x₁: ℝ)}
  zero_mem' := by simp
  add_mem' := by simp; intro _ _ x c y d; use (x + y); rw [←c, ←d]; ext z; simp; fin_cases z <;> simp
  smul_mem' := by simp

def subsdpace_ex1_37_V : Submodule ℝ (Fin 3 → ℝ) where
  carrier := { ![0, x₂, 0] |  (x₂ : ℝ)}
  zero_mem' := by simp
  smul_mem' := by simp
  add_mem' := by simp; intro _ _ x c y d; use (x + y); rw [←c, ←d]; ext z; simp; fin_cases z <;> simp

theorem ex1_37: subspace_ex1_37_U.carrier + subsdpace_ex1_37_V.carrier = { ![x₁, x₂, 0] | (x₁: ℝ) (x₂: ℝ)} := by
  dsimp [subspace_ex1_37_U, subsdpace_ex1_37_V]
  ext x ; simp [Set.mem_add]

#synth Module ℝ (subspace_ex1_37_U + subsdpace_ex1_37_V)

-- 1.38 example
def subspace_ex1_38_U : Submodule ℝ (Fin 4 → ℝ) where
  carrier := { ![x, x, y, y] | (x : ℝ) (y : ℝ)}
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop

def subspace_ex1_38_W : Submodule ℝ (Fin 4 → ℝ) where
  carrier := { ![x, x, x, y] | (x : ℝ) (y : ℝ)}
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop

theorem ex1_38: subspace_ex1_38_U.carrier + subspace_ex1_38_W.carrier = { ![x, x, y, z] | (x : ℝ) (y: ℝ) (z : ℝ)} := by
  dsimp [subspace_ex1_38_U, subspace_ex1_38_W]
  ext X; simp [Set.mem_add];
  constructor <;> intro h
  · aesop
  · rcases h with ⟨x, y, z, hx, hy, hz⟩
    use x - y, 0, y, z
    aesop

#synth Module ℝ (subspace_ex1_38_U + subspace_ex1_38_W)

-- 1.39 Sum of subspaces is the smallest containing subspace
section
variable (F M : Type*)
variable [Semiring F] [AddCommMonoid M] [Module F M]

-- basically we use `sup_le_iff` to prove it.
#check sup_le_iff

example {U V : Submodule F M} : ∀ W, U ≤ W ∧ V ≤ W → U + V ≤ W := by
  intro W ⟨hU, hV⟩
  simp_all only [Submodule.add_eq_sup, sup_le_iff, and_self]

end

-- 1.40 Definition: direct sum
-- NOTICE: (Maybe?) `∃! u ∈ U, ∃! v ∈ V, u + v = 0` is not equivalent to `∃! uv : M × M, uv.1 ∈ U ∧ uv.2 ∈ V → uv.1 + uv.2 = 0`
section
variable (F M : Type*)
variable [Ring F] [AddCommGroup M] [Module F M]
def isDirectSum {F M : Type*} [Semiring F] [AddCommMonoid M] [Module F M] (U V : Submodule F M) : Prop :=
    ∀ x ∈ U + V, ∃! uv : M × M , uv.1 ∈ U ∧ uv.2 ∈ V ∧ uv.1 + uv.2 = x
    -- ∀ x ∈ U + V, ∃! uv : M × M , uv.1 ∈ U ∧ uv.2 ∈ V → uv.1 + uv.2 = x

-- Given 1.45, for simpilation, we will use `Disjoint U V` to ensure `U + V` is a direct sum in the following codes instead of `isDirectSum U V`.

-- 1.41 example: {![x, y, 0]} ⨁ {![0, 0, z]} = F³
def ex1_41_U: Submodule F (Fin 3 → F) where
  carrier := { ![x, y, 0] | (x: F) (y: F) }
  add_mem' := by aesop
  smul_mem' := by aesop
  zero_mem' := by simp

def ex1_41_V: Submodule F (Fin 3 → F) where
  carrier := { ![0, 0, z] | (z: F) }
  add_mem' := by aesop
  smul_mem' := by aesop
  zero_mem' := by simp

example : IsCompl (ex1_41_U F) (ex1_41_V F) := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff (ex1_41_U F ⊓ ex1_41_V F)]
    intro X hX
    rw [Submodule.mem_inf] at hX
    have h₁ : X ∈ { ![x, y, 0] | (x: F) (y: F) } := by aesop
    have h₂ : X ∈ {![0, 0, z] | (z: F) } := by aesop
    simp at h₁ h₂
    rcases h₁ with ⟨x, y, h'⟩
    rcases h₂ with ⟨z, h''⟩
    ext i
    fin_cases i <;> simp
    · rw [←h'']; simp
    · rw [←h'']; simp
    · rw [←h']; simp
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro X
    rw [Submodule.mem_sup]
    let y := ![X 0, X 1, 0]
    let z := ![0, 0, X 2]
    use y
    constructor
    · apply (Submodule.mem_carrier (ex1_41_U F)).mp
      dsimp [ex1_41_U]; aesop
    · use z
      constructor
      · apply (Submodule.mem_carrier (ex1_41_V F)).mp
        dsimp [ex1_41_V]; aesop
      · ext i
        fin_cases i <;> simp
        · dsimp [y, z]; aesop
        · dsimp [y, z]; aesop
        · dsimp [y, z]; aesop




-- 1.42 TODO: example


-- 1.43 TODO: example


-- 1.44 Condition for a direct sum

theorem isDirectSum_iff_zero_unique (U V : Submodule F M) :
    isDirectSum U V ↔ ∀ u ∈ U, ∀ v ∈ V, u + v = 0 → u = 0 ∧ v = 0 := by
      unfold isDirectSum; constructor <;> intro h
      · rintro u hu v hv uv_zero
        let zero : M × M := (0, 0)
        have h : _ := h 0 (by aesop)
        have h₁ : zero.1 ∈ U ∧ zero.2 ∈ V ∧ zero.1 + zero.2 = 0 := by aesop
        have h₂ : (u, v).1 ∈ U ∧ (u, v).2 ∈ V ∧ (u, v).1 + (u, v).2 = 0 := by aesop
        have : _ := ExistsUnique.unique h h₁ h₂
        have : _ := Prod.ext_iff.mp this
        simp at this
        aesop
      · rintro x hx
        apply exists_unique_of_exists_of_unique
        · have : _ := Submodule.mem_sup.mp hx
          aesop
        · intro y₁ y₂ _ _
          have : (y₁.1 - y₂.1) + (y₁.2 - y₂.2) = 0 := by
            have : y₁.1 + y₁.2 = y₂.1 + y₂.2 := by aesop
            rw [←add_sub_assoc, add_comm_sub, ←add_sub_assoc, this]
            simp
          have : y₁.1 - y₂.1 = 0 ∧ y₁.2 - y₂.2 = 0 := h _ (by aesop) _ (by aesop) this
          apply Prod.ext
          · apply sub_eq_zero.mp this.1
          · apply sub_eq_zero.mp this.2


-- 1.45 Direct sum of two subspaces
-- Suppose U and W are subspaces of V. Then U + W is a direct sum if and only if U ∩ W = {0}.
theorem isDirectSum_iff_inter_eq_zero (U V : Submodule F M) :
    isDirectSum U V ↔ Disjoint U V := by
    apply Iff.trans (isDirectSum_iff_zero_unique _ _ U V)
    rw [disjoint_iff]
    constructor
    · intro h
      ext x
      constructor <;> intro h'
      · have : _ := h x (by aesop) (-x) (by aesop) (by aesop)
        aesop
      · aesop
    · intro h u hu v _ huv
      have h' : u = -v := eq_neg_of_add_eq_zero_left huv
      have : u ∈ U ⊓ V := Submodule.mem_inf.mpr ⟨hu, (by aesop)⟩
      aesop
