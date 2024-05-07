import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
-- set_option pp.all true
variable {F : Type*} (a b : ℝ) [Field F]
-- variable {V : Type _} [AddCommGroup V] [Module F V]
-- [Module F (Fin 3 → F)]

example {m : Set (Fin 3 → F)}
        (h : ∀ x, x 0 + 2 * x 1 + 3 * x 2 = 0 ↔ x ∈ m)
        : ∃ n : Submodule F (Fin 3 → F), m = n := by
  let s : Submodule F (Fin 3 → F) := {
      carrier := m
      zero_mem' := by
        let f := fun (_ : Fin 3) => (0 : F)
        have : f 0 + 2 * f 1 + 3 * f 2 = 0 := by ring
        -- simp
        exact (h f).mp this
      add_mem' := by
        rintro a b am bm
        have h₀ : _ := (h a).mpr am
        have h₁ : _ := (h b).mpr bm
        apply (h (a+b)).mp
        simp
        rw [←add_zero (a 0 + 2 * a 1 + 3 * a 2)] at h₀
        nth_rewrite 1 [←h₁] at h₀
        rw [←h₀]
        ring
      smul_mem' := by
        rintro c v vm
        simp at *
        have h' : (c • v) 0 + 2 * (c • v) 1 + 3 * (c • v) 2 = 0 := by
          simp
          ring_nf
          rw [mul_assoc, mul_assoc, ←mul_add, ←mul_add, mul_eq_zero.mpr]
          right
          have : _ := (h v).mpr vm
          ring_nf at this
          exact this
        exact (h (c • v)).mp h'
  }
  use s; rfl

example {m : Set (Fin 3 → ℂ)}
        (h : ∀ x, x 0 + 2 * x 1 + 3 * x 2 = 4 ↔ x ∈ m)
        : (0 : Fin 3 → ℂ) ∉ m := by
  intro h'
  have : _ := (h (0 : Fin 3 → ℂ)).mpr h'
  simp at this

example {m : Set (Fin 3 → F)}
        (h : ∀ x, x 0 - 5 * x 2 = 0 ↔ x ∈ m)
        : ∃ n : Submodule F (Fin 3 → F), m = n := by
  let s : Submodule F (Fin 3 → F) := {
      carrier := m
      zero_mem' := by
        let f := fun (_ : Fin 3) => (0 : F)
        have : f 0 - 5 * f 2 = 0 := by ring
        exact (h f).mp this
      add_mem' := by
        rintro a b am bm
        have h₀ : _ := (h a).mpr am
        have h₁ : _ := (h b).mpr bm
        apply (h (a+b)).mp
        simp
        rw [←add_zero (a 0 - 5 * a 2)] at h₀
        nth_rewrite 1 [←h₁] at h₀
        rw [←h₀]
        ring
      smul_mem' := by
        rintro c v vm
        simp at *
        have h' : (c • v) 0 - 5 * (c • v) 2 = 0 := by
          simp
          ring_nf
          rw [mul_assoc, ←mul_sub c (v 0) (v 2 * 5), mul_eq_zero.mpr]
          right
          have : _ := (h v).mpr vm
          ring_nf at this
          exact this
        exact (h (c • v)).mp h'
  }
  use s; rfl

-- example 1.35 (a)
example {m : Set (Fin 4 → F)} {b : F}
        (h : ∀ x, x 2 - 5 * x 3 - b = 0 ↔ x ∈ m)
        : b = 0 ↔ ∃ n : Submodule F (Fin 4 → F), m = n := by
  sorry

-- example 1.35 (b)
open Set
variable (f g : ℝ → ℝ)
example : f + g = fun x => f x + g x := by rfl

def R01 := {x : ℝ // x ∈ Set.Icc 0 1}

example [TopologicalSpace R01]
        {m : Set (R01 → ℝ)}
        (h : ∀ x, x ∈ m ↔ Continuous x)
        : ∃ n : Submodule ℝ (R01 → ℝ), m = n := by
  let s : Submodule ℝ (R01 → ℝ) := {
    carrier := m
    add_mem' := by
      rintro a b am bm
      have ca : _ := (h a).mp am
      have cb : _ := (h b).mp bm
      have cab : Continuous (a+b) := Continuous.add ca cb
      exact (h (a+b)).mpr cab
    zero_mem' := by
      simp
      exact (h 0).mpr continuous_zero
    smul_mem' := by
      simp
      rintro c x xm
      have cx : Continuous x := (h x).mp xm
      exact (h (c • x)).mpr (Continuous.const_smul cx c)
  }
  use s; rfl

-- example 1.35 (c)
example {m : Set (ℝ → ℝ)}
        (h : ∀ f, f ∈ m ↔ Differentiable ℝ f)
        : ∃ n : Submodule ℝ (ℝ → ℝ), m = n := by
  let s : Submodule ℝ (ℝ → ℝ) := {
    carrier := m
    add_mem' := by
      rintro a b am bm
      apply (h (a+b)).mpr
      have da : _ := (h a).mp am
      have db : _ := (h b).mp bm
      exact Differentiable.add da db
    zero_mem' := by
      simp
      apply (h 0).mpr (differentiable_const 0)
    smul_mem' := by
      simp
      rintro c x xm
      have dx : _ := (h x).mp xm
      have : Differentiable ℝ (fun y => c • x y) := by
        exact Differentiable.const_smul dx c
      exact (h (c • x)).mpr this
  }
  use s; rfl

-- example 1.35 (d)

def R03 := {x : ℝ // x ∈ Set.Ioo 0 3}

example {m : Set (R03 → ℝ)}
        [NontriviallyNormedField R03] [NormedSpace R03 ℝ]
        [SMulCommClass R03 ℝ ℝ]
        (h : ∀ f, f ∈ m ↔ Differentiable R03 f ∧ HasDerivAt f 0 2)
        : ∃ n : Submodule ℝ (R03 → ℝ), m = n := by
  let s : Submodule ℝ (R03 → ℝ) := {
    carrier := m
    add_mem' := by
      rintro a b am bm
      apply (h (a+b)).mpr
      constructor
      · apply Differentiable.add ((h a ).mp am).left ((h b ).mp bm).left
      · rw [←zero_add 0]
        apply HasDerivAt.add ((h a).mp am).right ((h b).mp bm).right
    zero_mem' := by
      simp
      apply (h 0).mpr; constructor
      · apply differentiable_const 0
      · apply hasDerivAt_const 2 0
    smul_mem' := by
      simp; rintro c x xm
      apply (h (c • x)).mpr; constructor
      · apply Differentiable.const_smul ((h x).mp xm).left c
      · have : _ := HasDerivAt.const_smul c ((h x).mp xm).right
        rw [←smul_zero c]
        exact this
  }
  use s; rfl

example {B : ℝ} {m : Set (R03 → ℝ)}
        [NontriviallyNormedField R03] [NormedSpace R03 ℝ]
        [SMulCommClass R03 ℝ ℝ]
        (h : ∀ f, f ∈ m ↔ Differentiable R03 f ∧ HasDerivAt f B 2)
        : B = 0 ↔ ∃ n : Submodule ℝ (R03 → ℝ), m = n := by
  constructor
  · intro Bzero
    let s : Submodule ℝ (R03 → ℝ) := {
      carrier := m
      add_mem' := by
        rintro a b am bm
        apply (h (a+b)).mpr
        constructor
        · apply Differentiable.add ((h a ).mp am).left ((h b ).mp bm).left
        · rw [Bzero, ←zero_add 0]
          have : _ := HasDerivAt.add ((h a).mp am).right ((h b).mp bm).right
          rw [Bzero] at this
          exact this
      zero_mem' := by
        simp
        apply (h 0).mpr; constructor
        · apply differentiable_const 0
        · rw [Bzero]; apply hasDerivAt_const 2 0
      smul_mem' := by
        simp; rintro c x xm
        apply (h (c • x)).mpr; constructor
        · apply Differentiable.const_smul ((h x).mp xm).left c
        · have : _ := HasDerivAt.const_smul c ((h x).mp xm).right
          rw [Bzero, ←smul_zero c]
          rw [Bzero] at this
          exact this
    }
    use s; rfl
  · rintro ⟨w, h'⟩
    sorry


-- example 1.35 (e)
example {m : Set (ℕ → ℂ)} : True := by trivial


-- exercise 3
def Rn44 := {x : ℝ // x ∈ Set.Ioo (-4) 4}

example {m : Set (Rn44 → ℝ)}
        [NontriviallyNormedField Rn44] [NormedSpace Rn44 ℝ]
        [SMulCommClass Rn44 ℝ ℝ]
        (h : ∀ f, f ∈ m ↔ Differentiable Rn44 f ∧ HasDerivAt f (3*(f 2)) (-1))
        : ∃ n : Submodule ℝ (Rn44 → ℝ), m = n := by
  let s : Submodule ℝ (Rn44 → ℝ) := {
    carrier := m
    add_mem' := by
      rintro a b am bm
      apply (h (a+b)).mpr
      constructor
      · apply Differentiable.add ((h a ).mp am).left ((h b ).mp bm).left
      · rw [Pi.add_def]; simp; rw [mul_add]
        apply HasDerivAt.add ((h a).mp am).right ((h b).mp bm).right
    zero_mem' := by
      simp
      apply (h 0).mpr; constructor
      · apply differentiable_const 0
      · simp; apply hasDerivAt_const (-1) 0
    smul_mem' := by
      simp; rintro c x xm
      apply (h (c • x)).mpr; constructor
      · apply Differentiable.const_smul ((h x).mp xm).left c
      · have : _ := HasDerivAt.const_smul c ((h x).mp xm).right
        rw [Pi.smul_def]; simp at *
        rw [←mul_assoc]
        rw [←mul_assoc, mul_comm c 3] at this
        exact this
  }
  use s; rfl



-- exercise 4

-- exercise 5: ℝ² is a subspace of ℂ² over ℝ
          --ℝ² isn't a subspace of ℂ² over ℂ
example {m : Set (Fin 2 → ℂ)}
        (h : ∀ x, x ∈ m ↔ (x 0).im = 0 ∧ (x 1).im = 0)
        : ∃ n : Submodule ℝ (Fin 2 → ℂ), m = n := by
  let n : Submodule ℝ (Fin 2 → ℂ) := {
    carrier := m
    add_mem' := by
      rintro a b am bm
      apply (h (a + b)).mpr
      simp
      have h₀ : _ := (h a).mp am
      have h₁ : _ := (h b).mp bm
      constructor
      · nth_rewrite 3 [←zero_add 0]
        nth_rewrite 1 [←h₀.1]
        rw [←h₁.1]
      · nth_rewrite 1 [←zero_add 0]
        nth_rewrite 1 [←h₀.2]
        rw [←h₁.2]
    zero_mem' := by
      apply (h 0).mpr; simp
    smul_mem' := by
      simp
      rintro c x xm
      apply (h (c • x)).mpr
      simp
      exact And.intro (Or.inr ((h x).mp xm).1) (Or.inr ((h x).mp xm).2)
  }
  use n; rfl
