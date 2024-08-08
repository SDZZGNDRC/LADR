import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Algebra.Module.Basic
import Aesop
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

-- 2.27 Definition: Basis
/-
A basis of V is a list of vectors in V that is linearly independent and spans V.
-/

#check Basis.mk
#check Basis.span


-- TODO) 2.28.a example
-- TODO) 2.28.b example
-- TODO) 2.28.c example
-- TODO) 2.28.d example
-- TODO) 2.28.e example
-- TODO) 2.28.f example
-- TODO) 2.28.g example

-- TODO) 2.29 Criterion for basis
/-
A list v1;:::; vn of vectors in V is a basis of V if and only if every v in V
can be written uniquely in the form:
v = a₁ • v₁ + ... + aₙ • vₙ

FIXME: Maybe need to use other terms in mathlib to express this.
Because `Basis.repr` is a function, that means a vector `v` is uniquely written as a linear combination of basis vectors.
A function can not map a value to multiple values.

`congrArg` in mathlib.

-/

#check congrArg

#check Basis.repr_injective -- FIXME: ?


-- TODO) 2.31 Spanning list contains a basis

-- may help:
#check Basis.le_span

-- 2.32 Basis of finite-dimensional vector space

/-
Every finite-dimensional vector space has a basis.

`Basis.exists_basis` in mathlib states the existence of a nonempty-basis.
-/

#check Basis.exists_basis

-- 2.33 Linearly independent list extends to a basis

/-
Every linearly independent list of vectors in a finite-dimensional vector
space can be extended to a basis of the vector spattce.

`Basis.extend` in mathlib describes this fact.
-/

#check Basis.extend

-- TODO) 2.34 Every subspace of V is part of a direct sum equal to V

/-
Suppose V is finite-dimensional and U is a subspace of V. Then there is a
subspace W of V such that V ⨁ U = W.
-/
section
variable (F V : Type*)
variable [Field F] [AddCommGroup V] [Module F V]

theorem theo_2_34 (U : Submodule F V) : ∃ W : Submodule F V, IsCompl U W := by
  sorry


end
