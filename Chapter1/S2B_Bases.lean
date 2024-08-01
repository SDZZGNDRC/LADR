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
A list v1;:::; vn of vectors in V is a basis of V if and only if every v 2 V
can be written uniquely in the form

FIXME: Maybe need to use other terms in mathlib to express this.
Because `Basis.repr` is a function, that means a vector `v` is uniquely written as a linear combination of basis vectors.
A function can not map a value to multiple values.

-/

#check Basis.repr_injective -- FIXME: ?
