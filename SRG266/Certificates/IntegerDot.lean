/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Integer dot products

This module isolates the small executable definition shared by the finite
certificate checkers.  In particular, clients that only evaluate a checker
do not need to import the general Farkas soundness proof.
-/

open scoped BigOperators

namespace SRG266

/-- Integer dot product, named locally to keep certificate statements
independent of scalar-product APIs. -/
def integerDot
    {ι : Type*} [Fintype ι]
    (u v : ι → ℤ) : ℤ :=
  ∑ i, u i * v i

end SRG266
