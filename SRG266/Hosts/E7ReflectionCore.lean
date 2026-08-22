/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7WeightCore

/-!
# Lightweight E7 coordinate reflections

This module contains only the executable root predicate and reflection path
evaluator shared by E7 certificate checkers.
-/

namespace SRG266

/-- Boolean characterization of the 126 roots of `E₇` in doubled
coordinates.

The conditions say that the coordinates sum to zero, have squared norm
eight, and all have the same parity. -/
def e7IsRoot (a : Fin 8 → ℤ) : Bool :=
  decide (
    (∑ i, a i) = 0 ∧
    integerDot a a = 8 ∧
    ∀ i, a i % 2 = a 0 % 2)

/-- Apply one checked `E₇` root reflection in doubled coordinates. -/
def e7Reflect? (y a : Fin 8 → ℤ) : Option (Fin 8 → ℤ) :=
  if e7IsRoot a then
    let z := integerDot y a
    if z % 4 = 0 then
      some (fun i => y i - (z / 4) * a i)
    else
      none
  else
    none

/-- Apply a declarative sequence of checked root reflections. -/
def e7ApplyReflections :
    (Fin 8 → ℤ) → List (Fin 8 → ℤ) → Option (Fin 8 → ℤ)
  | y, [] => some y
  | y, a :: roots =>
      (e7Reflect? y a).bind fun z => e7ApplyReflections z roots

end SRG266
