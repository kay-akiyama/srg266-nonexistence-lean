/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusCore

/-! # Executable trace-vector data for the glued E7 core -/

namespace SRG266
namespace Lattice

/-- Scaled coordinates of the `A₇` vector `8 e_i - 1`. -/
def e7TraceRow (i : Fin 8) : Fin 8 → ℤ := fun j => if j = i then 28 else -4

/-- Scaled coordinates of `8 e_i - 1` in one E7 factor. -/
def e7e7PlusTraceVector : Bool → Fin 8 → E7E7PlusIndex → ℤ
  | false, i => Sum.elim (e7TraceRow i) fun _ => 0
  | true, i => Sum.elim (fun _ => 0) (e7TraceRow i)

/-- Sparse lattice coefficients of a trace vector. -/
def e7e7PlusTraceCoeff : Bool → Fin 8 → Fin 14 → ℤ
  | false, i, k =>
      if i = 0 then
        if k = 0 then 28
        else if k.1 < 7 then -8
        else if k = 7 then -14
        else 0
      else
        if k = 0 then -4
        else if k = 7 then 2
        else if k.1 = i.1 then 8
        else 0
  | true, i, k =>
      if i = 0 then
        if k = 7 then 14
        else if 8 ≤ k.1 then -8
        else 0
      else
        if k = 7 then -2
        else if k.1 = 7 + i.1 then 8
        else 0

end Lattice
end SRG266
