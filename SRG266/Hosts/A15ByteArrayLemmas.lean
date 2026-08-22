/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Tactic

/-!
# Byte-array micro-API for the A15 pair histogram

The fast A15 eligible-shell counter stores a pair-sum histogram in a
`ByteArray` and addresses it with the partial operations `ByteArray.get!` and
`ByteArray.set!`.  Reasoning about that counter needs the handful of
elementary facts collected here: `set!` preserves the size, reads back the
written byte in range and leaves other positions untouched, `push` extends by
one byte, and a replicated array reads as zero everywhere.

Out-of-range `get!` returns `0` and out-of-range `set!` is a no-op, so several
statements below deliberately avoid range hypotheses; the two that do need one
(`a15ByteArray_get!_set!_self`, `a15ByteArray_get!_push_lt`) carry it
explicitly.
-/

namespace SRG266

set_option maxRecDepth 10000

/-- Writing a byte does not change the length. -/
theorem a15ByteArray_size_set! (a : ByteArray) (i : ℕ) (v : UInt8) :
    (a.set! i v).size = a.size := by
  cases a with | _ bs => simp [ByteArray.set!, ByteArray.size]

/-- Writing a byte leaves every other position untouched. -/
theorem a15ByteArray_get!_set!_ne (a : ByteArray) (i j : ℕ) (v : UInt8)
    (h : i ≠ j) : (a.set! i v).get! j = a.get! j := by
  cases a with | _ bs =>
  by_cases hj : j < bs.size
  · simp [ByteArray.set!, ByteArray.get!, getElem!_pos, hj, h]
  · simp [ByteArray.set!, ByteArray.get!, getElem!_neg, hj]

/-- An in-range write is read back. -/
theorem a15ByteArray_get!_set!_self (a : ByteArray) (i : ℕ) (v : UInt8)
    (h : i < a.size) : (a.set! i v).get! i = v := by
  cases a with | _ bs =>
  simp only [ByteArray.size] at h
  simp [ByteArray.set!, ByteArray.get!, getElem!_pos, h]

/-- A replicated zero byte array reads as zero at every position. -/
theorem a15ByteArray_get!_replicate (n i : ℕ) :
    (ByteArray.get! ⟨Array.replicate n 0⟩ i) = 0 := by
  by_cases h : i < n
  · simp [ByteArray.get!, getElem!_pos, h]
  · simp only [ByteArray.get!, getElem!_neg, h, Array.size_replicate,
      not_false_eq_true]
    rfl

/-- Pushing a byte extends the length by one. -/
theorem a15ByteArray_size_push (a : ByteArray) (x : UInt8) :
    (a.push x).size = a.size + 1 := by
  cases a with | _ bs => simp [ByteArray.push, ByteArray.size]

/-- Pushing a byte leaves the earlier positions untouched. -/
theorem a15ByteArray_get!_push_lt (a : ByteArray) (x : UInt8) (i : ℕ)
    (h : i < a.size) : (a.push x).get! i = a.get! i := by
  cases a with | _ bs =>
  simp only [ByteArray.size] at h
  have h2 : i < (bs.push x).size := by simp; omega
  simp only [ByteArray.push, ByteArray.get!, getElem!_pos, h, h2,
    Array.getElem_push_lt]

/-- The pushed byte lands at the previous length. -/
theorem a15ByteArray_get!_push_self (a : ByteArray) (x : UInt8) :
    (a.push x).get! a.size = x := by
  cases a with | _ bs =>
  simp [ByteArray.push, ByteArray.get!, ByteArray.size, getElem!_pos]

end SRG266
