/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15PairHistogram

/-!
# Packing a bounded counting function into one natural number

The A15 magnitude search asks, at each of its 420,403 terminal norm profiles,
whether a reduced profile carries at least seventy-four eligible shell
vectors.  Answering that with the byte pair-sum histogram costs the kernel
about a second per profile, because every `ByteArray.set!` rebuilds a
sixty-nine element list inside the reduction.

Natural-number arithmetic is different: the Lean kernel evaluates
`Nat.shiftLeft`, `Nat.shiftRight`, `Nat.pow`, `HDiv.hDiv` and `HMod.hMod`
through GMP, so a single arithmetic step on a half-megabit operand is free.
This module sets up the dictionary that lets a whole counting *function* be
carried in one such natural number: `a15Pack c N` holds `c 0, …, c (N-1)` in
consecutive base-`2 ^ 32` digits, and `a15Digit` reads one back.

Three algebraic facts are all the caller needs.

* `a15Digit_pack` reads a digit back, provided every digit stays below the
  base.
* `a15Pack_add` adds two packed functions digitwise -- there is no carry
  precisely because the digits stay below the base.
* `a15Pack_shiftLeft` shifts a packed function by whole digits, which is what
  multiplying a generating function by a monomial does.

Nothing in this module is evaluated; it is pure rewriting.
-/

open scoped BigOperators

namespace SRG266

/-- The digit base `2 ^ 32`. -/
def a15DigitBase : ℕ := 4294967296

theorem a15DigitBase_eq : a15DigitBase = 2 ^ 32 := by
  norm_num [a15DigitBase]

theorem a15DigitBase_pos : 0 < a15DigitBase := by
  norm_num [a15DigitBase]

theorem a15DigitBase_pow (v : ℕ) : (2 : ℕ) ^ (32 * v) = a15DigitBase ^ v := by
  rw [pow_mul, a15DigitBase_eq]

/-- Digit `v` of a packed natural number. -/
def a15Digit (p v : ℕ) : ℕ := (p >>> (32 * v)) % a15DigitBase

theorem a15Digit_eq_div_mod (p v : ℕ) :
    a15Digit p v = p / a15DigitBase ^ v % a15DigitBase := by
  rw [a15Digit, Nat.shiftRight_eq_div_pow, a15DigitBase_pow]

/-- The natural number whose base-`2 ^ 32` digits are `c 0, …, c (N-1)`. -/
def a15Pack (c : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ v ∈ Finset.range N, c v * a15DigitBase ^ v

theorem a15Pack_zero (c : ℕ → ℕ) : a15Pack c 0 = 0 := by
  simp [a15Pack]

theorem a15Pack_succ (c : ℕ → ℕ) (N : ℕ) :
    a15Pack c (N + 1) = a15Pack c N + c N * a15DigitBase ^ N := by
  simp [a15Pack, Finset.sum_range_succ]

/-- A packed function with digits below the base fits in `N` digits. -/
theorem a15Pack_lt (c : ℕ → ℕ) (hc : ∀ v, c v < a15DigitBase) (N : ℕ) :
    a15Pack c N < a15DigitBase ^ N := by
  induction N with
  | zero => simp [a15Pack_zero, a15DigitBase]
  | succ N ih =>
      rw [a15Pack_succ, pow_succ]
      have hcN : c N + 1 ≤ a15DigitBase := hc N
      calc a15Pack c N + c N * a15DigitBase ^ N
          < a15DigitBase ^ N + c N * a15DigitBase ^ N := by omega
        _ = (c N + 1) * a15DigitBase ^ N := by ring
        _ ≤ a15DigitBase * a15DigitBase ^ N :=
            Nat.mul_le_mul_right _ hcN
        _ = a15DigitBase ^ N * a15DigitBase := by ring

/-- Reading back a digit of a packed function. -/
theorem a15Digit_pack (c : ℕ → ℕ) (hc : ∀ v, c v < a15DigitBase) :
    ∀ (N v : ℕ), a15Digit (a15Pack c N) v = if v < N then c v else 0 := by
  intro N
  induction N with
  | zero => intro v; simp [a15Pack_zero, a15Digit]
  | succ N ih =>
      intro v
      have hpos : 0 < a15DigitBase ^ N := Nat.pow_pos a15DigitBase_pos
      rcases lt_trichotomy v N with hv | hv | hv
      · have hvpos : 0 < a15DigitBase ^ v := Nat.pow_pos a15DigitBase_pos
        have hsplit : a15DigitBase ^ N =
            a15DigitBase ^ (N - v - 1) * a15DigitBase * a15DigitBase ^ v := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        have hdvd :
            c N * a15DigitBase ^ N =
              c N * a15DigitBase ^ (N - v - 1) * a15DigitBase * a15DigitBase ^ v := by
          rw [hsplit]
          ring
        rw [a15Digit_eq_div_mod, a15Pack_succ, hdvd,
          Nat.add_mul_div_right _ _ hvpos, Nat.add_mul_mod_self_right,
          ← a15Digit_eq_div_mod, ih v, if_pos hv, if_pos (by omega)]
      · subst hv
        have hlt : a15Pack c v < a15DigitBase ^ v := a15Pack_lt c hc v
        rw [a15Digit_eq_div_mod, a15Pack_succ,
          Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add,
          Nat.mod_eq_of_lt (hc v), if_pos (by omega)]
      · have hlt : a15Pack c (N + 1) < a15DigitBase ^ v := by
          refine lt_of_lt_of_le (a15Pack_lt c hc (N + 1)) ?_
          exact Nat.pow_le_pow_right a15DigitBase_pos (by omega)
        rw [a15Digit_eq_div_mod, Nat.div_eq_of_lt hlt, Nat.zero_mod,
          if_neg (by omega)]

/-- Adding two packed functions adds their digit functions. -/
theorem a15Pack_add (c d : ℕ → ℕ) (N : ℕ) :
    a15Pack c N + a15Pack d N = a15Pack (fun v => c v + d v) N := by
  unfold a15Pack
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

theorem a15Pack_shiftLeft_eq_mul (x s : ℕ) :
    x <<< (32 * s) = x * a15DigitBase ^ s := by
  rw [Nat.shiftLeft_eq, a15DigitBase_pow]

/-- Shifting a packed function left by `s` digits shifts its digit
function. -/
theorem a15Pack_shiftLeft (c : ℕ → ℕ) (s : ℕ) :
    ∀ N : ℕ, a15Pack c N <<< (32 * s) =
      a15Pack (fun v => if s ≤ v then c (v - s) else 0) (N + s) := by
  intro N
  induction N with
  | zero =>
      rw [a15Pack_zero, Nat.zero_shiftLeft, Nat.zero_add, a15Pack]
      refine (Finset.sum_eq_zero ?_).symm
      intro v hv
      rw [if_neg (by have := Finset.mem_range.mp hv; omega), Nat.zero_mul]
  | succ N ih =>
      have hstep : N + 1 + s = N + s + 1 := by omega
      calc a15Pack c (N + 1) <<< (32 * s)
          = a15Pack c N * a15DigitBase ^ s +
              c N * a15DigitBase ^ (N + s) := by
            rw [a15Pack_shiftLeft_eq_mul, a15Pack_succ, add_mul, pow_add]
            ring
        _ = a15Pack (fun v => if s ≤ v then c (v - s) else 0) (N + s) +
              c N * a15DigitBase ^ (N + s) := by
            rw [← a15Pack_shiftLeft_eq_mul, ih]
        _ = a15Pack (fun v => if s ≤ v then c (v - s) else 0) (N + 1 + s) := by
            rw [hstep, a15Pack_succ, if_pos (by omega)]
            congr 3
            omega

/-- The packed function concentrated on digit zero. -/
theorem a15Pack_delta (N : ℕ) (hN : 0 < N) :
    a15Pack (fun s => if s = 0 then 1 else 0) N = 1 := by
  rw [a15Pack, Finset.sum_eq_single 0]
  · simp
  · intro v _ hv
    rw [if_neg hv, Nat.zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hN) h

/-- Extending a packed function past its support does not change it. -/
theorem a15Pack_extend (c : ℕ → ℕ) (N : ℕ) :
    ∀ M : ℕ, (∀ v, N ≤ v → c v = 0) → N ≤ M → a15Pack c M = a15Pack c N := by
  intro M
  induction M with
  | zero => intro _ hM; simp [Nat.le_zero.mp hM]
  | succ M ih =>
      intro hzero hM
      rcases Nat.lt_or_ge N (M + 1) with h | h
      · rw [a15Pack_succ, hzero M (by omega), Nat.zero_mul, Nat.add_zero]
        exact ih hzero (by omega)
      · exact congrArg (a15Pack c) (by omega)

end SRG266
