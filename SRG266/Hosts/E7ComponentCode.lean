/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7HistogramEnumeration

/-!
# Packed base-64 codes for E7 component keys

The 43-bin evaluation histogram of an E7 component profile stores 56 unit
increments in total, so every bin stays below 64.  Packing the bins as the
base-64 digits of a single natural number replaces array surgery by
GMP-accelerated arithmetic, which is what makes the kernel sweep over the
120,036 enumerated profiles affordable.

The listed component keys are therefore *defined* as decodings of literal
codes.  Recognising a profile then only needs the equation
`e7ComponentHistogram profile = e7HistogramOfCode (packed code)`; no
injectivity of the packing is required.
-/

namespace SRG266

/-- Base of the packed histogram code.  The 43 bins carry 56 increments in
total, so every bin stays below 64. -/
def e7CodeBase : ℕ := 64

/-- Base separating the squared norm from the packed histogram.  Component
squared norms are at most 300. -/
def e7NormBase : ℕ := 512

theorem e7NormBase_pos : 0 < e7NormBase := by
  simp [e7NormBase]

theorem e7CodeBase_pos : 0 < e7CodeBase := by
  simp [e7CodeBase]

/-- The `n` low base-`e7CodeBase` digits of `c`. -/
def e7CodeDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, c => c % e7CodeBase :: e7CodeDigits n (c / e7CodeBase)

theorem e7CodeDigits_length (n c : ℕ) : (e7CodeDigits n c).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [e7CodeDigits, ih]

theorem e7CodeDigits_getD (n : ℕ) :
    ∀ (c k : ℕ), k < n →
      (e7CodeDigits n c).getD k 0 = c / e7CodeBase ^ k % e7CodeBase := by
  induction n with
  | zero => intro c k hk; omega
  | succ n ih =>
      intro c k hk
      cases k with
      | zero => simp [e7CodeDigits]
      | succ k =>
          have hk' : k < n := by omega
          simp only [e7CodeDigits, List.getD_cons_succ, ih _ _ hk']
          rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem e7CodeDigits_zero (n : ℕ) : e7CodeDigits n 0 = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [e7CodeDigits, ih, List.replicate_succ, e7CodeBase]

/-- Contribution of one histogram increment at bin `i` to the packed code.
Bins outside `[0, 43)` contribute nothing, exactly matching the silent
out-of-bounds behaviour of `Array.set!`. -/
def e7BinWeight (i : ℕ) : ℕ := if i < 43 then e7CodeBase ^ i else 0

theorem e7CodeDigits_add_pow (n : ℕ) :
    ∀ (c i : ℕ), c / e7CodeBase ^ i % e7CodeBase + 1 < e7CodeBase →
      e7CodeDigits n (c + e7CodeBase ^ i) =
        (e7CodeDigits n c).set i ((e7CodeDigits n c).getD i 0 + 1) := by
  induction n with
  | zero => intro c i _; rfl
  | succ n ih =>
      intro c i hc
      cases i with
      | zero =>
          have hlow : c % e7CodeBase + 1 < e7CodeBase := by simpa using hc
          have hmod : (c + 1) % e7CodeBase = c % e7CodeBase + 1 := by
            simp only [e7CodeBase] at hlow ⊢; omega
          have hdiv : (c + 1) / e7CodeBase = c / e7CodeBase := by
            simp only [e7CodeBase] at hlow ⊢; omega
          simp [e7CodeDigits, hmod, hdiv]
      | succ i =>
          have hpow : e7CodeBase ^ (i + 1) = e7CodeBase * e7CodeBase ^ i := by
            rw [Nat.pow_succ]; ring
          have hmod :
              (c + e7CodeBase ^ (i + 1)) % e7CodeBase = c % e7CodeBase := by
            rw [hpow, Nat.add_mul_mod_self_left]
          have hdiv :
              (c + e7CodeBase ^ (i + 1)) / e7CodeBase =
                c / e7CodeBase + e7CodeBase ^ i := by
            rw [hpow, Nat.add_mul_div_left _ _ e7CodeBase_pos]
          have hdd :
              c / e7CodeBase ^ (i + 1) = c / e7CodeBase / e7CodeBase ^ i := by
            rw [Nat.div_div_eq_div_mul, hpow, Nat.mul_comm]
          have hc' :
              c / e7CodeBase / e7CodeBase ^ i % e7CodeBase + 1 < e7CodeBase := by
            rw [← hdd]; exact hc
          simp only [e7CodeDigits, hmod, hdiv, List.set_cons_succ,
            List.getD_cons_succ, ih _ _ hc']

theorem e7ListGetD_toArray (l : List ℕ) (k : ℕ) :
    (l.toArray).getD k 0 = l.getD k 0 := by
  simp only [Array.getD, List.getD]
  split
  · rename_i h
    simp only [List.size_toArray] at h
    simp [List.getElem?_eq_getElem h]
  · rename_i h
    simp only [List.size_toArray] at h
    simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-- One packed increment raises the addressed digit by one and leaves the
other digits alone. -/
theorem e7CodeDigit_add_binWeight_le (c i k : ℕ)
    (hc : c / e7CodeBase ^ i % e7CodeBase + 1 < e7CodeBase) :
    (c + e7BinWeight i) / e7CodeBase ^ k % e7CodeBase ≤
      c / e7CodeBase ^ k % e7CodeBase + 1 := by
  by_cases hi : i < 43
  · have hw : e7BinWeight i = e7CodeBase ^ i := by simp [e7BinWeight, hi]
    rw [hw]
    set n := i + k + 1 with hn
    have hkn : k < n := by omega
    have hin : i < n := by omega
    have hlen : (e7CodeDigits n c).length = n := e7CodeDigits_length n c
    have hlist := e7CodeDigits_add_pow n c i hc
    have hleft :
        (c + e7CodeBase ^ i) / e7CodeBase ^ k % e7CodeBase =
          ((e7CodeDigits n c).set i
            ((e7CodeDigits n c).getD i 0 + 1)).getD k 0 := by
      rw [← hlist, e7CodeDigits_getD n _ k hkn]
    rw [hleft]
    by_cases hki : k = i
    · subst hki
      have hset :
          ((e7CodeDigits n c).set k ((e7CodeDigits n c).getD k 0 + 1)).getD k 0 =
            (e7CodeDigits n c).getD k 0 + 1 := by
        show
          (((e7CodeDigits n c).set k ((e7CodeDigits n c).getD k 0 + 1))[k]?).getD 0
            = _
        rw [List.getElem?_set_self (by omega)]
        rfl
      rw [hset, e7CodeDigits_getD n c k hkn]
    · have hset :
          ((e7CodeDigits n c).set i ((e7CodeDigits n c).getD i 0 + 1)).getD k 0 =
            (e7CodeDigits n c).getD k 0 := by
        show
          (((e7CodeDigits n c).set i ((e7CodeDigits n c).getD i 0 + 1))[k]?).getD 0
            = _
        rw [List.getElem?_set_ne (by omega)]
        rfl
      rw [hset, e7CodeDigits_getD n c k hkn]
      omega
  · have hw : e7BinWeight i = 0 := by simp [e7BinWeight, hi]
    rw [hw, Nat.add_zero]
    omega

/-- The 43-bin histogram carried by a packed code. -/
def e7HistogramOfCode (c : ℕ) : Array ℕ := (e7CodeDigits 43 c).toArray

/-- The component key carried by a packed code: the squared norm is the
residue modulo `e7NormBase` and the histogram is the remaining quotient. -/
def e7KeyOfCode (v : ℕ) : E7ComponentKey where
  norm := v % e7NormBase
  histogram := e7HistogramOfCode (v / e7NormBase)

theorem e7HistogramOfCode_getD (c k : ℕ) (hk : k < 43) :
    (e7HistogramOfCode c).getD k 0 = c / e7CodeBase ^ k % e7CodeBase := by
  rw [← e7CodeDigits_getD 43 c k hk]
  exact e7ListGetD_toArray _ k

theorem e7HistogramOfCode_zero : e7HistogramOfCode 0 = Array.replicate 43 0 := by
  simp [e7HistogramOfCode, e7CodeDigits_zero, Array.replicate]

/-- One histogram increment, on both sides of the packing. -/
theorem e7HistogramOfCode_set (c i : ℕ)
    (hc : c / e7CodeBase ^ i % e7CodeBase + 1 < e7CodeBase) :
    (e7HistogramOfCode c).set! i ((e7HistogramOfCode c).getD i 0 + 1) =
      e7HistogramOfCode (c + e7BinWeight i) := by
  have hgetD : (e7HistogramOfCode c).getD i 0 = (e7CodeDigits 43 c).getD i 0 :=
    e7ListGetD_toArray _ i
  rw [hgetD]
  by_cases hi : i < 43
  · have hw : e7BinWeight i = e7CodeBase ^ i := by simp [e7BinWeight, hi]
    rw [hw]
    simp only [e7HistogramOfCode, e7CodeDigits_add_pow 43 c i hc]
    apply Array.ext'
    simp
  · have hw : e7BinWeight i = 0 := by simp [e7BinWeight, hi]
    rw [hw, Nat.add_zero]
    simp only [e7HistogramOfCode]
    apply Array.ext'
    simp only [Array.toList_set!]
    exact List.set_eq_of_length_le (by rw [e7CodeDigits_length]; omega)

/-- Folding unit increments into an array of bins and into a packed code
give the same histogram, as long as no digit can overflow. -/
theorem e7HistogramOfCode_foldl :
    ∀ (bins : List ℕ) (c : ℕ),
      (∀ k, c / e7CodeBase ^ k % e7CodeBase + bins.length < e7CodeBase) →
      bins.foldl
          (fun counts i => counts.set! i (counts.getD i 0 + 1))
          (e7HistogramOfCode c) =
        e7HistogramOfCode
          (bins.foldl (fun code i => code + e7BinWeight i) c) := by
  intro bins
  induction bins with
  | nil => intro c _; rfl
  | cons i bins ih =>
      intro c hbound
      have hci : c / e7CodeBase ^ i % e7CodeBase + 1 < e7CodeBase := by
        have := hbound i
        simp only [List.length_cons] at this
        omega
      have hstep := e7HistogramOfCode_set c i hci
      simp only [List.foldl_cons, hstep]
      apply ih
      intro k
      have hk := e7CodeDigit_add_binWeight_le c i k hci
      have := hbound k
      simp only [List.length_cons] at this
      omega

end SRG266
