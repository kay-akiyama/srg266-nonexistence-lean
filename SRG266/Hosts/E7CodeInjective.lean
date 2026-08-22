/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7FastComponentKey

/-!
# The packed component code is determined by the component key

`e7ComponentKey_eq_ofCode` recovers a component key from its packed code.  The
concrete expansion needs the converse direction as well: a filter for the
profiles carrying one *listed* key must be recognised by comparing packed
codes, so equal keys have to force equal codes.

Both facts are elementary once the packing is known to be a base-`64` digit
expansion below `64 ^ 43`, which is what this module establishes:

* `e7CodeDigits_inj` — bounded naturals are determined by their digits;
* `e7FastComponentCode_lt` — the packed code of an eight-coordinate profile
  with squared norm below `e7NormBase` stays below `e7NormBase * 64 ^ 43`;
* `e7ComponentKey_eq_code_iff` — the bridge used by the filtering sweep.
-/

namespace SRG266

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- A bounded natural number is determined by its base-`e7CodeBase` digits. -/
theorem e7CodeDigits_inj :
    ∀ (n a b : ℕ), a < e7CodeBase ^ n → b < e7CodeBase ^ n →
      e7CodeDigits n a = e7CodeDigits n b → a = b := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb _
      simp only [pow_zero] at ha hb
      omega
  | succ n ih =>
      intro a b ha hb hdigits
      simp only [e7CodeDigits, List.cons.injEq] at hdigits
      have hbase : (0 : ℕ) < e7CodeBase := e7CodeBase_pos
      have ha' : a / e7CodeBase < e7CodeBase ^ n :=
        (Nat.div_lt_iff_lt_mul hbase).mpr (by rw [pow_succ] at ha; exact ha)
      have hb' : b / e7CodeBase < e7CodeBase ^ n :=
        (Nat.div_lt_iff_lt_mul hbase).mpr (by rw [pow_succ] at hb; exact hb)
      have hdiv := ih _ _ ha' hb' hdigits.2
      have hmod := hdigits.1
      simp only [e7CodeBase] at hdiv hmod
      omega

/-- Bounded packed codes are determined by the key they decode to. -/
theorem e7KeyOfCode_inj (v w : ℕ)
    (hv : v < e7NormBase * e7CodeBase ^ 43)
    (hw : w < e7NormBase * e7CodeBase ^ 43)
    (hkey : e7KeyOfCode v = e7KeyOfCode w) : v = w := by
  simp only [e7KeyOfCode, E7ComponentKey.mk.injEq] at hkey
  obtain ⟨hnorm, hhist⟩ := hkey
  have hdigits : e7CodeDigits 43 (v / e7NormBase) = e7CodeDigits 43 (w / e7NormBase) := by
    have := congrArg Array.toList hhist
    simpa only [e7HistogramOfCode, List.toList_toArray] using this
  have hbase : (0 : ℕ) < e7NormBase := e7NormBase_pos
  have hv' : v / e7NormBase < e7CodeBase ^ 43 :=
    (Nat.div_lt_iff_lt_mul hbase).mpr (by rw [Nat.mul_comm] at hv; exact hv)
  have hw' : w / e7NormBase < e7CodeBase ^ 43 :=
    (Nat.div_lt_iff_lt_mul hbase).mpr (by rw [Nat.mul_comm] at hw; exact hw)
  have hdiv := e7CodeDigits_inj 43 _ _ hv' hw' hdigits
  simp only [e7NormBase] at hnorm hdiv
  omega

/-- Every packed bin weight stays below the top digit. -/
theorem e7BinWeight_le (i : ℕ) : e7BinWeight i ≤ e7CodeBase ^ 42 := by
  simp only [e7BinWeight]
  split
  · exact Nat.pow_le_pow_right (by simp [e7CodeBase]) (by omega)
  · exact Nat.zero_le _

/-- Every packed pair contribution stays below twice the top digit. -/
theorem e7PairCode_le (d : ℤ) : e7PairCode d ≤ 2 * e7CodeBase ^ 42 := by
  have h1 := e7BinWeight_le (e7BinOfDiff d)
  have h2 := e7BinWeight_le (e7BinOfDiff (-d))
  simp only [e7PairCode]
  omega

/-- The packed histogram of any profile is a proper base-`64` expansion. -/
theorem e7PairCodeSum_lt (profile : Array ℤ) :
    e7PairCodeSum profile < e7CodeBase ^ 43 := by
  have hle : e7PairCodeSum profile ≤ 28 * (2 * e7CodeBase ^ 42) := by
    simp only [e7PairCodeSum]
    calc
      (e7Pairs.map fun q =>
          e7PairCode (4 * (e7ComponentEnumerationProfile profile q.1 +
              e7ComponentEnumerationProfile profile q.2) -
            ∑ k, e7ComponentEnumerationProfile profile k)).sum
          ≤ (e7Pairs.map fun _ => 2 * e7CodeBase ^ 42).sum :=
        List.sum_le_sum (fun _ _ => e7PairCode_le _)
      _ = 28 * (2 * e7CodeBase ^ 42) := by
        simp only [List.map_const', List.sum_replicate, smul_eq_mul]
        rfl
  have hpos : 0 < e7CodeBase ^ 42 := Nat.pow_pos (by simp [e7CodeBase])
  have hsucc : e7CodeBase ^ 43 = e7CodeBase ^ 42 * e7CodeBase := pow_succ _ _
  simp only [e7CodeBase] at hsucc hle hpos ⊢
  omega

/-- The packed code of an eight-coordinate profile of small squared norm is a
proper base-`64` expansion above the squared norm. -/
theorem e7FastComponentCode_lt (profile : Array ℤ) (hsize : profile.size = 8)
    (hnorm : e7FastNorm profile < e7NormBase) :
    e7FastComponentCode profile < e7NormBase * e7CodeBase ^ 43 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := e7Profile_eq_toArray profile hsize
  have hhist :
      e7FastHistogramCodeOf a0 a1 a2 a3 a4 a5 a6 a7 < e7CodeBase ^ 43 := by
    have := e7PairCodeSum_lt ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray
    rwa [e7PairCodeSum_eq_of_coordinates] at this
  have hnorm' : e7FastNormOf a0 a1 a2 a3 a4 a5 a6 a7 < e7NormBase := by
    simpa only [e7FastNorm, List.toList_toArray] using hnorm
  simp only [e7FastComponentCode, e7FastComponentCodeOf]
  simp only [e7NormBase] at hnorm' ⊢
  omega

/-- The filtering bridge: for an eight-coordinate profile of small squared
norm, carrying the key of a bounded code is the same as carrying that code. -/
theorem e7ComponentKey_eq_code_iff (profile : Array ℤ) (hsize : profile.size = 8)
    (hnorm : e7FastNorm profile < e7NormBase) (code : ℕ)
    (hcode : code < e7NormBase * e7CodeBase ^ 43) :
    (e7ComponentKey profile = e7KeyOfCode code) ↔
      (e7FastComponentCode profile = code) := by
  rw [e7ComponentKey_eq_ofCode profile hsize hnorm]
  constructor
  · intro hkey
    exact e7KeyOfCode_inj _ _ (e7FastComponentCode_lt profile hsize hnorm) hcode hkey
  · intro hcodeEq
    rw [hcodeEq]

end SRG266
