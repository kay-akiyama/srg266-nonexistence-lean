/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentCode
import SRG266.Hosts.E7ScalarSearch

/-!
# Histogram arithmetic on packed component codes

Every listed component key is `e7KeyOfCode` applied to a literal natural
number, so its histogram bins are base-64 digits.  Reading a bin from the
decoded array costs a linear scan of a 43-element list; reading it as a digit
is one GMP division.  This module records the two rewrites that let the pair
filters and the scalar categories run entirely on codes.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- Histogram bin `index` of a packed histogram code. -/
def e7CodeDigit (code index : ℕ) : ℕ :=
  if index < 43 then code / e7CodeBase ^ index % e7CodeBase else 0

theorem e7HistogramOfCode_getD_eq (code index : ℕ) :
    (e7HistogramOfCode code).getD index 0 = e7CodeDigit code index := by
  unfold e7CodeDigit
  split
  · exact e7HistogramOfCode_getD code index (by assumption)
  · rename_i hindex
    simp only [e7HistogramOfCode, Array.getD, List.size_toArray,
      e7CodeDigits_length]
    rw [dif_neg hindex]

theorem e7KeyOfCode_norm (code : ℕ) :
    (e7KeyOfCode code).norm = code % e7NormBase := rfl

/-- The eligible paired-shell cardinality, read off two packed codes. -/
def e7CodeEligibleCount (leftCode rightCode : ℕ) : ℕ :=
  (List.range 43).foldl (fun total k =>
    total +
      e7CodeDigit (leftCode / e7NormBase) k *
        e7CodeDigit (rightCode / e7NormBase) (57 - k)) 0

theorem e7HistogramEligibleCount_ofCode (leftCode rightCode : ℕ) :
    e7HistogramEligibleCount (e7KeyOfCode leftCode) (e7KeyOfCode rightCode) =
      e7CodeEligibleCount leftCode rightCode := by
  simp only [e7HistogramEligibleCount, e7CodeEligibleCount, e7KeyOfCode,
    e7HistogramOfCode_getD_eq]

/-- The scalar dynamic-programming categories, read off two packed codes. -/
def e7CodeScalarCategories (leftCode rightCode : ℕ) : List (ℤ × ℕ) :=
  (List.range 43).map fun (k : ℕ) =>
    ((k : ℤ) - 21,
      3 * e7CodeDigit (leftCode / e7NormBase) k *
        e7CodeDigit (rightCode / e7NormBase) (57 - k))

theorem e7ScalarCategories_ofCode (leftCode rightCode : ℕ) :
    e7ScalarCategories (e7KeyOfCode leftCode) (e7KeyOfCode rightCode) =
      e7CodeScalarCategories leftCode rightCode := by
  simp only [e7ScalarCategories, e7CodeScalarCategories, e7KeyOfCode,
    e7HistogramOfCode_getD_eq]

/-- Refutation of one code pair, phrased so the kernel never leaves `ℕ`
arithmetic. -/
def e7CodeScalarRefuted (leftCode rightCode : ℕ) : Bool :=
  e7ScalarSearch (e7ScalarCompress (e7CodeScalarCategories leftCode rightCode))
    220 (11 * ((leftCode % e7NormBase : ℕ) : ℤ)) == false

theorem e7ScalarDPFeasible_eq_false_of_codeRefuted
    (leftCode rightCode : ℕ)
    (hrefuted : e7CodeScalarRefuted leftCode rightCode = true) :
    e7ScalarDPFeasible (e7KeyOfCode leftCode, e7KeyOfCode rightCode) = false := by
  apply e7ScalarDPFeasible_eq_false_of_search
  rw [e7ScalarCategories_ofCode, e7KeyOfCode_norm]
  simpa only [e7CodeScalarRefuted, beq_iff_eq] using hrefuted

end SRG266
