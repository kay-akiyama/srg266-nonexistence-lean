/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7ScalarDPData
import SRG266.Hosts.E7FastComponentKey

/-!
# Packed codes of the listed centroid profile pairs

`e7ListedCentroidHistogramPairsUpToSwap` sorts and deduplicates the component
keys of the 956 checked centroid profile pairs, so it cannot be evaluated by
the kernel.  Membership in it only needs the pre-sorting list, and this module
phrases that list in packed codes so a candidate pair can be recognised with
`Nat` arithmetic.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Packed codes of the listed centroid profile pairs, in both factor orders. -/
def e7ListedCentroidKeyCodePairs : List (ℕ × ℕ) :=
  e7ListedCentroidProfiles.flatMap fun pair =>
    let codes :=
      (e7FastComponentCode (Array.ofFn pair.1),
        e7FastComponentCode (Array.ofFn pair.2))
    [codes, (codes.2, codes.1)]

/-- Every listed centroid profile has a squared norm below `e7NormBase`. -/
def e7ListedCentroidCodeOk : Bool :=
  e7ListedCentroidProfiles.all fun pair =>
    decide (e7FastNorm (Array.ofFn pair.1) < e7NormBase) &&
      decide (e7FastNorm (Array.ofFn pair.2) < e7NormBase)

theorem e7CentroidPair_mem_listed
    (hok : e7ListedCentroidCodeOk = true)
    (leftCode rightCode : ℕ)
    (hpair : (leftCode, rightCode) ∈ e7ListedCentroidKeyCodePairs) :
    (e7KeyOfCode leftCode, e7KeyOfCode rightCode) ∈
      e7ListedCentroidHistogramPairsUpToSwap := by
  apply e7DedupAdjacent_mem_of_mem
  rw [List.mem_mergeSort, List.mem_flatMap]
  simp only [e7ListedCentroidKeyCodePairs, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  obtain ⟨profile, hprofile, hcodes⟩ := hpair
  have hok' := (List.all_eq_true.mp hok) profile hprofile
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
  have hkeyLeft :
      e7ComponentKey (Array.ofFn profile.1) =
        e7KeyOfCode (e7FastComponentCode (Array.ofFn profile.1)) :=
    e7ComponentKey_eq_ofCode _ (by simp) hok'.1
  have hkeyRight :
      e7ComponentKey (Array.ofFn profile.2) =
        e7KeyOfCode (e7FastComponentCode (Array.ofFn profile.2)) :=
    e7ComponentKey_eq_ofCode _ (by simp) hok'.2
  refine ⟨profile, hprofile, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases hcodes with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨by rw [hkeyLeft, hleft], by rw [hkeyRight, hright]⟩
  · exact Or.inr ⟨by rw [hkeyRight, hleft], by rw [hkeyLeft, hright]⟩

end SRG266
