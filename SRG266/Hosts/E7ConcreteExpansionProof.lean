/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7ConcreteEnumerationData
import SRG266.Certificates.E7ConcreteExpansionChecks
import SRG266.Certificates.E7ConcreteCodeChecks
import SRG266.Certificates.E7ConcreteInclusionChecks
import SRG266.Certificates.E7ConcreteWitnessChecks

/-!
# The concrete E7 expansion equals the listed centroid pairs

This module assembles the concrete expansion audit from the filtering sweep
and the finite checks. Its input is

  `e7EnumeratedComponentProfiles.filter e7ConcreteRelevant =
    e7ConcreteRelevantProfiles`,

which `SRG266/Certificates/E7ConcreteFilterAssembly.lean` discharges by
kernel evaluation.  Everything below is bookkeeping around it:

* the relevance test recognises exactly the profiles carrying a listed
  component key (`e7ConcreteRelevant_of_key` and its converse);
* hence each of the 43 listed key filters of `e7KeyedComponentProfiles` is the
  corresponding listed fibre (`e7ConcreteKeyedFilter`);
* the listed histogram key pairs are exactly the decoded listed code pairs;
* the two resulting inclusions between `e7ExpandedConcreteProfilePairs` and
  `e7ListedCanonicalArrayPairs` are read off the packed encodings and the
  expansion witnesses.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- `List.filter` after `List.map` filters the source list. -/
theorem e7Filter_mapComp {α β : Type _} (l : List α) (f : α → β) (ok : β → Bool) :
    (l.map f).filter ok = (l.filter fun a => ok (f a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases hok : ok (f a)
      · simp [hok, ih]
      · simp [hok, ih]

/-! ### The relevance test -/

/-- A relevant profile has eight coordinates. -/
theorem e7ConcreteRelevant_size (profile : Array ℤ)
    (hprofile : e7ConcreteRelevant profile = true) : profile.size = 8 := by
  simp only [e7ConcreteRelevant, Bool.and_eq_true, decide_eq_true_eq] at hprofile
  exact hprofile.1.1

/-- A relevant profile has a small squared norm. -/
theorem e7ConcreteRelevant_normLt (profile : Array ℤ)
    (hprofile : e7ConcreteRelevant profile = true) :
    e7FastNorm profile < e7NormBase := by
  simp only [e7ConcreteRelevant, Bool.and_eq_true, decide_eq_true_eq] at hprofile
  exact e7ConcreteNormTree_lt _
    (E7CodeTree.mem_toList_of_contains _ _ hprofile.1.2)

/-- A relevant profile carries a listed component code. -/
theorem e7ConcreteRelevant_code (profile : Array ℤ)
    (hprofile : e7ConcreteRelevant profile = true) :
    e7FastComponentCode profile ∈ e7ConcreteKeyCodes := by
  simp only [e7ConcreteRelevant, Bool.and_eq_true, decide_eq_true_eq] at hprofile
  have := E7CodeTree.mem_toList_of_contains _ _ hprofile.2
  rwa [e7ConcreteKeyCodeTree_toList] at this

/-- A relevant profile carries the key of its packed code. -/
theorem e7ConcreteRelevant_key (profile : Array ℤ)
    (hprofile : e7ConcreteRelevant profile = true) :
    e7ComponentKey profile = e7KeyOfCode (e7FastComponentCode profile) :=
  e7ComponentKey_eq_ofCode profile (e7ConcreteRelevant_size profile hprofile)
    (e7ConcreteRelevant_normLt profile hprofile)

/-- An eight-coordinate profile carrying a listed key is relevant. -/
theorem e7ConcreteRelevant_of_key (profile : Array ℤ) (hsize : profile.size = 8)
    (code : ℕ) (hcode : code ∈ e7ConcreteKeyCodes)
    (hkey : e7ComponentKey profile = e7KeyOfCode code) :
    e7ConcreteRelevant profile = true := by
  have hnorm : e7FastNorm profile = code % e7NormBase := by
    rw [← e7ComponentNorm_eq_fast profile hsize]
    exact congrArg E7ComponentKey.norm hkey
  have hlt : e7FastNorm profile < e7NormBase := by
    rw [hnorm]; exact Nat.mod_lt _ e7NormBase_pos
  have hcodeEq : e7FastComponentCode profile = code :=
    (e7ComponentKey_eq_code_iff profile hsize hlt code
      (e7ConcreteKeyCodes_lt code hcode)).mp hkey
  simp only [e7ConcreteRelevant, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hsize, ?_⟩, ?_⟩
  · rw [hnorm]; exact e7ConcreteNormTree_contains code hcode
  · rw [hcodeEq]; exact e7ConcreteKeyCodeTree_contains code hcode

/-! ### Fibres -/

/-- The listed fibre table computes the fibre of every listed code. -/
theorem e7ConcreteFibreOf_eq (code : ℕ) (hcode : code ∈ e7ConcreteKeyCodes) :
    e7ConcreteFibreOf code = e7ConcreteFibre code := by
  have hsome := e7ConcreteFibreTable_isSome code hcode
  cases hfind : e7ConcreteFibreTable.find? fun entry => decide (entry.1 = code) with
  | none => rw [hfind] at hsome; exact absurd hsome (by simp)
  | some entry =>
      have hmem := List.mem_of_find?_eq_some hfind
      have heq := List.find?_some hfind
      simp only [decide_eq_true_eq] at heq
      simp only [e7ConcreteFibreOf, hfind]
      rw [← heq]
      exact (e7ConcreteFibreTable_checked entry hmem).symm

section Filtered

variable (hfilter :
  e7EnumeratedComponentProfiles.filter e7ConcreteRelevant =
    e7ConcreteRelevantProfiles)

include hfilter

/-- Every surviving profile is enumerated and relevant. -/
theorem e7ConcreteRelevantProfiles_mem (profile : Array ℤ)
    (hprofile : profile ∈ e7ConcreteRelevantProfiles) :
    profile ∈ e7EnumeratedComponentProfiles ∧ e7ConcreteRelevant profile = true := by
  rw [← hfilter, List.mem_filter] at hprofile
  exact hprofile

/-- Every profile in a fibre is enumerated and carries the decoded key. -/
theorem e7ConcreteFibre_mem (code : ℕ) (profile : Array ℤ)
    (hprofile : profile ∈ e7ConcreteFibre code) :
    profile ∈ e7EnumeratedComponentProfiles ∧
      e7ComponentKey profile = e7KeyOfCode code := by
  rw [e7ConcreteFibre, List.mem_filter, decide_eq_true_eq] at hprofile
  obtain ⟨hmem, hcode⟩ := hprofile
  obtain ⟨henum, hrel⟩ := e7ConcreteRelevantProfiles_mem hfilter profile hmem
  exact ⟨henum, by rw [e7ConcreteRelevant_key profile hrel, hcode]⟩

/-- The listed key filter of the keyed profiles is the listed fibre. -/
theorem e7ConcreteKeyedFilter (code : ℕ) (hcode : code ∈ e7ConcreteKeyCodes) :
    (e7KeyedComponentProfiles.filter fun item => item.1 = e7KeyOfCode code) =
      (e7ConcreteFibre code).map fun profile => (e7KeyOfCode code, profile) := by
  have hkeyed :
      (e7KeyedComponentProfiles.filter fun item => item.1 = e7KeyOfCode code) =
        (e7EnumeratedComponentProfiles.filter fun profile =>
            decide (e7ComponentKey profile = e7KeyOfCode code)).map
          fun profile => (e7ComponentKey profile, profile) := by
    simp only [e7KeyedComponentProfiles, e7Filter_mapComp]
  have hrestrict :
      (e7EnumeratedComponentProfiles.filter fun profile =>
          decide (e7ComponentKey profile = e7KeyOfCode code)) =
        e7ConcreteRelevantProfiles.filter fun profile =>
          decide (e7ComponentKey profile = e7KeyOfCode code) := by
    rw [← hfilter, List.filter_filter]
    refine List.filter_congr ?_
    intro profile hprofile
    by_cases hkey : e7ComponentKey profile = e7KeyOfCode code
    · have hrel := e7ConcreteRelevant_of_key profile
        (e7EnumeratedComponentProfiles_size profile hprofile) code hcode hkey
      simp [hkey, hrel]
    · simp [hkey]
  have hcodeFilter :
      (e7ConcreteRelevantProfiles.filter fun profile =>
          decide (e7ComponentKey profile = e7KeyOfCode code)) =
        e7ConcreteFibre code := by
    refine List.filter_congr ?_
    intro profile hprofile
    obtain ⟨_, hrel⟩ := e7ConcreteRelevantProfiles_mem hfilter profile hprofile
    rw [decide_eq_decide]
    exact e7ComponentKey_eq_code_iff profile (e7ConcreteRelevant_size profile hrel)
      (e7ConcreteRelevant_normLt profile hrel) code (e7ConcreteKeyCodes_lt code hcode)
  rw [hkeyed, hrestrict, hcodeFilter]
  refine List.map_congr_left ?_
  intro profile hprofile
  rw [(e7ConcreteFibre_mem hfilter code profile hprofile).2]

/-- The inner expansion of one listed key pair is the product of its two
listed fibres. -/
theorem e7ConcreteInner (left right : ℕ)
    (hleft : left ∈ e7ConcreteKeyCodes) (hright : right ∈ e7ConcreteKeyCodes) :
    ((e7KeyedComponentProfiles.filter fun item => item.1 = e7KeyOfCode left).flatMap
        fun l =>
          (e7KeyedComponentProfiles.filter fun item => item.1 = e7KeyOfCode right).map
            fun r => e7CanonicalComponentArrayPair l.2 r.2) =
      (e7ConcreteFibre left).flatMap fun a =>
        (e7ConcreteFibre right).map fun b => e7CanonicalComponentArrayPair a b := by
  rw [e7ConcreteKeyedFilter hfilter left hleft, e7ConcreteKeyedFilter hfilter right hright]
  simp only [List.flatMap_map, List.map_map, Function.comp_def]

end Filtered

/-! ### The listed histogram key pairs -/

/-- Every listed histogram key pair decodes one listed code pair. -/
theorem e7ListedPair_mem_concrete (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7ListedCentroidHistogramPairsUpToSwap) :
    ∃ codes ∈ e7ConcreteCodePairs,
      pair = (e7KeyOfCode codes.1, e7KeyOfCode codes.2) := by
  have hmem := e7DedupAdjacent_subset _ _ hpair
  rw [List.mem_mergeSort, List.mem_flatMap] at hmem
  obtain ⟨profile, hprofile, hcases⟩ := hmem
  have hok := (List.all_eq_true.mp e7ListedCentroidCodeOk_checked) profile hprofile
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hleft : e7ComponentKey (Array.ofFn profile.1) =
      e7KeyOfCode (e7FastComponentCode (Array.ofFn profile.1)) :=
    e7ComponentKey_eq_ofCode _ (by simp) hok.1
  have hright : e7ComponentKey (Array.ofFn profile.2) =
      e7KeyOfCode (e7FastComponentCode (Array.ofFn profile.2)) :=
    e7ComponentKey_eq_ofCode _ (by simp) hok.2
  have hforward : (e7FastComponentCode (Array.ofFn profile.1),
      e7FastComponentCode (Array.ofFn profile.2)) ∈ e7ListedCentroidKeyCodePairs := by
    simp only [e7ListedCentroidKeyCodePairs, List.mem_flatMap]
    exact ⟨profile, hprofile, by simp⟩
  have hbackward : (e7FastComponentCode (Array.ofFn profile.2),
      e7FastComponentCode (Array.ofFn profile.1)) ∈ e7ListedCentroidKeyCodePairs := by
    simp only [e7ListedCentroidKeyCodePairs, List.mem_flatMap]
    exact ⟨profile, hprofile, by simp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcases
  rcases hcases with rfl | rfl
  · exact ⟨_, e7CentroidKeyCodePairs_mem_concrete _ hforward, by rw [hleft, hright]⟩
  · exact ⟨_, e7CentroidKeyCodePairs_mem_concrete _ hbackward, by rw [hleft, hright]⟩

/-- Every listed code pair decodes a listed histogram key pair. -/
theorem e7ConcretePair_mem_listed (codes : ℕ × ℕ)
    (hcodes : codes ∈ e7ConcreteCodePairs) :
    (e7KeyOfCode codes.1, e7KeyOfCode codes.2) ∈
      e7ListedCentroidHistogramPairsUpToSwap :=
  e7CentroidPair_mem_listed e7ListedCentroidCodeOk_checked _ _
    (e7ConcreteCodePairs_mem_centroid _ hcodes)

/-! ### The two inclusions -/

section Filtered

variable (hfilter :
  e7EnumeratedComponentProfiles.filter e7ConcreteRelevant =
    e7ConcreteRelevantProfiles)

include hfilter

/-- The native expansion is contained in the listed expansion. -/
theorem e7Expanded_subset_concrete :
    ∀ pair ∈ e7ExpandedConcreteProfilePairs, pair ∈ e7ConcreteExpansion := by
  intro pair hpair
  simp only [e7ExpandedConcreteProfilePairs] at hpair
  rw [List.mem_flatMap] at hpair
  obtain ⟨keys, hkeys, hpair⟩ := hpair
  obtain ⟨codes, hcodes, rfl⟩ := e7ListedPair_mem_concrete keys hkeys
  dsimp only at hpair
  have hleft := (e7ConcreteCodePairs_codes _ hcodes).1
  have hright := (e7ConcreteCodePairs_codes _ hcodes).2
  rw [e7ConcreteInner hfilter codes.1 codes.2 hleft hright] at hpair
  simp only [e7ConcreteExpansion, List.mem_flatMap]
  refine ⟨codes, hcodes, ?_⟩
  rw [e7ConcreteFibreOf_eq _ hleft, e7ConcreteFibreOf_eq _ hright]
  rw [List.mem_flatMap] at hpair
  exact hpair

/-- The listed canonical pairs occur in the native expansion. -/
theorem e7Listed_subset_expanded :
    ∀ pair ∈ e7ListedCanonicalArrayPairs, pair ∈ e7ExpandedConcreteProfilePairs := by
  intro pair hpair
  rw [e7ConcreteWitnesses_pairs, List.mem_map] at hpair
  obtain ⟨witness, hwitness, rfl⟩ := hpair
  have hcheck := (List.all_eq_true.mp e7ConcreteWitnesses_fibres) witness hwitness
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hpair, hleft⟩, hright⟩ := hcheck
  have hcodeLeft := (e7ConcreteCodePairs_codes _ hpair).1
  have hcodeRight := (e7ConcreteCodePairs_codes _ hpair).2
  rw [e7ConcreteFibreOf_eq _ hcodeLeft] at hleft
  rw [e7ConcreteFibreOf_eq _ hcodeRight] at hright
  obtain ⟨hmemLeft, hkeyLeft⟩ := e7ConcreteFibre_mem hfilter _ _ hleft
  obtain ⟨hmemRight, hkeyRight⟩ := e7ConcreteFibre_mem hfilter _ _ hright
  refine canonical_pair_mem_expansion _ _ hmemLeft hmemRight ?_
  rw [hkeyLeft, hkeyRight]
  exact e7ConcretePair_mem_listed witness.1 hpair

/-- The native expansion is contained in the listed canonical pairs. -/
theorem e7Expanded_subset_listed :
    ∀ pair ∈ e7ExpandedConcreteProfilePairs, pair ∈ e7ListedCanonicalArrayPairs := by
  have hround := List.all_eq_true.mp e7ConcreteListed_roundTrip
  simp only [decide_eq_true_eq] at hround
  have hlength : e7ConcreteListedCodeList.length = 956 := by
    rw [← e7ConcreteListedCodes_eq, e7ConcreteListedCodes, List.length_map,
      e7ListedCanonicalArrayPairs_length]
  have hnodup : e7ConcreteListedCodeList.Nodup :=
    e7NatDistinct_nodup _ e7ConcreteListedCodeList_distinct
  have hsetEq :
      e7ConcreteListedCodeList.toFinset = e7ConcreteListedCodeTree.toList.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro code hcode
      rw [List.mem_toFinset] at hcode ⊢
      exact E7CodeTree.mem_toList_of_contains _ _
        ((List.all_eq_true.mp e7ConcreteListedCodeList_mem_tree) code hcode)
    · have hle : e7ConcreteListedCodeTree.toList.toFinset.card ≤ 956 := by
        calc e7ConcreteListedCodeTree.toList.toFinset.card
            ≤ e7ConcreteListedCodeTree.toList.length := List.toFinset_card_le _
          _ = 956 := e7ConcreteListedCodeTree_length
      have heq : e7ConcreteListedCodeList.toFinset.card = 956 := by
        rw [List.toFinset_card_of_nodup hnodup, hlength]
      omega
  intro pair hpair
  have hexp := e7Expanded_subset_concrete hfilter pair hpair
  have hcheck := (List.all_eq_true.mp e7ConcreteExpansion_checked) pair hexp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hmemTree : e7PairEncode pair ∈ e7ConcreteListedCodeTree.toList :=
    E7CodeTree.mem_toList_of_contains _ _ hcheck.1
  have hmemList : e7PairEncode pair ∈ e7ConcreteListedCodeList := by
    rw [← List.mem_toFinset, hsetEq, List.mem_toFinset]
    exact hmemTree
  rw [← e7ConcreteListedCodes_eq] at hmemList
  exact e7Pair_mem_of_code_mem _ hround pair hcheck.2 hmemList

/-- The concrete expansion audit. -/
theorem e7ConcreteEnumerationAudit_of_filter :
    e7ConcreteEnumerationAudit =
      { expandedCount := 956, listedCount := 956, sameProfiles := true } := by
  have hfin :
      e7ExpandedConcreteProfilePairs.toFinset = e7ListedCanonicalArrayPairs.toFinset := by
    ext pair
    simp only [List.mem_toFinset]
    exact ⟨fun h => e7Expanded_subset_listed hfilter pair h,
      fun h => e7Listed_subset_expanded hfilter pair h⟩
  have hnodup : e7ListedCanonicalArrayPairs.Nodup := by
    refine List.Nodup.of_map e7PairEncode ?_
    rw [show e7ListedCanonicalArrayPairs.map e7PairEncode = e7ConcreteListedCodeList from
      e7ConcreteListedCodes_eq]
    exact e7NatDistinct_nodup _ e7ConcreteListedCodeList_distinct
  have hcard : e7ListedCanonicalArrayPairs.toFinset.card = 956 := by
    rw [List.toFinset_card_of_nodup hnodup, e7ListedCanonicalArrayPairs_length]
  simp only [e7ConcreteEnumerationAudit, hfin, hcard, decide_true]

end Filtered

end SRG266
