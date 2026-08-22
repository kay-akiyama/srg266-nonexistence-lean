/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ScalarPairFilter
import SRG266.Hosts.E7CentroidKeyCodes
import SRG266.Hosts.E7EnumeratedKeySubset

/-!
# The trace-filtered scalar-feasible pairs are listed centroid pairs

This module assembles the inclusion recorded by `E7ScalarDPAuditInput` from
six finite checks:

* every enumerated component profile has a listed component key;
* every listed code sits in the bucket of its own squared norm;
* every trace-range eligible pair of listed codes is one of 421 candidates;
* 378 of those candidates are refuted by the scalar target equations;
* the remaining 43 are packed codes of listed centroid profile pairs;
* the listed centroid profiles have squared norms below `e7NormBase`.

The checks themselves are kernel evaluations, discharged in
`SRG266/Certificates/E7ComponentKeyCoverage.lean` and
`SRG266/Certificates/E7ScalarPairAudit.lean`.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem e7EnumeratedKey_eq_ofCode
    (hcoverage : ∀ profile ∈ e7EnumeratedComponentProfiles,
      e7ComponentKey profile ∈ e7ListedComponentKeys)
    (key : E7ComponentKey) (hkey : key ∈ e7EnumeratedComponentKeys) :
    ∃ code ∈ e7ListedKeyCodes, key = e7KeyOfCode code := by
  obtain ⟨profile, hprofile, hkeyEq⟩ := e7EnumeratedComponentKeys_subset key hkey
  have hlisted := hcoverage profile hprofile
  rw [e7ListedComponentKeys, List.mem_map] at hlisted
  obtain ⟨code, hcode, hcodeEq⟩ := hlisted
  exact ⟨code, hcode, by rw [← hkeyEq, ← hcodeEq]⟩

theorem e7Trace_subset_of_checks
    (hcoverage : ∀ profile ∈ e7EnumeratedComponentProfiles,
      e7ComponentKey profile ∈ e7ListedComponentKeys)
    (hbucket : e7CodeBucketOk = true)
    (hcheck : ∀ halfNorm, 19 ≤ halfNorm → halfNorm ≤ 131 →
      e7CandidatePairCheckAt halfNorm = true)
    (hrefuted : ∀ pair ∈ e7RefutedCodePairs,
      e7CodeScalarRefuted pair.1 pair.2 = true)
    (htraceListed : ∀ pair ∈ e7TraceCodePairs,
      pair ∈ e7ListedCentroidKeyCodePairs)
    (hcentroid : e7ListedCentroidCodeOk = true)
    (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7TraceFeasibleHistogramPairs) :
    pair ∈ e7ListedCentroidHistogramPairsUpToSwap := by
  obtain ⟨left, right⟩ := pair
  simp only [e7TraceFeasibleHistogramPairs, e7ScalarFeasibleHistogramPairs,
    e7EligibleHistogramPairs, List.mem_filter, decide_eq_true_eq] at hpair
  obtain ⟨⟨⟨hcomplementary, hcount⟩, hfeasible⟩, hlow, hhigh⟩ := hpair
  simp only [e7NormComplementaryHistogramPairs, List.mem_flatMap, List.mem_map,
    List.mem_range, mem_e7ComponentKeysAtNorm, Prod.mk.injEq] at hcomplementary
  obtain ⟨halfNorm, hhalf, leftKey, ⟨hleftMem, hleftNorm⟩, rightKey,
    ⟨hrightMem, hrightNorm⟩, hleftEq, hrightEq⟩ := hcomplementary
  subst hleftEq
  subst hrightEq
  obtain ⟨leftCode, hleftCode, hleftKeyEq⟩ :=
    e7EnumeratedKey_eq_ofCode hcoverage _ hleftMem
  obtain ⟨rightCode, hrightCode, hrightKeyEq⟩ :=
    e7EnumeratedKey_eq_ofCode hcoverage _ hrightMem
  subst hleftKeyEq
  subst hrightKeyEq
  rw [e7KeyOfCode_norm] at hleftNorm hrightNorm hlow hhigh
  rw [e7HistogramEligibleCount_ofCode] at hcount
  have hcandidate :=
    e7CandidateCodePair_of hbucket hcheck leftCode rightCode halfNorm
      hleftCode hrightCode hleftNorm hrightNorm hhalf hlow hhigh hcount
  rw [e7CandidateCodePairs, List.mem_append] at hcandidate
  rcases hcandidate with hmem | hmem
  · exfalso
    have := e7ScalarDPFeasible_eq_false_of_codeRefuted leftCode rightCode
      (hrefuted _ hmem)
    rw [this] at hfeasible
    exact Bool.noConfusion hfeasible
  · exact e7CentroidPair_mem_listed hcentroid leftCode rightCode
      (htraceListed _ hmem)

end SRG266
