/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15SortedProfileCodes
import SRG266.Certificates.A15EnumerationBranch0
import SRG266.Certificates.A15EnumerationBranch2

/-!
# The enumerated A15 centroid profiles, in code form

The other half of `A15CentroidEnumerationInput`.  The two branch modules
identify the magnitude search with the explicit concatenation of the 731 chunk
certificates, so `a15EnumeratedProfileList` below is a literal list of 2,212
profiles independently of the search. This module checks that those
profiles are codable and that their base-141 codes sort to
`a15SortedProfileCodes`, the same literal the listed profiles sort to.

Everything here is `decide +kernel`.  The expensive part is not this module but
the 731 chunk modules underneath it; see
`scripts/build_a15_enumeration_chunks.py`.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- The profiles the magnitude search emits, as an explicit list. -/
def a15EnumeratedProfileList : List (Array ℤ) :=
  a15Branch0Profiles ++ a15Branch2Profiles

/-- The explicit list is what the search emits.  No search is evaluated here:
the two branch theorems are simply concatenated. -/
theorem a15EnumeratedCandidateProfiles_eq_list :
    a15EnumeratedCandidateProfiles = a15EnumeratedProfileList := by
  rw [← a15PolyEnumeratedCandidateProfiles_eq,
    a15PolyEnumeratedCandidateProfiles, a15EnumeratedProfileList,
    a15Branch0_eq, a15Branch2_eq]

/-- Every enumerated profile is a codable one. -/
theorem a15EnumeratedProfileList_codable :
    ∀ profile ∈ a15EnumeratedProfileList,
      a15CodableProfile profile = true := by
  decide +kernel

/-- The enumerated profiles carry exactly the sorted codes. -/
theorem a15EnumeratedProfileList_sortedCodes :
    a15SortCodes (a15EnumeratedProfileList.map a15ProfileCode) =
      a15SortedProfileCodes := by
  decide +kernel

end SRG266
