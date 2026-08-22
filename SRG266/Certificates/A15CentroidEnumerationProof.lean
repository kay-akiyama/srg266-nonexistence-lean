/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15CentroidEnumerationData
import SRG266.Certificates.A15ListedProfileCodes
import SRG266.Certificates.A15EnumeratedProfileCodes

/-!
# `A15CentroidEnumerationInput`, discharged by the kernel

The input asks that the magnitude recursion of
`SRG266.Hosts.A15CentroidEnumeration` and the list of profiles that carry
separators or survivor records describe the same set of 2,212 profiles.  It is
assembled here from four kernel-checked facts and no assumption:

* the 731 chunk certificates under
  `SRG266/Certificates/A15EnumerationChunks/`, glued by 26 group modules and
  the two branch modules, identify the search with an explicit list -- this is
  `a15EnumeratedCandidateProfiles_eq_list`, and it is where the 1,796,107
  recursion nodes are actually evaluated;
* both lists consist of codable profiles;
* both lists have `a15SortedProfileCodes` as their sorted base-141 code list.

The last two feed `a15_toFinset_eq_of_sortedCodes_eq`, which needs only that
the sort permutes its input.
-/

namespace SRG266

/-- The magnitude search and the listed profiles describe the same set. -/
theorem a15EnumeratedCandidateProfiles_toFinset_eq_listed :
    a15EnumeratedCandidateProfiles.toFinset =
      a15ListedCandidateProfiles.toFinset := by
  rw [a15EnumeratedCandidateProfiles_eq_list]
  refine a15_toFinset_eq_of_sortedCodes_eq _ _
    a15EnumeratedProfileList_codable a15ListedCandidateProfiles_codable ?_
  rw [a15EnumeratedProfileList_sortedCodes,
    a15ListedCandidateProfiles_sortedCodes]

instance instA15CentroidEnumerationInput : A15CentroidEnumerationInput where
  enumerated_eq_listed := a15EnumeratedCandidateProfiles_toFinset_eq_listed

end SRG266
