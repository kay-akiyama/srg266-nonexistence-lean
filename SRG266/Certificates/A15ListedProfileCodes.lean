/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15SortedProfileCodes

/-!
# The listed A15 centroid profiles, in code form

Half of `A15CentroidEnumerationInput`.  Two kernel evaluations are recorded:
the 2,212 profiles that already carry separators or survivor records are
codable -- sixteen coordinates, each in `[-70, 70]`, so
`SRG266.a15ProfileCode_injective` applies to them -- and their base-141 codes
sort to `a15SortedProfileCodes`.

Both are checked with `decide +kernel`. The other half of the input is
`SRG266.Certificates.A15EnumeratedProfileCodes`; the two meet at
`a15SortedProfileCodes` and nowhere else.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- Every listed profile is a codable one. -/
theorem a15ListedCandidateProfiles_codable :
    ∀ profile ∈ a15ListedCandidateProfiles,
      a15CodableProfile profile = true := by
  decide +kernel

/-- The listed profiles carry exactly the sorted codes. -/
theorem a15ListedCandidateProfiles_sortedCodes :
    a15SortCodes (a15ListedCandidateProfiles.map a15ProfileCode) =
      a15SortedProfileCodes := by
  decide +kernel

end SRG266
