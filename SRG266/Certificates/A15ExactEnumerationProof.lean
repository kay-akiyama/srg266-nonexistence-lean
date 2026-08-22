/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15ExactEnumerationData
import SRG266.Hosts.A15ExactEnumerationCongruence

/-!
# Kernel proof of the reference/fast A15 enumeration comparison

`a15ExactEnumeratedCandidateProfiles_eq` identifies the two magnitude searches
outright, by structural induction on the magnitude parameter combined with
`a15_counters_agree`: the two eligible-shell counters answer the enumerator's
only question, `74 ≤ ·`, identically.

The resulting instance supplies `A15ExactEnumerationInput`.
-/

namespace SRG266

/-- The reference and fast A15 centroid searches retain exactly the same
canonical profiles. -/
theorem a15ExactEnumeratedCandidateProfiles_toFinset_eq :
    a15ExactEnumeratedCandidateProfiles.toFinset =
      a15EnumeratedCandidateProfiles.toFinset :=
  congrArg List.toFinset a15ExactEnumeratedCandidateProfiles_eq

instance : A15ExactEnumerationInput :=
  ⟨a15ExactEnumeratedCandidateProfiles_toFinset_eq⟩

end SRG266
