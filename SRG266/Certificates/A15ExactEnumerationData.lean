/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ExactEnumeration
import SRG266.Certificates.A15CentroidEnumerationData

/-!
# External comparison interface for the reference and fast A15 enumerators

The reference search counts the declarative eligible finite subtype at every
terminal norm profile. This module states its equality with the fast search.
-/

namespace SRG266

class A15ExactEnumerationInput : Prop where
  exact_eq_fast :
    a15ExactEnumeratedCandidateProfiles.toFinset =
      a15EnumeratedCandidateProfiles.toFinset

/-- The declarative finite-subtype count and fast pair histogram retain
exactly the same canonical centroid profiles. -/
theorem a15ExactEnumeratedCandidateProfiles_eq_fast
    [A15ExactEnumerationInput] :
    a15ExactEnumeratedCandidateProfiles.toFinset =
      a15EnumeratedCandidateProfiles.toFinset :=
  A15ExactEnumerationInput.exact_eq_fast

end SRG266
