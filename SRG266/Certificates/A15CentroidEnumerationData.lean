/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15CentroidEnumeration

/-!
# Interface for the A15 canonical-enumeration audit

This module states the finite equality proved by the bounded subtree
certificates in `SRG266.Certificates.A15CentroidEnumerationProof`.
-/

namespace SRG266

class A15CentroidEnumerationInput : Prop where
  enumerated_eq_listed :
    a15EnumeratedCandidateProfiles.toFinset =
      a15ListedCandidateProfiles.toFinset

/-- The exact finite completeness statement supplied by the current input. -/
theorem a15EnumeratedCandidateProfiles_eq_listed
    [A15CentroidEnumerationInput] :
    a15EnumeratedCandidateProfiles.toFinset =
      a15ListedCandidateProfiles.toFinset :=
  A15CentroidEnumerationInput.enumerated_eq_listed

end SRG266
