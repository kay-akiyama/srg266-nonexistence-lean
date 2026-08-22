/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ConcreteEnumeration

/-!
# Interface for the concrete E7 profile expansion

The chunked certificates in
`SRG266.Certificates.E7ConcreteEnumerationProof` prove the exact expansion over
120,036 component profiles.
-/

namespace SRG266

structure E7ConcreteEnumerationAudit where
  expandedCount : ℕ
  listedCount : ℕ
  sameProfiles : Bool
  deriving DecidableEq

def e7ConcreteEnumerationAudit : E7ConcreteEnumerationAudit :=
  let expanded := e7ExpandedConcreteProfilePairs.toFinset
  let listed := e7ListedCanonicalArrayPairs.toFinset
  { expandedCount := expanded.card
    listedCount := listed.card
    sameProfiles := decide (expanded = listed) }

class E7ConcreteEnumerationAuditInput : Prop where
  audit_checked :
    e7ConcreteEnumerationAudit =
      { expandedCount := 956
        listedCount := 956
        sameProfiles := true }

theorem e7ConcreteEnumerationAudit_checked
    [E7ConcreteEnumerationAuditInput] :
    e7ConcreteEnumerationAudit =
      { expandedCount := 956
        listedCount := 956
        sameProfiles := true } :=
  E7ConcreteEnumerationAuditInput.audit_checked

end SRG266
