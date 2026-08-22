/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ConcreteFilterAssembly
import SRG266.Hosts.E7ConcreteExpansionProof

/-!
# The concrete E7 enumeration audit, kernel-checked

The filtering sweep of
`SRG266/Certificates/E7ConcreteFilterAssembly.lean` identifies the 335
enumerated profiles carrying one of the 37 listed component keys, and
`SRG266/Hosts/E7ConcreteExpansionProof.lean` turns that into the audit.

Every finite step is checked with `decide +kernel`.
-/

namespace SRG266

/-- The concrete expansion audit, established by kernel evaluation. -/
theorem e7ConcreteEnumerationAudit_kernel :
    e7ConcreteEnumerationAudit =
      { expandedCount := 956, listedCount := 956, sameProfiles := true } :=
  e7ConcreteEnumerationAudit_of_filter e7ConcreteRelevantProfiles_checked

instance instE7ConcreteEnumerationAuditInput : E7ConcreteEnumerationAuditInput :=
  ⟨e7ConcreteEnumerationAudit_kernel⟩

end SRG266
