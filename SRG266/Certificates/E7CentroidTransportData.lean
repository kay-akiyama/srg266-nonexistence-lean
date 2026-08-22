/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7CentroidTransport

/-!
# Evaluated E7 centroid-to-residual transport audit

For all 54 survivor records Lean checks, over the complete 3,136-element
paired minuscule shell, that certificate-scale eligibility is exactly
residual eligibility after coordinatewise division by five.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem e7GeneratedSurvivorCentroidTransportValid :
    e7GeneratedSurvivorOrbitCertificates.all
      E7SurvivorOrbitCertificate.centroidTransportValid = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have htransport :=
    (List.all_eq_true.mp
      e7GeneratedSurvivorOrbitCertificates_transport_checked) c hc
  have hparts := c.transportCheck_parts htransport
  have hcheck := of_decide_eq_true (by
    simpa only [E7SurvivorOrbitCertificate.check] using hparts.1)
  have hfactor := of_decide_eq_true
    ((List.all_eq_true.mp
      e7GeneratedSurvivorOrbitCertificates_factorAudit) c hc)
  exact c.centroidTransportValid_of_factor_audit
    hcheck.1 hcheck.2.1 hfactor.1 hfactor.2

end SRG266
