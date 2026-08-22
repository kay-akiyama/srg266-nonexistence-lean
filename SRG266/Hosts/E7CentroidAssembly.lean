/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7CentroidKernelAudit
import SRG266.Hosts.E7CentroidProfiles

/-!
# Assembly of the checked E7 centroid lists

This module connects direct certificate-scale shell realizations to all 902
Farkas rejections and all 54 Weyl-transported survivors.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A listed E7 survivor cannot carry a direct certificate-scale
realization. -/
theorem e7_generated_survivor_no_centroid_realization
    (hG : IsHypothetical G) (x : V)
    (c : E7SurvivorOrbitCertificate)
    (hc : c ∈ e7GeneratedSurvivorOrbitCertificates) :
    IsEmpty (E7CentroidShellGramRealization G x c.y₁ c.y₂) := by
  have htransport :
      c.transportCheck = true :=
    (List.all_eq_true.mp
      e7GeneratedSurvivorOrbitCertificates_transport_checked) c hc
  have hcentroid :
      c.centroidTransportValid = true :=
    (List.all_eq_true.mp
      e7GeneratedSurvivorCentroidTransportValid) c hc
  refine ⟨fun realization => ?_⟩
  have residual :=
    realization.toResidual G c htransport hcentroid
  exact
    (e7_generated_survivor_no_realization
      G hG x c hc).false residual

/-- No listed E7 centroid profile carries a direct realization. -/
theorem e7ListedCentroidProfile_no_realization
    (hG : IsHypothetical G) (x : V)
    (y₁ y₂ : Fin 8 → ℤ)
    (hlisted : (y₁, y₂) ∈ e7ListedCentroidProfiles) :
    IsEmpty (E7CentroidShellGramRealization G x y₁ y₂) := by
  rcases List.mem_append.mp hlisted with hrejected | hsurvivor
  · obtain ⟨certificate, hcertificate, hpairs⟩ :=
      List.mem_map.mp hrejected
    cases Prod.ext_iff.mp hpairs with
    | intro hleft hright =>
        simp only at hleft hright
        subst y₁
        subst y₂
        refine ⟨fun realization => ?_⟩
        exact
          (e7_generated_centroid_certificate_no_bounded_solution
            certificate hcertificate
            (realization.exists_centroid_bounded_solution G hG x)).elim
  · obtain ⟨certificate, hcertificate, hpairs⟩ :=
      List.mem_map.mp hsurvivor
    cases Prod.ext_iff.mp hpairs with
    | intro hleft hright =>
        simp only at hleft hright
        subst y₁
        subst y₂
        exact
          e7_generated_survivor_no_centroid_realization
            G hG x certificate hcertificate

end SRG266
