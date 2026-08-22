/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7SurvivorCanonicalCount.TwoTen
import SRG266.Certificates.E7SurvivorCanonicalCount.FourEightGeneric
import SRG266.Certificates.E7SurvivorCanonicalCount.FourEightSpecial
import SRG266.Certificates.E7SurvivorCanonicalCount.SixGenericSixGeneric
import SRG266.Certificates.E7SurvivorCanonicalCount.SixGenericSixSpecial

namespace SRG266

theorem e7ResidualCanonicalEligibleCount_checked
    (kind : E7ResidualType) :
    e7ResidualCanonicalEligibleCount kind =
      e7ResidualExpectedEligibleCount kind := by
  cases kind with
  | twoTen => exact e7ResidualCanonicalEligibleCount_twoTen
  | fourEightGeneric =>
      exact e7ResidualCanonicalEligibleCount_fourEightGeneric
  | fourEightSpecial =>
      exact e7ResidualCanonicalEligibleCount_fourEightSpecial
  | sixGenericSixGeneric =>
      exact e7ResidualCanonicalEligibleCount_sixGenericSixGeneric
  | sixGenericSixSpecial =>
      exact e7ResidualCanonicalEligibleCount_sixGenericSixSpecial

/-- Reconstruct the original survivor checker from its reduced field,
one-factor, root, and canonical-cardinality audits. -/
theorem E7SurvivorOrbitCertificate.check_of_reduced_audits
    (c : E7SurvivorOrbitCertificate)
    (hcore : c.coreAudit = true)
    (hfactor : c.centroidTransportFactorAudit = true)
    (hroots : c.transportRootAudit = true) :
    c.check = true := by
  let canonical := e7ResidualCanonical c.residualType
  let target₁ := if c.swapFactors then canonical.2 else canonical.1
  let target₂ := if c.swapFactors then canonical.1 else canonical.2
  let d₁ := fun i => c.y₁ i / 5
  let d₂ := fun i => c.y₂ i / 5
  have hcore' :
      (∀ i, c.y₁ i % 5 = 0) ∧
      (∀ i, c.y₂ i % 5 = 0) ∧
      c.reportedEligible =
        e7ResidualExpectedEligibleCount c.residualType ∧
      e7ApplyReflections d₁ c.leftReflections = some target₁ ∧
      e7ApplyReflections d₂ c.rightReflections = some target₂ := by
    exact of_decide_eq_true (by
      simpa only [E7SurvivorOrbitCertificate.coreAudit, canonical,
        target₁, target₂, d₁, d₂] using hcore)
  have hfactor' :
      (∀ w : E7WeightIndex,
        integerDot d₁ (e7Weight4 w) % 8 = 0) ∧
      (∀ w : E7WeightIndex,
        integerDot d₂ (e7Weight4 w) % 8 = 0) := by
    exact of_decide_eq_true (by
      simpa only [
        E7SurvivorOrbitCertificate.centroidTransportFactorAudit,
        d₁, d₂] using hfactor)
  have hroots' :
      c.leftReflections.all e7ReflectionTransportCheck = true ∧
      c.rightReflections.all e7ReflectionTransportCheck = true := by
    simpa only [E7SurvivorOrbitCertificate.transportRootAudit,
      Bool.and_eq_true] using hroots
  have hcentroidCard :
      e7EligibleCount c.y₁ c.y₂ =
        Fintype.card (E7ResidualEligibleIndex d₁ d₂) := by
    unfold e7EligibleCount
    exact Fintype.card_congr
      (e7CentroidResidualEquivOfFactorAudits
        c.y₁ c.y₂ hcore'.1 hcore'.2.1 hfactor'.1 hfactor'.2)
  have hleft := e7Residual_card_applyReflections_left
    (d₂ := d₂) c.leftReflections hroots'.1 hcore'.2.2.2.1
  have hright := e7Residual_card_applyReflections_right
    (d₁ := target₁) c.rightReflections hroots'.2 hcore'.2.2.2.2
  have hcanonical :
      Fintype.card (E7ResidualEligibleIndex target₁ target₂) =
        e7ResidualExpectedEligibleCount c.residualType := by
    cases hswap : c.swapFactors with
    | false =>
        simpa [target₁, target₂, canonical, hswap,
          e7ResidualCanonicalEligibleCount] using
            e7ResidualCanonicalEligibleCount_checked c.residualType
    | true =>
        calc
          _ = Fintype.card
              (E7ResidualEligibleIndex target₂ target₁) :=
            Fintype.card_congr (e7ResidualSwapEquiv target₁ target₂)
          _ = e7ResidualExpectedEligibleCount c.residualType := by
            simpa [target₁, target₂, canonical, hswap,
              e7ResidualCanonicalEligibleCount] using
                e7ResidualCanonicalEligibleCount_checked c.residualType
  have heligible :
      e7EligibleCount c.y₁ c.y₂ = c.reportedEligible := by
    calc
      _ = Fintype.card (E7ResidualEligibleIndex d₁ d₂) := hcentroidCard
      _ = Fintype.card (E7ResidualEligibleIndex target₁ d₂) := hleft
      _ = Fintype.card (E7ResidualEligibleIndex target₁ target₂) := hright
      _ = e7ResidualExpectedEligibleCount c.residualType := hcanonical
      _ = c.reportedEligible := hcore'.2.2.1.symm
  unfold E7SurvivorOrbitCertificate.check
  apply decide_eq_true
  exact ⟨hcore'.1, hcore'.2.1, heligible,
    hcore'.2.2.2.1, hcore'.2.2.2.2⟩

end SRG266
