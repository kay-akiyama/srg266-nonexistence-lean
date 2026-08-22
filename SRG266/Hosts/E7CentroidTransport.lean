/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7SurvivorData
import SRG266.Hosts.E7CentroidRealization

/-!
# Direct E7 centroid realizations

The centroid certificates use the integral coordinates `y₁,y₂`, while the
residual host eliminations use `d₁ = y₁/5` and `d₂ = y₂/5`. This module
defines the direct realization at the certificate scale, derives the bounded
integer centroid system from shell multiplicities, and supplies the exact
subtype transport to the residual scale.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def E7CentroidShellGramRealization.toFiniteShell
    {x : V} {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂) :
    FiniteShellGramRealization G x
      (E7EligibleIndex y₁ y₂)
      (fun u v => e7ShellInner u.1 v.1) where
  shell := realization.shell
  gram := realization.gram
  eq_of_inner_eq_three := by
    intro u v huv
    exact Subtype.ext ((e7ShellInner_eq_three_iff u.1 v.1).mp huv)

/-- The two certificate-scale centroid profiles have total squared norm
`1200`.  This follows directly from the 220 eligibility equations and the two
centroid equations, without consulting the component-profile enumeration. -/
theorem E7CentroidShellGramRealization.profile_sq_sum
    (hG : IsHypothetical G) (x : V) {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂) :
    (∑ i, (y₁ i) ^ 2) + ∑ i, (y₂ i) ^ 2 = 1200 := by
  have hleft :
      (∑ B, integerDot y₁ (e7Weight4 (realization.shell B).1.1)) =
        22 * ∑ i, (y₁ i) ^ 2 := by
    unfold integerDot
    calc
      (∑ B, ∑ i, y₁ i * e7Weight4 (realization.shell B).1.1 i) =
          ∑ i, ∑ B, y₁ i * e7Weight4 (realization.shell B).1.1 i := by
        rw [Finset.sum_comm]
      _ = ∑ i, y₁ i *
          (∑ B, e7Weight4 (realization.shell B).1.1 i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, y₁ i * (22 * y₁ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [realization.leftCentroid i]
      _ = 22 * ∑ i, (y₁ i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hright :
      (∑ B, integerDot y₂ (e7Weight4 (realization.shell B).1.2)) =
        22 * ∑ i, (y₂ i) ^ 2 := by
    unfold integerDot
    calc
      (∑ B, ∑ i, y₂ i * e7Weight4 (realization.shell B).1.2 i) =
          ∑ i, ∑ B, y₂ i * e7Weight4 (realization.shell B).1.2 i := by
        rw [Finset.sum_comm]
      _ = ∑ i, y₂ i *
          (∑ B, e7Weight4 (realization.shell B).1.2 i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, y₂ i * (22 * y₂ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [realization.rightCentroid i]
      _ = 22 * ∑ i, (y₂ i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have htotal :
      (∑ B,
          (integerDot y₁ (e7Weight4 (realization.shell B).1.1) +
            integerDot y₂ (e7Weight4 (realization.shell B).1.2))) =
        26400 := by
    calc
      _ = ∑ _B : SecondSubconstituent G x, (120 : ℤ) := by
        apply Finset.sum_congr rfl
        intro B _
        exact (realization.shell B).2
      _ = 26400 := by
        rw [Finset.sum_const, Finset.card_univ,
          secondSubconstituent_card G hG x]
        norm_num
  rw [Finset.sum_add_distrib, hleft, hright] at htotal
  omega

/-- Integer shell multiplicities at the centroid scale. -/
def E7CentroidShellGramRealization.integerMultiplicity
    {x : V} {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂)
    (w : E7EligibleIndex y₁ y₂) : ℤ :=
  ((realization.toFiniteShell G).multiplicity G w : ℤ)

/-- Every direct realization supplies the bounded integer solution tested by
an E7 centroid certificate. -/
theorem E7CentroidShellGramRealization.exists_centroid_bounded_solution
    (hG : IsHypothetical G) (x : V)
    {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂) :
    ∃ m : E7EligibleIndex y₁ y₂ → ℤ,
      (∀ w, 0 ≤ m w) ∧
      (∀ w, m w ≤ 3) ∧
      e7CentroidMatrix y₁ y₂ *ᵥ m =
        e7CentroidTarget y₁ y₂ := by
  let finite := realization.toFiniteShell G
  let m := realization.integerMultiplicity G
  refine ⟨m, ?_, ?_, ?_⟩
  · intro w
    exact Int.natCast_nonneg _
  · intro w
    change ((finite.multiplicity G w : ℕ) : ℤ) ≤ 3
    exact_mod_cast finite.multiplicity_le_three G hG x w
  · funext row
    cases row with
    | count =>
        simp only [Matrix.mulVec, dotProduct, e7CentroidMatrix,
          e7CentroidTarget, m,
          E7CentroidShellGramRealization.integerMultiplicity, one_mul]
        rw [← Nat.cast_sum,
          (realization.toFiniteShell G).sum_multiplicity G,
          secondSubconstituent_card G hG x]
        norm_num
    | left i =>
        simp only [Matrix.mulVec, dotProduct, e7CentroidMatrix,
          e7CentroidTarget, m,
          E7CentroidShellGramRealization.integerMultiplicity]
        calc
          (∑ w, e7Weight4 w.1.1 i *
              ((realization.toFiniteShell G).multiplicity G w : ℤ)) =
              ∑ w,
                ((realization.toFiniteShell G).multiplicity G w : ℤ) *
                  e7Weight4 w.1.1 i := by
            apply Finset.sum_congr rfl
            intro w _
            ring
          _ = ∑ B, e7Weight4 (realization.shell B).1.1 i := by
            rw [(realization.toFiniteShell G).sum_multiplicity_mul G
              (fun w => e7Weight4 w.1.1 i)]
            simp [E7CentroidShellGramRealization.toFiniteShell]
          _ = 22 * y₁ i := realization.leftCentroid i
    | right i =>
        simp only [Matrix.mulVec, dotProduct, e7CentroidMatrix,
          e7CentroidTarget, m,
          E7CentroidShellGramRealization.integerMultiplicity]
        calc
          (∑ w, e7Weight4 w.1.2 i *
              ((realization.toFiniteShell G).multiplicity G w : ℤ)) =
              ∑ w,
                ((realization.toFiniteShell G).multiplicity G w : ℤ) *
                  e7Weight4 w.1.2 i := by
            apply Finset.sum_congr rfl
            intro w _
            ring
          _ = ∑ B, e7Weight4 (realization.shell B).1.2 i := by
            rw [(realization.toFiniteShell G).sum_multiplicity_mul G
              (fun w => e7Weight4 w.1.2 i)]
            simp [E7CentroidShellGramRealization.toFiniteShell]
          _ = 22 * y₂ i := realization.rightCentroid i

/-- Finite condition needed to identify the certificate-scale shell with the
residual `y/5` shell. -/
def E7SurvivorOrbitCertificate.centroidTransportValid
    (c : E7SurvivorOrbitCertificate) : Bool :=
  decide (
    ∀ w : E7ShellIndex,
      e7Eligible c.y₁ c.y₂ w ↔
        e7ResidualEligible
          (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5) w)

/-- Reduce the paired-shell transport audit to the two 56-weight factors.

Coordinatewise divisibility by five identifies each original centroid with
five times its residual centroid. Divisibility of every one-factor pairing
by eight then makes the residual evaluation divisions exact, so the paired
eligibility equations are equivalent by integer arithmetic. -/
theorem E7SurvivorOrbitCertificate.centroidTransportValid_of_factor_audit
    (c : E7SurvivorOrbitCertificate)
    (hdiv₁ : ∀ i, c.y₁ i % 5 = 0)
    (hdiv₂ : ∀ i, c.y₂ i % 5 = 0)
    (heval₁ : ∀ w : E7WeightIndex,
      integerDot (fun i => c.y₁ i / 5) (e7Weight4 w) % 8 = 0)
    (heval₂ : ∀ w : E7WeightIndex,
      integerDot (fun i => c.y₂ i / 5) (e7Weight4 w) % 8 = 0) :
    c.centroidTransportValid = true := by
  unfold E7SurvivorOrbitCertificate.centroidTransportValid
  apply decide_eq_true
  exact e7Eligible_iff_residual_of_factor_audits
    c.y₁ c.y₂ hdiv₁ hdiv₂ heval₁ heval₂

theorem E7SurvivorOrbitCertificate.centroidTransportValid_iff
    (c : E7SurvivorOrbitCertificate)
    (hvalid : c.centroidTransportValid = true) :
    ∀ w : E7ShellIndex,
      e7Eligible c.y₁ c.y₂ w ↔
        e7ResidualEligible
          (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5) w := by
  exact of_decide_eq_true hvalid

def E7SurvivorOrbitCertificate.centroidResidualEquiv
    (c : E7SurvivorOrbitCertificate)
    (hvalid : c.centroidTransportValid = true) :
    E7EligibleIndex c.y₁ c.y₂ ≃
      E7ResidualEligibleIndex
        (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5) :=
  (Equiv.refl E7ShellIndex).subtypeEquiv
    (c.centroidTransportValid_iff hvalid)

/-- Transport a checked survivor realization from certificate scale to the
residual scale consumed by the Weyl reduction. -/
def E7CentroidShellGramRealization.toResidual
    {x : V} (c : E7SurvivorOrbitCertificate)
    (hcheck : c.transportCheck = true)
    (hvalid : c.centroidTransportValid = true)
    (realization :
      E7CentroidShellGramRealization G x c.y₁ c.y₂) :
    E7ShellGramRealization G x
      (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5) where
  shell B := c.centroidResidualEquiv hvalid (realization.shell B)
  gram B C := by
    exact realization.gram B C
  leftCentroid i := by
    have hparts := c.transportCheck_parts hcheck
    have hprofile :
        (∀ j, c.y₁ j % 5 = 0) ∧
          ∀ j, c.y₂ j % 5 = 0 := by
      have hc := of_decide_eq_true (by
        simpa only [E7SurvivorOrbitCertificate.check] using hparts.1)
      exact ⟨hc.1, hc.2.1⟩
    change
      (∑ B, e7Weight4 (realization.shell B).1.1 i) =
        110 * (c.y₁ i / 5)
    rw [realization.leftCentroid i]
    have hdiv : (5 : ℤ) ∣ c.y₁ i :=
      Int.dvd_iff_emod_eq_zero.mpr (hprofile.1 i)
    have hcancel := Int.ediv_mul_cancel hdiv
    nlinarith
  rightCentroid i := by
    have hparts := c.transportCheck_parts hcheck
    have hprofile :
        (∀ j, c.y₁ j % 5 = 0) ∧
          ∀ j, c.y₂ j % 5 = 0 := by
      have hc := of_decide_eq_true (by
        simpa only [E7SurvivorOrbitCertificate.check] using hparts.1)
      exact ⟨hc.1, hc.2.1⟩
    change
      (∑ B, e7Weight4 (realization.shell B).1.2 i) =
        110 * (c.y₂ i / 5)
    rw [realization.rightCentroid i]
    have hdiv : (5 : ℤ) ∣ c.y₂ i :=
      Int.dvd_iff_emod_eq_zero.mpr (hprofile.2 i)
    have hcancel := Int.ediv_mul_cancel hdiv
    nlinarith

/-- Direct, certificate-independent version of `toResidual`.  Divisibility
and the two factor audits are the complete assumptions needed to change from
centroid scale to residual scale. -/
def E7CentroidShellGramRealization.toResidualOfFactorAudits
    {x : V} {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂)
    (hdiv₁ : ∀ i, y₁ i % 5 = 0)
    (hdiv₂ : ∀ i, y₂ i % 5 = 0)
    (heval₁ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₁ i / 5) (e7Weight4 w) % 8 = 0)
    (heval₂ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₂ i / 5) (e7Weight4 w) % 8 = 0) :
    E7ShellGramRealization G x
      (fun i => y₁ i / 5) (fun i => y₂ i / 5) where
  shell B :=
    e7CentroidResidualEquivOfFactorAudits
      y₁ y₂ hdiv₁ hdiv₂ heval₁ heval₂ (realization.shell B)
  gram B C := realization.gram B C
  leftCentroid i := by
    change
      (∑ B, e7Weight4 (realization.shell B).1.1 i) =
        110 * (y₁ i / 5)
    rw [realization.leftCentroid i]
    have hcancel := Int.ediv_mul_cancel
      (Int.dvd_iff_emod_eq_zero.mpr (hdiv₁ i))
    nlinarith
  rightCentroid i := by
    change
      (∑ B, e7Weight4 (realization.shell B).1.2 i) =
        110 * (y₂ i / 5)
    rw [realization.rightCentroid i]
    have hcancel := Int.ediv_mul_cancel
      (Int.dvd_iff_emod_eq_zero.mpr (hdiv₂ i))
    nlinarith

end SRG266
