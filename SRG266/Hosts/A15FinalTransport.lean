/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15FinalTransportSurvivors
import SRG266.Hosts.A15ProjectorSoundness

/-!
# Transport from all checked A15 projector profiles

This module combines the four constructive survivor transports with the nine
empty-survivor eliminations backed by the full projector certificate.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An indexed direct realization of any checked projector profile yields a
final shell case. The nine profiles with empty survivor arrays are discharged
by the checked projector theorem itself. -/
theorem A15ShellGramRealization.hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (i : Fin a15ProjectorProfileCertificates.size)
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfileCertificates[i].profile.centroidVector) :
    Nonempty (A15FinalShellCase G x) := by
  fin_cases i
  · exact realization.profile00_hasFinalShellCase G hG x
  · exact realization.profile01_hasFinalShellCase G hG x
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile02 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile02] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile03 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile03] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile04 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile04] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile05 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile05] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile06 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile06] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile07 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile07] at hsurvivor
  · exact realization.profile08_hasFinalShellCase G hG x
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile09 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile09] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile10 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile10] at hsurvivor
  · have hsurvivor :=
      realization.projectorOrbitTotals_mem_survivors
        G hG x a15ProjectorProfile11 (by
          simp [a15ProjectorProfileCertificates])
    simp [a15ProjectorProfile11] at hsurvivor
  · exact realization.profile12_hasFinalShellCase G hG x

end SRG266
