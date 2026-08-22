/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.A15MinedDirectPayload
import SRG266.Hosts.A15MinedTransport

/-!
# Closing the `A₁₅⁺` branch through the mined finite transport

The bounded geometric payload construction is isolated in
`SRG266.Lattice.Branches.A15MinedDirectPayload`.  This small assembly module
sends its 17-profile mined realization to the final shell contradiction.
-/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mined route reaches a final shell case without either whole-search
enumeration input. -/
theorem A15MinedDirectPayload.hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (P : A15MinedDirectPayload (G := G) x) :
    Nonempty (A15FinalShellCase G x) :=
  a15MinedNormRealization_hasFinalShellCase G hG x
    P.coordinates P.profile P.realization

/-- **The `A₁₅⁺` branch is closed.**  The payload it produces reaches a final
A15 shell case, and all four of those are refuted by
`SRG266.no_a15FinalShellCase`. -/
theorem not_isHostCoreModel_a15Plus (hMT : NoQuasiSymmetricDesign56.{u})
    {x : V} (hG : IsHypothetical G) (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier} (hu : ∀ i, E.host.pairing (u i) (u i) = 1) :
    ¬IsHostCoreModel E.host u a15PlusGram := by
  intro hmodel
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hu hmodel
  obtain ⟨P⟩ := a15MinedDirectPayload_of_pureCoreModel hG hc M
  exact
    (no_a15FinalShellCase G hMT hG x).false
      (P.hasFinalShellCase G hG x).some

/-- **The full `A₁₅⁺` chain.**  The maximal orthonormal family comes from the
norm-one splitting of `SRG266/Lattice/Core.lean`; the classification hypothesis
is applied to *that* family only. -/
theorem no_pure_a15PlusCore (hMT : NoQuasiSymmetricDesign56.{u})
    {x : V} (hG : IsHypothetical G) (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    (hclass : ∀ (k : ℕ) (u : Fin k → E.host.carrier),
      (∀ i, E.host.pairing (u i) (u i) = 1) →
      (∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) →
      (∀ w : E.host.carrier, (∀ i, E.host.pairing (u i) w = 0) →
        E.host.pairing w w ≠ 1) →
      IsHostCoreModel E.host u a15PlusGram) : False := by
  obtain ⟨k, u, hnorm, horth, hfree, -⟩ :=
    E.host.exists_orthonormal_normOneFree
  exact not_isHostCoreModel_a15Plus G hMT hG E hpure hnorm
    (hclass k u hnorm horth hfree)

end Lattice
end SRG266
