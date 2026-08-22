/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Branches.E7PayloadConstruction
import SRG266.Lattice.Branches.E7MinedPayload
import SRG266.Lattice.Branches.PureCore

/-!
# Closure of the pure E7 branch

The lattice construction and mined contradiction are isolated in bounded
modules; this wrapper connects them to the classified host-core interface.
-/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The `(E₇ ⊕ E₇)⁺` branch is closed.**  The payload it produces is refuted by
the mined 25-profile/Weyl/residual route. -/
theorem not_isHostCoreModel_e7e7Plus {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier} (hu : ∀ i, E.host.pairing (u i) (u i) = 1) :
    ¬IsHostCoreModel E.host u e7e7PlusGram := by
  intro hmodel
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hu hmodel
  obtain ⟨P⟩ := e7BranchPayload_of_pureCoreModel hG hc M
  exact P.elim G hG x

/-- The maximal orthonormal family comes from the norm-one splitting of
`SRG266/Lattice/Core.lean`; the classification hypothesis is applied only to
that family. -/
theorem no_pure_e7e7PlusCore
    {x : V} (hG : IsHypothetical G) (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    (hclass : ∀ (k : ℕ) (u : Fin k → E.host.carrier),
      (∀ i, E.host.pairing (u i) (u i) = 1) →
      (∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) →
      (∀ w : E.host.carrier, (∀ i, E.host.pairing (u i) w = 0) →
        E.host.pairing w w ≠ 1) →
      IsHostCoreModel E.host u e7e7PlusGram) : False := by
  obtain ⟨k, u, hnorm, horth, hfree, -⟩ :=
    E.host.exists_orthonormal_normOneFree
  exact not_isHostCoreModel_e7e7Plus G hG E hpure hnorm
    (hclass k u hnorm horth hfree)

end Lattice
end SRG266
