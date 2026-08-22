/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.AuditedHostReduction
import SRG266.Lattice.Branches.A15
import SRG266.Lattice.Branches.A15Construction

/-!
# Aggregate interface for the A15 branch

This module connects the branch payload to `AuditedRank15HostCase` and the
enumeration-based transport.
-/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Package the branch payload as an audited host case. -/
def A15BranchPayload.toHostCase {x : V} (P : A15BranchPayload G x) :
    AuditedRank15HostCase G x :=
  .a15Plus P.residue P.coordinates P.residue_cases P.coordinate_count
    P.coordinate_bounds P.coordinate_sum P.coordinate_sq_sum
    P.special_residue_bound P.realization

/-- Derive the final shell case from the whole-search inputs. -/
theorem A15BranchPayload.hasFinalShellCase [A15CentroidEnumerationInput]
    [A15ExactEnumerationInput] (hG : IsHypothetical G) (x : V)
    (P : A15BranchPayload G x) : Nonempty (A15FinalShellCase G x) :=
  a15CanonicalRealization_hasFinalShellCase G hG x P.residue P.coordinates
    P.residue_cases P.coordinate_count P.coordinate_bounds P.coordinate_sum
    P.coordinate_sq_sum P.special_residue_bound P.realization

/-- A pure embedding whose norm-one-free core is modelled by `A₁₅⁺` produces
the audited host payload. -/
theorem a15Plus_branch_of_model {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x)
    (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier}
    (hu : ∀ i, E.host.pairing (u i) (u i) = 1)
    (hmodel : IsHostCoreModel E.host u a15PlusGram) :
    Nonempty (AuditedRank15HostCase G x) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hu hmodel
  obtain ⟨P⟩ := a15BranchPayload_of_pureCoreModel hG hc M
  exact ⟨P.toHostCase G⟩

end Lattice
end SRG266
