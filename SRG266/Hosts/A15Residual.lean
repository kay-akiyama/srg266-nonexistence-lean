/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.CocliqueDesign
import SRG266.Hosts.A15Parity
import SRG266.Hosts.A15PackingReduction

/-!
# The four residual `A₁₅⁺` profiles

The orbit-averaged projector leaves four profiles.  Two profiles give a
binary weight-three factorization of the local Gram matrix.  The other two
give the weighted triple system excluded in `A15Parity`.

This module packages those two endpoint alternatives and eliminates both.
The separate host-reduction layer remains responsible for transporting the
four concrete projector survivors into this endpoint type.
-/

namespace SRG266

universe u

/-- The exact weighted-triple data produced by either member of the final
sign-paired `A₁₅⁺` orbit. -/
structure A15ParityPacking where
  multiplicity : A15ParityTriple → ℕ
  total : ∑ t, multiplicity t = 55
  frame :
    ∀ t, 0 < multiplicity t →
      a15ParityTriplePairSum multiplicity t = 30

/-- The parity endpoint is empty by the native double-counting theorem. -/
theorem no_a15ParityPacking : IsEmpty A15ParityPacking := by
  refine ⟨fun packing => ?_⟩
  exact a15Parity_no_weighted_triple_system
    packing.multiplicity packing.total packing.frame

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two possible combinatorial endpoints of an `A₁₅⁺` projector survivor.
The binary branch stores the local one-integrability proposition. -/
inductive A15ResidualCase (x : V)
  | binary (factorization : LocalGramIsOneIntegrable G x)
  | parity (packing : A15ParityPacking)

/-- Transport the first extreme A15 projector survivor to the binary
endpoint. -/
def A15ShellGramRealization.profile0_residualCase
    {x : V}
    (realization :
      A15ShellGramRealization G x a15BinaryProfile0)
    (hselected :
      ∀ B, a15SubsetContains (realization.shell B) 0) :
    A15ResidualCase G x :=
  .binary (realization.profile0_oneIntegrable G hselected)

/-- Transport the sign-reversed extreme A15 projector survivor to the same
binary endpoint. -/
def A15ShellGramRealization.profile12_residualCase
    {x : V}
    (realization :
      A15ShellGramRealization G x a15BinaryProfile12)
    (hselected :
      ∀ B, a15SubsetContains (realization.shell B) 15) :
    A15ResidualCase G x :=
  .binary (realization.profile12_oneIntegrable G hselected)

/-- All four residual `A₁₅⁺` endpoints are impossible, conditional only on
the explicitly named quasi-symmetric-design nonexistence input. -/
theorem no_a15ResidualCase
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G) (x : V) :
    IsEmpty (A15ResidualCase G x) := by
  refine ⟨fun residual => ?_⟩
  cases residual with
  | binary factorization =>
      exact
        (localGram_not_oneIntegrable_of_noQuasiSymmetricDesign
          G hMT hG x)
          factorization
  | parity packing =>
      exact no_a15ParityPacking.false packing

end SRG266
