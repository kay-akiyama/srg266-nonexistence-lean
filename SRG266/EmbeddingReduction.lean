/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.D12Plus
import SRG266.Hosts.E7PackingReduction
import SRG266.Hosts.A15ParityTransport

/-!
# Explicit rank-15 host-reduction interface

This module is the assembly boundary between the native graph/certificate
proof and the external rank-15 embedding and odd-unimodular classification
theorems.

`Rank15HostCase` states the exact coordinate-level alternatives consumed by
the checked host eliminations:

* a normalized `D₁₂⁺` Gram realization;
* one of the five canonical `(E₇ ⊕ E₇)⁺` direct Gram realizations;
* one of the four concrete `A₁₅⁺` shell survivors, with its selected-orbit
  conclusion.

`Rank15HostReduction` packages the coordinate alternatives consumed by the
checked host eliminations.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Coordinate-level host alternatives left by the rank-15 reduction. -/
inductive Rank15HostCase (x : V)
  | d12Plus (realization : D12PlusGramRealization G x)
  | e7e7Plus (residualType : E7ResidualType)
      (realization :
        E7ShellGramRealization G x
          (e7ResidualCanonical residualType).1
          (e7ResidualCanonical residualType).2)
  | a15Plus (finalCase : A15FinalShellCase G x)

/-- External reduction input used by the assembled theorem.

The input is polymorphic in the finite graph.  It says that the embedded local
rank-12 Gram lattice can be normalized into one of the coordinate-level host
cases above. -/
abbrev Rank15HostReduction : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsHypothetical G → ∀ x : V, Nonempty (Rank15HostCase G x)

/-- Every case in the explicit host-reduction interface is excluded by the
native host proofs. -/
theorem no_rank15HostCase
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G) (x : V) :
    IsEmpty (Rank15HostCase G x) := by
  refine ⟨fun host => ?_⟩
  cases host with
  | d12Plus realization =>
      exact (no_d12PlusRealization G hMT hG x) ⟨realization⟩
  | e7e7Plus residualType realization =>
      exact
        (no_e7ResidualCanonical_realization
          G hG x residualType).false realization
  | a15Plus finalCase =>
      exact (no_a15FinalShellCase G hMT hG x).false finalCase

end SRG266
