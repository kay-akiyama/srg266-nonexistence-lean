/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.AuditedHostReduction
import SRG266.Lattice.MixedBoundary
import SRG266.Lattice.YangYoshino

/-!
# Assembled conditional nonexistence theorems

This file exposes conditional forms of the nonexistence theorem, separating
the rank-15 embedding, lattice classification, mixed-direction exclusion, and
finite certificate equalities.
-/

namespace SRG266

universe u

/-- Conditional nonexistence of `srg(266,45,0,9)` from the explicit
rank-15 host reduction and the quasi-symmetric-design nonexistence theorem. -/
theorem srg266_nonexistence_of_rank15HostReduction
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hHost : Rank15HostReduction.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G := by
  classical
  intro hG
  have hcard : Fintype.card V = 266 := hG.card
  have hnonempty : Nonempty V := by
    exact Fintype.card_pos_iff.mp (by omega)
  let x : V := Classical.choice hnonempty
  obtain ⟨host⟩ := hHost G hG x
  exact (no_rank15HostCase G hMT hG x).false host

/-- Conditional nonexistence using the strong final-case reduction input. -/
theorem srg266_nonexistence_of_external_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hYY : YangYoshinoRank15Embedding.{u})
    (hFinalReduction : Rank15FinalCaseReductionInput.{u})
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_rank15HostReduction
    hMT (rank15HostReduction_of_external_inputs hYY hFinalReduction) G

/-- Conditional nonexistence with the mathematical reduction and finite search
equalities exposed as separate inputs. -/
theorem srg266_nonexistence_of_separated_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hYY : YangYoshinoRank15Embedding.{u})
    (hNormalize : Rank15PreEnumerationNormalizationInput.{u})
    (hMixed : MixedNormOneDirectionExclusionInput.{u})
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G := by
  classical
  letI : E7ScalarDPAuditInput := hE7Scalar
  letI : E7ConcreteEnumerationAuditInput := hE7Concrete
  letI : A15CentroidEnumerationInput := hA15Centroid
  letI : A15ExactEnumerationInput := hA15Exact
  intro hG
  have hnonempty : Nonempty V :=
    Fintype.card_pos_iff.mp (hG.card.symm ▸ by decide)
  let x : V := Classical.choice hnonempty
  obtain ⟨embedding⟩ := hYY G hG x
  obtain ⟨host⟩ := hNormalize G hG x embedding
  exact (no_auditedRank15HostCase G hMT hMixed hG x).false host

/-- A strictly sharper separated boundary: host-specific mixed-direction work
is required only at centroid coordinate zero.  The nonzero fibres are removed
by the local block-intersection identity and the Delsarte-coclique argument,
not by a shell enumeration. -/
theorem srg266_nonexistence_of_zeroCentroid_mixed_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hYY : YangYoshinoRank15Embedding.{u})
    (hNormalize : Rank15PreEnumerationNormalizationInput.{u})
    (hMixedZero : ZeroCentroidMixedNormOneDirectionExclusionInput.{u})
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_separated_inputs hMT hYY hNormalize
    (mixedNormOneDirectionExclusionInput_of_zeroCentroid hMT hMixedZero)
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- The mixed-direction hypothesis disappears completely: it follows from
`hMT` by the extremal-coclique and zero-centroid signed-trade arguments. -/
theorem srg266_nonexistence_without_mixed_input
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hYY : YangYoshinoRank15Embedding.{u})
    (hNormalize : Rank15PreEnumerationNormalizationInput.{u})
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_separated_inputs hMT hYY hNormalize
    (mixedNormOneDirectionExclusionInput_of_noQuasiSymmetricDesign hMT)
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- Conditional nonexistence with graph-independent lattice classification and
host-indexed mixed-direction hypotheses. -/
theorem srg266_nonexistence_of_recut_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hClass : RootedNormOneFreeClassification)
    (hIdentify : MixedNormOneHostIdentificationInput.{u})
    (hOther : MixedNonE7NormOneDirectionExclusionInput.{u})
    (hE7Mixed : E7MixedNormOneExclusion.{u})
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_separated_inputs hMT yangYoshinoRank15Embedding
    (rank15PreEnumerationNormalization_of_classification hClass)
    (mixedNormOneDirectionExclusionInput_of_recut hIdentify hOther hE7Mixed)
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- Conditional nonexistence without mixed-direction hypotheses. -/
theorem srg266_nonexistence_of_reduced_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hClass : RootedNormOneFreeClassification)
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_without_mixed_input hMT yangYoshinoRank15Embedding
    (rank15PreEnumerationNormalization_of_classification hClass)
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

end SRG266
