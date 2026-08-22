/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Main
import SRG266.Lattice.Rank24HarmonicTheta
import SRG266.Lattice.ThetaEutaxyKneserBridge
import SRG266.Lattice.ThetaSecondMomentInstances
import SRG266.QuasiSymmetric.CherryRecut

/-!
# Nonexistence from the minimal theta second moment

This endpoint separates the two mathematical statements that remain after the
root-system and host-search reductions:

* nonexistence of the quasi-symmetric design, or its weaker residual
  cherry-cover form;
* the exact degree-two root second moment for norm-one-free unimodular
  lattices in ranks twelve through fifteen.

It additionally exposes the four exact finite E7/A15 audit equalities so the
lightweight build does not schedule their large certificate families.

Every bounded ADE root orbit is filled by kernel-checked Lean data.  The four
E7/A15 whole-search equalities remain explicit arguments in this lightweight
endpoint; their existing pure-Lean instance modules can discharge them after
their own low-memory certificate sweeps.  The Yang--Yoshino embedding, ADE
classification, full-rank glue calculations, mixed-direction exclusion, and
all graph-specific reasoning are theorems of the project.
-/

namespace SRG266

universe u

/-- Nonexistence of `srg(266,45,0,9)` from the design theorem and the single
root second-moment identity. -/
theorem srg266_nonexistence_of_secondMoment_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hTheta : ThetaRootSecondMomentInput)
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_without_mixed_input hMT yangYoshinoRank15Embedding
    (rank15PreEnumerationNormalization_of_thetaEutaxy
      (thetaEutacticADEDecomposition_of_checkedSecondMoment hTheta))
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- The design-side input is reduced to the finite residual cherry-cover
obstruction; the root-system side remains the single second moment. -/
theorem srg266_nonexistence_of_cherry_secondMoment_inputs
    (hCherry : QuasiSymmetric.NoResidualCherryCover)
    (hTheta : ThetaRootSecondMomentInput)
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_secondMoment_inputs
    (QuasiSymmetric.noQuasiSymmetricDesign56_of_noResidualCherryCover hCherry)
    hTheta hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- The internally proved rank-24 harmonic-theta and van der Blij arguments
discharge the root second-moment input. -/
theorem srg266_nonexistence_of_design_audit_inputs
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_secondMoment_inputs hMT
    Lattice.thetaRootSecondMoment_of_harmonicTheta
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

/-- The same endpoint with the design side reduced to the residual
cherry-cover obstruction. -/
theorem srg266_nonexistence_of_cherry_audit_inputs
    (hCherry : QuasiSymmetric.NoResidualCherryCover)
    (hE7Scalar : E7ScalarDPAuditInput)
    (hE7Concrete : E7ConcreteEnumerationAuditInput)
    (hA15Centroid : A15CentroidEnumerationInput)
    (hA15Exact : A15ExactEnumerationInput)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_cherry_secondMoment_inputs hCherry
    Lattice.thetaRootSecondMoment_of_harmonicTheta
    hE7Scalar hE7Concrete hA15Centroid hA15Exact G

end SRG266
