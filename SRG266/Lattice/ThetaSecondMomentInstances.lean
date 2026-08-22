/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.ADERootOrbitData
import SRG266.Lattice.ThetaSecondMomentReduction

/-!
# Checked ADE orbit instances for the theta reduction

This module is the intentionally certificate-heavy endpoint of the lightweight
second-moment reduction.  Every selected orbit table is checked by the Lean
kernel in the generated shard modules before it can inhabit the selector.
-/

namespace SRG266
namespace Lattice

/-- The generated kernel-checked ADE certificates packaged as the bounded
selector used by the theta reduction. -/
noncomputable def checkedADEOrbitCertificateSelectorLE15 :
    ADEOrbitCertificateSelectorLE15 :=
  adeRootOrbitCertificateOfRegularOfRankLE

end Lattice

/-- The minimal root second-moment input implies the theta/ADE
interface with all finite root-orbit data discharged internally. -/
theorem thetaEutacticADEDecomposition_of_checkedSecondMoment
    (hTheta : ThetaRootSecondMomentInput) :
    ThetaEutacticADEDecompositionInput :=
  thetaEutacticADEDecomposition_of_secondMoment
    Lattice.checkedADEOrbitCertificateSelectorLE15 hTheta

end SRG266
