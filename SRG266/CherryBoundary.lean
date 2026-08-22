/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.ThetaSecondMomentMain
import SRG266.QuasiSymmetric.SemanticBridge
import SRG266.Certificates.A15CentroidEnumerationProof
import SRG266.Certificates.A15ExactEnumerationProof
import SRG266.Certificates.E7ConcreteEnumerationProof
import SRG266.Hosts.E7ScalarDPInstance

/-!
# Reduction to the residual cherry-cover obstruction

All lattice and host-enumeration inputs are discharged internally. The only
remaining proposition-valued input is the finite residual cherry-cover
obstruction.
-/

namespace SRG266

universe u

/-- Nonexistence of `srg(266,45,0,9)` from the residual cherry-cover
obstruction alone. -/
theorem srg266_nonexistence_of_noResidualCherryCover
    (hCherry : QuasiSymmetric.NoResidualCherryCover)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬IsHypothetical G :=
  srg266_nonexistence_of_cherry_audit_inputs hCherry
    inferInstance inferInstance inferInstance inferInstance G

end SRG266
