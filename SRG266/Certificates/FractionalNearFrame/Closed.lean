/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.FractionalNearFrame.Final
import SRG266.Certificates.RootNearNormalFormCoverage

/-!
# Closed fractional near-frame audit

This small assembly module supplies the kernel-checked 2,752-orbit normal-form
cover to the semantic fractional near-frame obstruction.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Certificates

theorem isEmpty_globalDesign_fractionalNearFrame : IsEmpty GlobalDesign :=
  isEmpty_globalDesign_of_fractionalNearFrameAudit rootNearNormalFormCover

/-- No residual cherry cover exists. -/
theorem noResidualCherryCover_holds : NoResidualCherryCover :=
  noResidualCherryCover_of_fractionalNearFrameAudit rootNearNormalFormCover

theorem noQuasiSymmetricDesign56_fractionalNearFrameAudit :
    NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_fractionalNearFrame rootNearNormalFormCover

end SRG266.QuasiSymmetric
