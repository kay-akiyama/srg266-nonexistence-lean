/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15FarkasKernel

/-! # The two residual separators of the mined A15 profile search -/

namespace SRG266

/-- The two separators left after mining the centroid search down to the
15 shell-admissible norm profiles. -/
def a15MinedExceptionalCertificates : List A15CentroidRawCertificate :=
  [ { d := #[-50, -30, -10, -10, -10, 10, 10, 10,
        10, 10, 10, 10, 10, 10, 10, 10]
      q := #[0, 1, -1, -1, -1, -1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1]
      reportedResidue := 2
      reportedEligible := 89
      reportedGap := 456 },
    { d := #[-10, -10, -10, -10, -10, -10, -10, -10,
        -10, -10, -10, 10, 10, 10, 30, 50]
      q := #[0, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, 1, 1, 1, 1, -1]
      reportedResidue := 2
      reportedEligible := 89
      reportedGap := 456 } ]

/-- Both residual separators are checked by the bounded choose-four kernel. -/
theorem a15MinedExceptionalCertificates_checked :
    a15MinedExceptionalCertificates.all
      A15CentroidRawCertificate.fastCheck = true := by
  decide +kernel

end SRG266
