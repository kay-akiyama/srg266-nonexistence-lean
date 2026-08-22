import SRG266.Certificates.FractionalNearFrame.Group2Entries
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Native-free group 2 mask identification
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2_masks :
    fractionalNearFrameCertificatesGroup2.map
        FractionalNearFrameCertificateEntry.nearMask =
      rootNearRepresentativeGroup2 := by
  decide +kernel

end SRG266.Certificates
