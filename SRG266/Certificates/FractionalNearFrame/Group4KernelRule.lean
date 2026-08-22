import SRG266.Certificates.FractionalNearFrame.Group4Entries
import SRG266.Certificates.FractionalNearFrame.Group4Chunk0000KernelHall
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Native-free group 4 empty rule and mask identification
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup4_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup4 := by
  simpa [fractionalNearFrameCertificatesGroup4] using
    fractionalNearFrameCertificatesGroup4Chunk0000_emptyRule

theorem fractionalNearFrameCertificatesGroup4_masks :
    fractionalNearFrameCertificatesGroup4.map
        FractionalNearFrameCertificateEntry.nearMask =
      rootNearRepresentativeGroup4 := by
  rw [fractionalNearFrameCertificatesGroup4,
    fractionalNearFrameCertificatesGroup4Chunk0000_masks]
  decide +kernel

end SRG266.Certificates
