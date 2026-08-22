import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Data
import SRG266.QuasiSymmetric.FractionalNearFrameRangeAudit

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-! # Reverse compiled-start shell prefix for group 2 representative 0 -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameGroup2Representative0000_start01 :
    CompactIndexedEmptyStartBoundOn
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      ((compactNearColumnShellReverse
        fractionalNearFrameGroup2Representative0000.nearMask 0).take 143) := by
  apply compactIndexedEmptyStartBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
