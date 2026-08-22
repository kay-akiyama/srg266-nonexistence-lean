import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Start00
import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Start01

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-! # Compiled-start shell bound for group 2 representative 0 -/

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameGroup2Representative0000_shellLength :
    (compactNearColumnShell
      fractionalNearFrameGroup2Representative0000.nearMask 0).length = 493 := by
  rw [← compactNearColumnShellCount_eq_length]
  decide +kernel

theorem fractionalNearFrameGroup2Representative0000_startBound :
    CompactIndexedEmptyStartBoundOn
      fractionalNearFrameGroup2Representative0000.nearMask
      fractionalNearFrameGroup2Representative0000Witness
      (compactNearColumnShell
        fractionalNearFrameGroup2Representative0000.nearMask 0) := by
  exact compactIndexedEmptyStartBoundOn_of_forward_reverse
    fractionalNearFrameGroup2Representative0000.nearMask
    fractionalNearFrameGroup2Representative0000Witness
    350 143 fractionalNearFrameGroup2Representative0000_shellLength
    fractionalNearFrameGroup2Representative0000_start00
    fractionalNearFrameGroup2Representative0000_start01

end SRG266.Certificates
