import SRG266.Certificates.FractionalNearFrameSubtree.G4R0003D
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 0 for `G4R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0003_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0003Mask fractionalNearFrameSubtreeG4R0003Witness
      (fractionalNearFrameSubtreeG4R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0003Mask (fractionalNearFrameSubtreeG4R0003Endpoint 0)).drop 0).take 12)
      (-1719) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0003_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0003Mask fractionalNearFrameSubtreeG4R0003Witness
      (fractionalNearFrameSubtreeG4R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0003Mask (fractionalNearFrameSubtreeG4R0003Endpoint 0)).drop 12).take 12)
      (-1719) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0003_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0003Mask fractionalNearFrameSubtreeG4R0003Witness
      (fractionalNearFrameSubtreeG4R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0003Mask (fractionalNearFrameSubtreeG4R0003Endpoint 0)).drop 24).take 12)
      (-1719) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0003_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0003Mask fractionalNearFrameSubtreeG4R0003Witness
      (fractionalNearFrameSubtreeG4R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0003Mask (fractionalNearFrameSubtreeG4R0003Endpoint 0)).drop 36).take 12)
      (-1719) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
