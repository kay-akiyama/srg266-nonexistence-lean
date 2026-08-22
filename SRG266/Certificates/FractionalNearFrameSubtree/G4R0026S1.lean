import SRG266.Certificates.FractionalNearFrameSubtree.G4R0026S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G4R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0026_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0026Mask fractionalNearFrameSubtreeG4R0026Witness
      (fractionalNearFrameSubtreeG4R0026Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0026Mask (fractionalNearFrameSubtreeG4R0026Endpoint 0)).drop 48).take 12)
      (5861) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0026_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0026Mask fractionalNearFrameSubtreeG4R0026Witness
      (fractionalNearFrameSubtreeG4R0026Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0026Mask (fractionalNearFrameSubtreeG4R0026Endpoint 0)).drop 60).take 12)
      (5861) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0026_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0026Mask fractionalNearFrameSubtreeG4R0026Witness
      (fractionalNearFrameSubtreeG4R0026Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0026Mask (fractionalNearFrameSubtreeG4R0026Endpoint 0)).drop 72).take 12)
      (5861) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
