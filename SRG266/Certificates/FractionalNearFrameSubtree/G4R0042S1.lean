import SRG266.Certificates.FractionalNearFrameSubtree.G4R0042S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G4R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG4R0042_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0042Mask fractionalNearFrameSubtreeG4R0042Witness
      (fractionalNearFrameSubtreeG4R0042Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0042Mask (fractionalNearFrameSubtreeG4R0042Endpoint 0)).drop 48).take 12)
      (-755) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0042_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0042Mask fractionalNearFrameSubtreeG4R0042Witness
      (fractionalNearFrameSubtreeG4R0042Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0042Mask (fractionalNearFrameSubtreeG4R0042Endpoint 0)).drop 60).take 12)
      (-755) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG4R0042_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG4R0042Mask fractionalNearFrameSubtreeG4R0042Witness
      (fractionalNearFrameSubtreeG4R0042Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG4R0042Mask (fractionalNearFrameSubtreeG4R0042Endpoint 0)).drop 72).take 12)
      (-755) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
