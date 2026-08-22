import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0026Mask : ℕ := 468279648635025

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0026Witness : Array ℤ :=
  #[555, 13, 472, -766, -1084, -1126, 0, 1070, 617, 817, 357, 722, 0, 228,
  -57, 717, -959, -1407, -231, 485, -628, -330, -35, -362, -899, -80, -670,
  -850, -193, 375, 48, 77, -86, -410, -332, -993, 651, 492, 116, -162, 1397,
  814, 8, -433, -1061, 58, 55, 662, 167, 769, 566, 262, -481, -141, 446,
  -720, -713, 203, -775, -33, 292, 544, 215, -89, 746, 167, -485, -568, 425,
  508, 365, 300, 38, 496, 534, -448, -338, -54, 346, -123, -386, 481, 268,
  639, -346, -704, -384, -608, 383, -279, 487, 682, 384, 500, 109, 343, 111,
  -7, 784, -751, 763, 133, 553, 76, -354, -11, 76, 267, 699, -244, -373,
  147, -218, 911, 742, 486, 90, 203, -1345, -408, -514, 1025, 369, 166,
  -172, 482, -1064, -848, -665, -971, 242, -301, 514, 134, 708, 294, -798,
  -249, -428, 878, -276, 248, 113, -875, 633, 300, 790, -313, -150, -24,
  1125, 867, 998, 36, 269, -265, 558, 268, -186, 237, 190, 219, 510, -684,
  242, -225, 141, 917]

theorem fractionalNearFrameSubtreeG1R0026_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0026Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0026Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0026Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0026_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0026LowerBoundTable : List ℤ :=
  [-405, 751, 514, -23, 31, -992, 656, 3018, -417, 3012, 1941, 2698, -457,
  -1232, -400, 2976, 101, 2501, 2593, 2804, 101, -1221, 2192, 764, 99]

def fractionalNearFrameSubtreeG1R0026LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0026Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0026LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
