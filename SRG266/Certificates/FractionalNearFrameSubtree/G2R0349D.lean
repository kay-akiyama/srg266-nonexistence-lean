import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0349`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0349Mask : ℕ := 5668923786376209

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0349Witness : Array ℤ :=
  #[910, 335, 707, 633, 907, 776, -1337, -689, -879, 0, -740, -949, 0, -134,
  170, 377, 310, 496, -289, -565, -220, 48, 336, 138, 81, 785, -52, 1452,
  -665, 378, 220, 455, -154, -194, -263, -16, -73, 554, 746, 275, 72, -588,
  -194, -100, 855, -582, 424, 597, 204, 533, -20, -134, 226, 439, 125, -586,
  50, 189, 96, -53, 301, 29, 497, 752, 63, -78, 108, 43, -312, -369, 267, 4,
  -99, 137, 372, -182, -270, 302, -168, 1136, 1435, 221, 450, 703, -745,
  -195, -48, 1114, 471, 567, 156, -416, 298, -136, -170, -543, 148, -322,
  -561, 468, 444, -540, -196, 486, -332, -177, -497, 269, 0, -561, 13, -210,
  198, -542, -357, -395, 330, -246, -544, -163, 336, -371, 356, 385, -731,
  933, -238, -592, 253, 782, 241, -663, 24, -353, -452, 218, -185, 0, -747,
  -567, -961, 208, -99, -446, 309, 584, -49, 140, -85, 240, 681, -251, 623,
  -466, 416, 468, -278, 206, 243, 60, 45, -227, -78, 289, 380, -174, -522,
  -63]

theorem fractionalNearFrameSubtreeG2R0349_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0349Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0349Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0349Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0349_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0349LowerBoundTable : List ℤ :=
  [-156, -759, -414, 1271, 1055, 571, 1625, 128, 1004, 437, 476, -3071,
  1570, -1860, 910, 819, 482, 2155, 143, 1228, 1885, 3614, 1005, 99, 2636]

def fractionalNearFrameSubtreeG2R0349LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0349Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0349LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
