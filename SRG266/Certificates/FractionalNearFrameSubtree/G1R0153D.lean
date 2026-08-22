import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0153`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0153Mask : ℕ := 1039879777065648

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0153Witness : Array ℤ :=
  #[344, -90, 345, 16, 78, -14, -9, 13, 27, -133, 95, -2, -2, -223, 226, -9,
  -166, 233, 126, -63, 178, 9, -67, -41, -122, 33, -100, -149, 450, 266, 87,
  71, 111, -158, -155, -249, -60, -115, -188, -148, -289, -314, -356, 126,
  -28, -35, -12, 84, 145, 367, -102, 116, 38, 28, -92, -164, -174, 2, -128,
  360, 398, 263, -122, -167, 310, 26, 254, -38, -273, 14, -95, -214, -49,
  51, -380, -137, -24, 92, -37, 68, 99, 131, 60, 161, -82, -44, -139, 67,
  -104, 20, 76, 129, -76, -64, 324, -72, 230, 2, -43, 50, 347, 55, 5, 160,
  5, -98, -138, 22, 36, -144, -240, 97, -136, 136, 115, 23, 263, 42, -2, 13,
  -67, -9, 74, 11, 154, -10, -159, 18, 41, -29, 130, 277, 22, -104, 129, -4,
  93, 99, 57, 76, -262, -182, 21, 84, 123, 132, 13, 188, -108, 151, 272,
  235, 47, 33, 94, 84, 149, 382, 101, 35, 81, -133, 47, 240, -29, 4, 0, 261]

theorem fractionalNearFrameSubtreeG1R0153_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0153Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0153Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0153Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0153_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0153LowerBoundTable : List ℤ :=
  [172, 647, 118, 196, 486, 534, -193, 79, 240, 816, 486, 480, 258, 787,
  -676, 3, -371, 630, -54, 396, 438, 1308, 708, 588, -108]

def fractionalNearFrameSubtreeG1R0153LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0153Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0153LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
