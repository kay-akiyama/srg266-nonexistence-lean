import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0297`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0297Mask : ℕ := 5387182188123668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0297Witness : Array ℤ :=
  #[361, 109, 302, -307, 326, -1, 275, 369, -149, 161, -189, 2, 176, -15,
  -432, -351, -390, -227, -153, -548, -201, -203, -13, 48, -17, 168, 279,
  220, 556, 345, 39, -102, -128, -424, 507, 392, -327, -226, 250, 439, 571,
  -503, -173, -314, 125, -80, 388, 398, 0, 283, 280, -212, 79, -284, 763,
  138, 188, -229, 53, 84, 172, -401, -95, -453, 391, -83, 84, 819, 215, 323,
  -709, 203, 428, 30, 31, 432, -369, -195, -193, 103, 551, 505, 405, 422,
  183, 6, -457, -477, 297, 354, 14, 241, 280, 78, -179, -157, -23, -148,
  -117, -169, 478, 201, 525, 0, -102, -113, 112, 283, 495, -137, 17, -176,
  540, -22, 137, 635, -52, 372, -322, -224, 250, 387, 266, -147, -73, -539,
  50, 130, 174, 388, 241, 458, 448, -236, -39, 467, 425, 377, 489, 277, 268,
  218, -191, 42, 65, 310, -157, 582, 183, 442, 302, -75, -314, 0, 33, 124,
  -42, -352, -87, 125, -254, 512, -59, 601, -300, 263, -196, -78]

theorem fractionalNearFrameSubtreeG2R0297_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0297Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0297Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0297Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0297_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0297LowerBoundTable : List ℤ :=
  [721, 1298, 664, 491, 592, 482, 798, 1110, 803, 1135, 3320, 1716, 791,
  965, 1132, 357, 1249, -77, 2013, -35, 733, 668, 1359, 1977, 1718]

def fractionalNearFrameSubtreeG2R0297LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0297Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0297LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
