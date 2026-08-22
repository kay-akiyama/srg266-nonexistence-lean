import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0099`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0099Mask : ℕ := 1247503191089249

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0099Witness : Array ℤ :=
  #[21, 563, -584, -676, 0, 209, 991, 559, 326, 103, 127, 266, -945, 24,
  -185, -351, 503, -300, -15, -1056, 427, -183, -708, 1319, 471, -646, -385,
  -453, 795, 888, 774, 370, 183, -645, -889, -67, -375, 492, 693, -528, 0,
  794, 427, 955, 729, -115, 31, 505, 167, -179, 1056, 438, -639, 35, 764,
  1001, 131, -389, 64, 119, 114, 729, 597, -642, -395, -570, -245, -140, 13,
  -318, 44, 237, 26, 1101, 153, -224, 154, 358, -208, -407, 214, 124, -12,
  719, -28, 266, 417, -135, -52, 1623, 581, 219, 23, 255, 772, -71, 69, 14,
  69, 1668, 173, 97, 348, 178, 258, 449, -361, 564, -326, 301, 1023, -136,
  0, -1709, -877, -1436, -1939, -1392, 573, 997, -635, -68, -1076, -134,
  344, -536, 153, 449, 526, 885, -76, -47, 532, -22, 17, 273, -245, 30,
  -270, -83, 240, 356, 228, -70, -349, 470, 283, -131, 7, 411, -526, 201,
  -130, 76, 539, 0, -217, -39, 260, 419, 100, -97, 207, -61, 52, 53, 118,
  505]

theorem fractionalNearFrameSubtreeG2R0099_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0099Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0099Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0099Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0099_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0099LowerBoundTable : List ℤ :=
  [183, 9, 1259, -258, 859, 3586, 569, 418, 947, 2913, 695, -1490, 822, 100,
  4142, 101, 1429, 1611, 2175, 683, 1903, 101, 65, 1609, 4468]

def fractionalNearFrameSubtreeG2R0099LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0099Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0099LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
