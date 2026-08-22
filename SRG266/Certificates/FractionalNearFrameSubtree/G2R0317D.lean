import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0317`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0317Mask : ℕ := 5389414909418152

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0317Witness : Array ℤ :=
  #[48, -390, 452, 214, 222, 57, -702, -333, 577, 127, -617, -116, 124,
  -142, -294, -364, 208, -392, -326, 702, -490, 121, 98, 37, 589, -364, -77,
  775, -103, -424, 462, 165, -277, 621, 573, -10, -856, -487, 273, 540, 208,
  -211, -322, 210, -113, -472, 533, 627, 393, 788, 231, -33, -428, 0, -298,
  822, 922, 480, 412, -285, -42, -599, -764, -309, -52, -296, -11, -796,
  -252, -386, 615, 609, -121, 713, -534, 338, -531, 922, 387, 221, -50,
  -401, 113, -53, 223, -190, 216, -381, 619, -31, 66, 572, 216, 35, -147,
  655, 51, -395, -169, -507, 190, 77, 0, -308, -365, -204, 672, 647, 348,
  813, -221, -552, -1171, -322, -897, -301, 250, -511, -254, 333, 1056, 581,
  -924, 82, 15, 602, 161, 16, 89, -47, 237, 300, -282, 10, -303, -330, -31,
  460, 104, 161, 342, -364, -891, 586, -223, -181, 34, -29, -765, -248, 171,
  299, -423, 638, 507, -566, -440, -357, -232, -188, -338, 45, -138, 175,
  815, -35, -1004, -51]

theorem fractionalNearFrameSubtreeG2R0317_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0317Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0317Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0317Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0317_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0317LowerBoundTable : List ℤ :=
  [-576, -690, -530, 32, -704, 33, 876, 32, -61, 1882, 395, 100, 1026, -103,
  1028, -944, 383, -1302, -520, 2490, 1461, 179, -659, 2615, 969]

def fractionalNearFrameSubtreeG2R0317LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0317Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0317LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
