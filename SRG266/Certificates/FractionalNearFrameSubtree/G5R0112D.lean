import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0112`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0112Mask : ℕ := 5792761292243203

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0112Witness : Array ℤ :=
  #[438, 82, 221, 56, 462, 579, -771, -284, -429, -518, -466, 250, -108,
  459, 664, 407, 65, 49, 211, -34, 246, 150, -128, -62, 111, 44, 115, 213,
  122, 191, -138, -211, 111, -126, -94, 105, 61, 106, -524, 243, 41, 26,
  560, -194, 6, 267, -276, 224, 324, 257, -421, 0, -212, 312, 296, -110,
  112, 302, -230, 49, 72, -94, 38, 264, 9, -155, 134, -528, 555, 52, 291,
  494, 417, -165, -121, 77, -320, 79, 273, 658, -211, 67, 119, 291, 25, 421,
  -24, 716, 135, -393, 120, -27, 233, 8, -283, 194, -741, 640, 90, 13, -61,
  -64, -230, 125, -179, 210, -174, -672, -298, -235, -119, -583, 32, -35,
  434, 284, -215, 6, -179, 60, -268, 78, 385, -290, -165, 255, 620, -72,
  675, 357, 188, -54, 186, 290, 84, 407, 332, -175, -408, 299, -551, 806,
  -784, 391, -446, 91, -116, -301, -188, 169, 568, 249, 116, 669, -332,
  -137, 48, 0, 136, 14, 361, -114, 16, 451, 64, 166, -234, -595]

theorem fractionalNearFrameSubtreeG5R0112_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0112Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0112Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0112Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0112_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0112LowerBoundTable : List ℤ :=
  [149, 407, 367, 418, 733, 796, 840, 669, 457, 135, 136, 1, -560, -1280,
  573, 1848, 225, 1137, 283, 1266, 1785, 258, 1108, 1372, 1334]

def fractionalNearFrameSubtreeG5R0112LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0112Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0112LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
