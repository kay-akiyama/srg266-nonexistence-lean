import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0102`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0102Mask : ℕ := 2521293596332644

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0102Witness : Array ℤ :=
  #[186, 387, -1098, -1093, 109, 304, 1177, -390, 807, -711, 646, 450, 200,
  865, -1352, 1848, -62, 654, -403, 67, -203, 386, 1422, -525, 229, 35, 406,
  0, -543, 557, -207, -1106, -25, -18, -16, 90, -130, 181, -124, -494, -573,
  -215, -1545, 0, 30, -791, 151, 441, 88, 83, 37, -43, 218, -157, -1405,
  -1186, -770, -708, 354, -326, -647, -28, -589, 503, 760, -1563, 78, 1764,
  -304, 196, 246, 683, -710, -949, -654, 1497, -1298, 409, -840, 277, 697,
  910, 241, -520, 496, -142, 986, 1513, 762, -94, -379, -1257, 98, -66, 718,
  775, -101, -429, 379, 455, -373, -375, 129, -212, -816, -593, 11, 95,
  -557, 987, -4, 69, 178, -370, -1324, -575, 627, -1146, -442, 47, 735,
  1163, 867, 226, 521, -456, -1513, -1873, 316, -99, 213, 625, -1251, 314,
  531, 296, 87, -229, -388, -473, 75, -24, 704, 260, -132, -66, 1161, 189,
  623, 993, 384, -670, -285, 386, -324, 631, -489, -17, -53, 231, 2089,
  -203, 2985, 779, 708, 175, 308, 1144]

theorem fractionalNearFrameSubtreeG3R0102_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0102Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0102Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0102Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0102_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0102LowerBoundTable : List ℤ :=
  [-1096, 1759, 32, 725, 1075, 32, 1327, -489, -545, 100, 4446, 100, 98,
  1200, 100, 100, -1559, 4742, 100, 689, -4387, 2489, 4402, 101, 1148]

def fractionalNearFrameSubtreeG3R0102LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0102Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0102LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
