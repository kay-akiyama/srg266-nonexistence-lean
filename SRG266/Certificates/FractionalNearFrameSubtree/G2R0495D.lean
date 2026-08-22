import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0495`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0495Mask : ℕ := 5811315853972756

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0495Witness : Array ℤ :=
  #[245, -118, 257, 158, 133, 48, 35, 204, 51, 9, -24, -112, -312, -195,
  -105, -58, 150, -109, 63, 65, -168, -38, 100, 17, -52, -107, 37, -115,
  136, 91, 180, 203, 75, 46, -99, -102, 0, -44, -151, -26, -170, 90, -167,
  -62, -60, -88, -186, 85, -51, 215, 263, 247, -112, -116, 79, 112, 161,
  -43, -23, 111, 52, 28, 1, -41, -105, 60, 0, 93, -30, 65, 107, 17, 31, -66,
  -42, -39, -149, -4, -275, 204, -92, 139, -113, -53, 67, -185, 76, 89, 42,
  203, 329, -95, -257, 106, -166, 297, -1, -78, 5, 57, 114, 89, -77, 44,
  111, 29, 62, 61, -131, -101, 194, -41, 60, 31, -13, 134, 104, -43, 86, 55,
  171, 7, 104, 85, -86, 41, 127, -22, 72, -43, -44, 110, 1, 135, -54, -12,
  -91, 171, 166, -29, 8, 153, 157, 37, 92, 15, 156, -37, 122, -31, 136, 32,
  68, 243, 17, 218, 55, 373, -70, -56, 50, 14, 106, 76, 33, 206, 113, 13]

theorem fractionalNearFrameSubtreeG2R0495_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0495Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0495Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0495Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0495_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0495LowerBoundTable : List ℤ :=
  [253, 672, 344, 393, 400, 105, 1, 238, 410, 635, 672, 424, 650, 537, -176,
  -208, 199, 931, 464, 816, 767, -331, 206, 121, 486]

def fractionalNearFrameSubtreeG2R0495LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0495Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0495LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
