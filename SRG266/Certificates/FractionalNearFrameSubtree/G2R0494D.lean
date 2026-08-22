import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0494`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0494Mask : ℕ := 5811310477039124

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0494Witness : Array ℤ :=
  #[650, -590, 0, 513, 304, -848, -1564, -396, 138, -455, 48, 100, 101,
  -163, 358, 793, -382, -463, -129, 192, 254, 134, -825, -448, -594, -92,
  193, 584, 499, 779, 307, 344, 1116, 1032, -1400, 249, -401, -635, -61,
  191, -466, -239, -112, -558, 915, 454, -534, 211, 693, -530, -211, 72,
  -150, -139, 1072, -60, 684, -112, -243, 192, -198, 663, -46, 1088, 205,
  -25, -192, 485, -815, -258, 352, -319, -333, 958, -42, 220, 34, 733, -143,
  -103, 300, -636, -461, 354, 404, 107, 1810, 180, -326, 751, -123, -1106,
  477, 438, 481, 1, -1026, -410, -361, 320, 659, 177, -183, 692, 616, 285,
  -1110, -727, -565, 1043, 1, -479, -884, -210, 586, 534, -34, 568, 1019,
  -161, 138, -48, -715, -272, 272, 185, 620, -844, -105, -451, 965, 356, -3,
  -337, 781, 352, -752, 158, 1428, 552, 278, -42, 454, 499, -144, -537, 439,
  -182, 684, 150, -114, -799, 667, 415, -71, -971, -146, 56, 29, 83, -408,
  852, -145, -324, -220, 50, -728, -688]

theorem fractionalNearFrameSubtreeG2R0494_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0494Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0494Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0494Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0494_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0494LowerBoundTable : List ℤ :=
  [-375, 1189, 31, 929, 33, -44, 33, 33, 736, 100, 692, 1981, 3250, 1492,
  -94, 1374, 2741, 121, 492, 1529, 3220, -239, 101, -827, 101]

def fractionalNearFrameSubtreeG2R0494LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0494Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0494LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
