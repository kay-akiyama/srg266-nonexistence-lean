import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0274`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0274Mask : ℕ := 5371977207978664

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0274Witness : Array ℤ :=
  #[-313, 241, 374, 96, 248, 107, 340, 117, -318, -262, 376, 414, 49, -141,
  -412, -4, 388, -297, -472, 261, 26, 193, 117, 192, 296, 374, 1389, -449,
  -347, 1350, -94, -110, 60, 281, 413, 177, -48, -1416, 301, 191, 836, -16,
  1276, -4, -473, -236, -105, 433, -68, -1400, -365, 50, 2080, 1124, -409,
  -448, -205, -768, 33, -120, -479, -1171, -227, -48, -538, -336, 98, -119,
  -205, 131, -250, 163, 549, 474, 625, 236, 1472, 60, -364, 148, 246, -558,
  220, 214, 552, -1020, -1183, -41, -870, -139, 479, 149, -653, -1347, 1,
  -211, -80, -129, 112, 15, 102, 1062, -463, 231, 86, 196, 246, -38, -2,
  -324, -1659, 783, 122, 308, 176, 273, 223, 224, -218, -1439, 182, 166,
  272, 232, -205, 363, 303, 569, 356, -27, 244, 293, -124, 497, 1435, 164,
  -157, 107, 991, -25, -275, 52, -264, 322, 20, 353, 259, 570, 314, 1382,
  -428, 631, 392, 207, -116, -1796, 701, 209, 284, 403, -624, 185, -57, 847,
  -88, 579, 418, -354]

theorem fractionalNearFrameSubtreeG2R0274_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0274Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0274Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0274Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0274_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0274LowerBoundTable : List ℤ :=
  [534, 1882, 977, 31, 1098, 32, 503, 625, 31, 3336, 1603, 1798, 791, 2222,
  877, 1688, 425, 226, 991, -270, 915, 100, 1121, 161, 1029]

def fractionalNearFrameSubtreeG2R0274LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0274Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0274LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
