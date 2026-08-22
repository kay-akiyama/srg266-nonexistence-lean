import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0083`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0083Mask : ℕ := 2372327537619489

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0083Witness : Array ℤ :=
  #[-1218, 0, 211, -207, 754, -619, 698, 120, 2404, 0, -115, 1104, -89, 748,
  -707, -758, 0, 714, 1509, -307, 1676, -723, 0, 541, -1664, -253, 182,
  -868, 309, 267, 1034, 1890, -922, -44, 508, 379, 317, -1425, -104, 368,
  139, 1481, 725, 128, -815, -2354, -257, 832, 829, 718, 1200, 331, 266,
  -127, 1114, 1557, 1037, 912, 1541, 629, -518, -212, -2171, 639, -160,
  -436, -296, -558, -164, -540, 627, 63, 552, 37, -314, -71, 341, 8, 768,
  -583, 660, 686, 357, 974, 766, 401, 1066, -21, -663, -722, 113, 327, 628,
  -389, -376, -757, 704, -332, 840, 1910, 1118, 120, -1803, -870, -1400,
  681, -298, 534, 531, 896, -148, -743, 276, -270, -698, -162, -446, -205,
  668, -814, -220, -294, 871, 1423, 1015, 97, 157, 122, -406, -539, 601,
  172, 243, 1144, 415, 1395, 1557, -1354, -752, 450, -2256, -355, 336, 351,
  9, -352, -794, 71, 598, 182, 448, 1712, -240, 891, -721, 956, 177, 94,
  1130, 1288, -480, -499, -325, 265, 147, 221, -1504, 417]

theorem fractionalNearFrameSubtreeG3R0083_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0083Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0083Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0083Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0083_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0083LowerBoundTable : List ℤ :=
  [1175, 1345, 1040, 1761, 2170, 2658, 2919, -430, 797, 720, 177, 3206,
  1420, 2008, 1128, -2852, 222, 2024, 8224, -698, 936, 1593, 6272, 6410,
  2298]

def fractionalNearFrameSubtreeG3R0083LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0083Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0083LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
