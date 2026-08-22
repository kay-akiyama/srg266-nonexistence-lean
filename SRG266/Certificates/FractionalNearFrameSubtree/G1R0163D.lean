import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0163`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0163Mask : ℕ := 2361645046122769

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0163Witness : Array ℤ :=
  #[-832, -46, -409, -719, -84, -470, -1295, -409, -1001, -789, -427, -649,
  1030, 1582, 853, 1695, 1486, 1696, -580, 468, 1118, 318, 42, 572, 686,
  168, 430, 287, -507, -700, -538, 325, -1278, 178, -1111, -1115, -9, 846,
  1078, 1379, 451, -504, -325, 505, 1715, 195, -64, -61, 309, -58, 655, 143,
  -283, 892, 700, 78, 763, 1111, -608, -486, 641, -1606, -939, 592, 487, 0,
  -67, -252, 25, -97, -422, 223, 68, 284, -453, 514, 207, 893, 668, 18,
  -427, -677, 289, 161, -132, -26, 459, 500, 405, -48, -252, 84, -329, -60,
  -1156, -270, -9, -366, 556, 597, 106, -546, 13, 162, 277, -719, 280, 64,
  433, -289, -796, 257, -106, -181, 151, 1145, 199, 1042, 16, -254, 1037,
  162, 62, 1046, 576, -207, 23, 308, -69, 643, 1017, 22, -215, 68, 928, 214,
  636, -206, 419, 427, 109, 651, -401, -215, -122, -883, 103, 135, -497,
  123, 204, 162, -278, -65, -288, -293, -836, -1188, -192, 324, -530, 144,
  -392, 214, -402, 261, 110, -1090]

theorem fractionalNearFrameSubtreeG1R0163_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0163Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0163Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0163Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0163_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0163LowerBoundTable : List ℤ :=
  [395, 32, 500, 576, 438, 1951, 1214, 24, 1196, 409, 1708, 1663, 1509,
  1046, 1277, 1093, 495, 1968, 1763, -1328, 502, 1625, 100, 100, 4116]

def fractionalNearFrameSubtreeG1R0163LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0163Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0163LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
