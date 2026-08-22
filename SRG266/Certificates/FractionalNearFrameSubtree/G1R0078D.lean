import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0078`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0078Mask : ℕ := 898798982908425

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0078Witness : Array ℤ :=
  #[-6, 291, 291, 1, 687, 204, -98, -758, -152, 0, 225, 182, -506, 134, 61,
  0, -434, -435, 668, 262, 22, -586, -143, -478, 26, -513, 172, -305, 482,
  370, 440, 1156, 261, 351, -225, 23, -787, -750, 355, -730, -30, -183,
  -335, -578, 1190, 262, 475, 45, -444, 70, -520, 1346, -983, -897, 55,
  -370, 323, -54, -410, -144, 500, 895, -563, -721, 419, 288, -538, 239,
  -189, 900, 246, -408, -590, 47, 480, -759, 50, -1022, 376, 1085, -506,
  -496, -176, -203, 36, 806, -87, -13, 443, -244, 19, -131, -224, 449, -21,
  273, -624, 120, -1135, 355, 227, 369, -773, -250, 67, 746, -540, 741, 192,
  679, 801, -506, 249, 126, 259, 321, 270, 425, 769, 928, -1059, 89, 134,
  691, -539, 478, -469, -481, 1233, 1100, -282, -429, -131, -225, 272, 123,
  -1133, 335, -961, 190, -471, 277, -189, -78, -58, -460, -624, 1270, 716,
  94, 223, -718, -78, 116, 606, 42, -673, -5, -83, -730, -114, -177, -38, 4,
  397, 615, 96, -1271]

theorem fractionalNearFrameSubtreeG1R0078_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0078Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0078Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0078Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0078_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0078LowerBoundTable : List ℤ :=
  [-531, -151, -114, 32, -173, 427, 33, 31, -109, 1550, 351, -25, 436, -164,
  2183, 2002, -1123, 56, 1499, 515, 100, -1387, 2759, -1273, -1215]

def fractionalNearFrameSubtreeG1R0078LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0078Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0078LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
