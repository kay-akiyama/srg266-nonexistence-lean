import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0151`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0151Mask : ℕ := 6850219856940556

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0151Witness : Array ℤ :=
  #[-118, -2175, -1247, 0, -999, -942, 454, 269, -225, -336, 1085, 1017,
  163, 327, 745, 1163, 1139, -921, 322, 23, 177, -78, 1357, 716, -413, 1877,
  -551, -1082, -1224, -1029, 603, 447, 864, 830, -555, -1297, -539, -146,
  22, -394, -1470, -737, -518, -1125, -359, -15, -204, 1606, 535, 1377,
  -1015, -971, 396, 1866, 800, -410, 348, 574, 83, 192, 22, -1217, -102,
  -623, 159, 297, -147, 585, -150, 881, 791, 171, 749, -307, -346, -387,
  -322, 136, -162, -202, -590, 122, 783, 1198, -48, 21, 709, 573, 664, 134,
  405, -490, -107, -181, -188, -172, -707, 542, 982, 692, -165, -197, -426,
  -284, 257, -1643, -680, 63, 985, 73, -243, 517, 703, 476, -726, 111,
  -1074, -904, -447, -951, 304, 242, -1104, 597, 156, 352, 176, 550, -1228,
  -165, 368, 522, -114, 615, -46, 623, -480, 465, 103, 1791, 112, 723, -321,
  181, 866, -176, -1495, -762, -297, -596, 60, -484, 829, 1064, 683, -587,
  641, 1076, 419, -541, 593, 721, 242, 1295, 933, 490, -379, -227]

theorem fractionalNearFrameSubtreeG3R0151_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0151Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0151Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0151Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0151_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0151LowerBoundTable : List ℤ :=
  [146, 1942, 931, 1076, 32, 758, -542, -1291, 2449, 99, -478, 229, 3189,
  320, -2743, 99, 1085, 193, 2177, 101, 4125, 450, -938, 2771, 1427]

def fractionalNearFrameSubtreeG3R0151LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0151Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0151LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
