import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0059Mask : ℕ := 758344945420809

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0059Witness : Array ℤ :=
  #[1574, 427, 2143, 804, 1125, 211, 495, -524, 1064, 1081, -524, 250,
  -1119, -811, -2433, -856, -1554, -1989, 808, -1695, -1755, -1333, -1153,
  1480, 104, -765, 209, -464, 912, 1480, 607, 1374, 521, 375, 250, 353, 988,
  349, -503, -360, -676, -997, -620, 737, 0, -765, -1319, 28, -391, 305, 1,
  -495, 247, 14, 199, 866, 53, -476, 105, -639, -195, -778, 301, 211, -162,
  97, 2089, -986, -668, -630, 654, 57, 1034, 74, -1187, -628, -733, -488,
  673, 344, -7, -281, -699, 529, 294, -922, 503, -276, 566, 37, 558, 847,
  494, 463, 521, 143, -38, -418, 796, 474, 361, 1059, 515, 546, 1025, 625,
  403, 618, 325, 452, 367, 308, -45, -211, -87, 358, -187, -1406, -158, 269,
  119, -632, -1146, 581, 907, 351, 365, -290, -276, -13, -153, -202, 1678,
  578, -295, -559, -405, -1700, 563, -22, -474, 525, -1669, 17, 343, 336,
  782, -494, 502, 6, -660, 212, -967, -186, -86, 1250, 339, 1341, -1175,
  131, 917, 2117, 152, -415, -1155, -285, 1471, 808]

theorem fractionalNearFrameSubtreeG1R0059_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0059Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0059Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0059Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0059_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0059LowerBoundTable : List ℤ :=
  [-6, 973, 1148, 32, 726, 1379, 33, 32, 1172, 794, 2744, -11, -3588, 3139,
  1522, 682, -1089, 2273, 166, 777, -2078, 2969, 101, 2350, 99]

def fractionalNearFrameSubtreeG1R0059LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0059Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0059LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
