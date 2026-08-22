import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0481`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0481Mask : ℕ := 5810340903109778

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0481Witness : Array ℤ :=
  #[-104, 471, 847, 586, -235, 451, -556, -268, 193, 0, 162, -906, 41, -785,
  580, -142, -60, 545, 1184, 1003, 566, -908, 77, 13, -1119, -273, -181,
  -323, 29, 351, -598, -265, 100, 580, 1282, 319, -77, 431, 585, -50, -448,
  572, 98, 18, 12, 255, 656, 655, 576, 205, 195, 196, 360, -41, 1400, -157,
  57, -213, 1077, 1126, -1364, -271, -829, -70, 525, -451, 705, -1033, 328,
  -200, -322, 241, -15, -543, -142, -508, 669, -137, -46, 342, 124, 189,
  -40, 745, -236, -253, 505, 427, 14, 511, 566, -295, 109, 1984, 125, 786,
  36, -243, -449, 578, 139, 304, -165, -23, -459, -285, 730, -369, 302, 36,
  772, 153, 40, -494, 71, 136, 986, -124, 776, -706, -349, -38, 746, 234,
  -30, 558, -555, -712, -537, 642, -184, 82, 328, 166, 344, 171, -29, 263,
  -465, 550, -358, -6, -561, 416, 184, -198, -517, -731, 702, -665, 299,
  -814, 673, -31, -404, 235, -12, 140, -170, 292, 0, -135, 474, -180, 1269,
  -308, -413, -814]

theorem fractionalNearFrameSubtreeG2R0481_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0481Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0481Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0481Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0481_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0481LowerBoundTable : List ℤ :=
  [247, -211, -143, -36, 1956, 1947, 32, 1372, 493, 2229, -975, 649, 1533,
  1083, -813, 100, 431, 637, 3962, 4126, 1842, 1978, 3162, 899, 5480]

def fractionalNearFrameSubtreeG2R0481LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0481Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0481LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
