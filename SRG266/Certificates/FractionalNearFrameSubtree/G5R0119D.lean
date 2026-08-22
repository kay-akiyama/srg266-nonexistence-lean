import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0119`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0119Mask : ℕ := 5794205435075105

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0119Witness : Array ℤ :=
  #[109, -648, 421, 286, -61, -293, 840, -294, 683, -512, -390, 392, -1037,
  105, 0, 89, -358, -120, 195, 247, 555, -932, -69, -110, -229, 92, -48,
  550, -233, -265, 726, -124, 544, 657, 68, -1146, -360, 604, -52, -653, 87,
  -43, -77, 661, 1013, 517, 609, 59, -153, 654, -336, 290, 850, 366, -1187,
  90, 662, 613, -601, -543, 226, 170, -944, 130, 843, -735, 355, 251, 176,
  370, 241, 628, 388, -695, -261, 120, 506, -310, 616, 143, -710, 656, 18,
  439, -55, -192, 33, -614, -288, 231, -190, 540, -210, 676, -1010, -630, 4,
  -191, 667, -108, 60, 1152, -1003, -51, 484, -574, -19, -194, 256, 540,
  -270, -1051, 869, 399, -292, 382, 69, 460, 624, 795, 199, -939, -1614,
  -786, 1254, 725, -1197, -768, 631, 332, 845, -167, -1064, -32, -409, 466,
  172, 592, -467, 182, 411, -889, 1021, -504, 1607, -685, 452, -104, 265,
  -45, -92, 105, 1011, 655, 181, 482, 284, 389, -640, 582, 946, 266, 67,
  871, -735, 749, -704, -71]

theorem fractionalNearFrameSubtreeG5R0119_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0119Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0119Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0119Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0119_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0119LowerBoundTable : List ℤ :=
  [411, 1403, 1388, -121, 1344, -1403, 894, 124, 1859, 2588, 99, 1724, 3950,
  101, 1576, 1713, 2921, 99, -543, 1762, -578, 957, -2205, -2263, 4485]

def fractionalNearFrameSubtreeG5R0119LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0119Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0119LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
