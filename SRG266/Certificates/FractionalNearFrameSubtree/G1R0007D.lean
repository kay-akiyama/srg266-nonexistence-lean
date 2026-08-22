import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0007`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0007Mask : ℕ := 260272620691717

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0007Witness : Array ℤ :=
  #[0, 406, 265, 784, 370, 103, 241, -382, -548, -225, -11, -573, -434,
  -933, -323, -963, -405, -970, -922, -1038, -455, -1216, -308, 731, 883,
  161, 390, -653, -316, -133, 372, 1095, -984, -154, -111, -452, 372, 512,
  -361, 369, 1046, 443, -53, -514, -102, -464, -889, 1631, -18, 610, 883,
  57, -297, 1439, 700, 499, 396, -94, 504, -1431, -366, 974, 1435, -572,
  -1237, 1190, -764, -201, -479, 128, 977, -295, 866, 421, 366, 481, -248,
  442, 148, 162, -117, -84, 89, 453, -84, -326, 16, 274, 1011, -332, -594,
  1482, 771, 12, 430, -651, 736, -268, -545, -173, 500, 341, -475, 12, -104,
  -620, 346, -208, -621, -464, -714, -334, -861, 23, -655, 778, -131, 392,
  -248, 636, 527, 96, -221, 303, 621, 33, 289, 187, 849, 0, 177, 566, -291,
  -136, 1489, 38, 597, 1119, 717, -445, -150, 592, 30, 1655, 189, 543, -362,
  421, 1874, 426, 83, 447, 297, 484, 322, 248, -1227, -93, -1143, -266,
  1125, -482, 82, 799, 1104, 167, 387, 596]

theorem fractionalNearFrameSubtreeG1R0007_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0007Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0007Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0007Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0007_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0007LowerBoundTable : List ℤ :=
  [17, 3029, 1251, 1091, -1025, 997, 38, 767, 2114, 3912, 2297, 3058, 900,
  2119, 1036, 3492, 3179, 1307, 1872, 2672, 1639, -1705, -178, 958, 99]

def fractionalNearFrameSubtreeG1R0007LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0007Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0007LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
