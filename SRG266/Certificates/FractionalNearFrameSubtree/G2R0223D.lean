import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0223`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0223Mask : ℕ := 2487830969172642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0223Witness : Array ℤ :=
  #[-246, 39, -485, -72, -424, 21, 900, 314, 822, 21, 775, 26, -704, -650,
  -547, -1124, 162, 222, -341, -478, -665, -174, -41, -260, -766, -1028,
  705, 623, -110, 574, 607, 207, 0, -334, 198, -622, 113, -549, 151, 3, 494,
  -448, 306, -40, -268, -138, 342, 319, -681, -234, -606, -343, 1058, 42,
  81, -122, -223, 297, 224, -1103, -1002, 639, -488, -1334, 473, -64, -4,
  30, 755, -390, 146, -233, 295, -960, 131, -113, -11, -199, 323, -277, 777,
  45, 58, -538, -391, 447, -8, -509, 502, 231, 103, 1027, 112, -989, 821,
  -183, -421, 30, -224, 10, 795, -569, 478, -557, 757, -573, 543, -29, 57,
  450, 525, 334, -34, 144, -532, 618, 266, 629, 104, 487, 612, 130, 853,
  414, 156, -60, 495, -279, -44, 810, -83, 882, 1192, -737, 264, -88, 84,
  -201, 453, -826, -329, 41, 798, 136, -344, 971, 551, 110, 156, -72, -107,
  495, -1, 31, 688, 470, 259, 626, -246, 659, 291, -127, 350, -281, 492,
  164, 0, -239]

theorem fractionalNearFrameSubtreeG2R0223_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0223Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0223Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0223Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0223_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0223LowerBoundTable : List ℤ :=
  [-33, 2648, 371, -964, 1154, -823, 542, 470, 340, 1465, 1549, 2644, 1662,
  3095, 100, 1559, 1390, 453, -1385, 399, 101, 883, 101, 1138, -11]

def fractionalNearFrameSubtreeG2R0223LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0223Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0223LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
