import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0005`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0005Mask : ℕ := 944037882200131

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0005Witness : Array ℤ :=
  #[262, 298, -366, -127, -634, -307, 260, 91, 306, 64, 26, 250, 196, 200,
  -114, -270, 201, -72, -323, 162, -301, -438, 296, 91, 593, -321, -339,
  184, 140, 0, 90, 390, -236, 66, -577, -111, -422, -351, 570, 234, 212,
  385, 186, 353, 463, -248, -352, 577, -91, 31, -4, 240, -199, -417, -457,
  -554, 42, -76, 24, -171, -579, 12, -43, 15, -566, -850, -167, 117, -234,
  191, 120, 618, 561, 26, 176, 278, 431, 128, 353, -365, 190, -393, -251,
  -442, -73, 284, 75, 372, -193, 523, -96, -71, 255, 792, 621, -149, 426,
  84, 288, 267, 179, 189, 606, 317, -351, -364, 449, -528, -392, -330, -102,
  -291, -3, 474, -342, 198, -114, 559, 226, 219, 771, 15, -538, 600, -106,
  344, -390, -520, 443, -126, -306, 682, 125, 291, 144, 15, -263, -968,
  -416, 162, -163, -78, -18, -109, -207, -812, 703, -21, 28, 704, 717, -484,
  -51, -325, -99, -19, 318, 39, 585, 21, -82, -83, -861, -443, 120, 692,
  640, 31]

theorem fractionalNearFrameSubtreeG4R0005_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0005Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0005Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0005Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0005_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0005LowerBoundTable : List ℤ :=
  [-543, 1, 218, 267, -419, 1491, 366, 944, -486, 1834, 153, 1065, -2511,
  188, 285, -161, -712, 667, -951, 9, -468, -536, 2032, 2778, 1934]

def fractionalNearFrameSubtreeG4R0005LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0005Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0005LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
