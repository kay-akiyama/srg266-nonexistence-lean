import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0608`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0608Mask : ℕ := 7057474578781730

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0608Witness : Array ℤ :=
  #[717, 457, 570, 173, 221, 856, 353, 0, 477, -320, -104, -644, -269, -865,
  -837, -693, 179, -209, 217, -115, 88, -192, -378, 93, -143, 131, 81, 534,
  339, -76, 81, 521, 177, 80, -416, -30, 100, -352, 635, -570, 7, -450,
  -241, -44, -99, 69, -13, 16, -62, 111, -59, -185, 580, 210, -355, -90,
  473, 124, 321, -106, 111, -450, -66, -316, -179, 153, 12, 432, 193, -86,
  -322, -479, -345, -22, 167, 32, -590, 123, 150, 307, 366, 94, 562, 90,
  197, 331, 33, -23, -180, -79, -31, -582, -31, 69, -27, -407, 90, -270, 59,
  -875, -53, -581, 29, 69, 540, -118, -4, -36, 463, -70, 391, -380, -309,
  -133, -370, 543, 235, 556, 192, 977, -239, -63, -337, -612, 709, -211, 59,
  486, 386, 431, 54, 464, 201, -428, -86, -55, -72, 300, 0, -943, 57, -83,
  -206, 200, 364, 94, 569, 434, 228, 16, 193, 188, -86, 826, -287, 610, 0,
  415, 437, 702, 613, 293, 255, 262, -52, 370, 80, 62]

theorem fractionalNearFrameSubtreeG2R0608_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0608Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0608Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0608Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0608_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0608LowerBoundTable : List ℤ :=
  [55, 1506, 2, 462, 2, -390, 345, 115, 535, 2179, 2926, 973, 1705, 1419,
  1361, -683, 10, 1202, -634, 721, 1016, 482, 639, 1140, 1339]

def fractionalNearFrameSubtreeG2R0608LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0608Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0608LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
