import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0310`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0310Mask : ℕ := 5388109136642450

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0310Witness : Array ℤ :=
  #[7, 47, -26, 28, -91, -131, -64, 36, -87, -21, -14, 61, -21, 120, 181,
  -339, 77, 156, 14, 36, 16, 29, 107, 10, -4, 30, -65, -164, -82, -277, -48,
  -124, -70, -50, 70, 72, 25, -57, -143, 80, 12, 410, 34, 62, 36, -1, 100,
  -118, -104, -184, 33, -53, -5, 132, 212, -175, -124, -94, 49, 51, 72, -22,
  -74, 102, 100, 87, -428, -115, 64, -30, -55, -64, 21, 28, -12, 350, -32,
  70, 30, -31, 128, -50, -37, -19, 137, -53, 52, 21, 31, 84, 73, -23, -155,
  244, -215, 66, -110, -29, 107, 71, 116, 90, -92, 44, -140, -74, -40, -31,
  44, 78, 40, -180, 227, -62, -50, -37, -121, 31, 107, -62, -118, 47, -33,
  64, 80, -15, 18, 5, 27, -62, -2, 107, -95, -372, 43, 6, -24, 22, 247, 38,
  -8, 79, -87, -101, -35, 151, 15, 10, -48, -75, 170, -301, 130, -289, 408,
  -13, 199, 55, 83, -185, 136, 111, 361, -87, 180, -131, -199, 246]

theorem fractionalNearFrameSubtreeG2R0310_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0310Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0310Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0310Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0310_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0310LowerBoundTable : List ℤ :=
  [-89, 158, 256, -182, -244, 37, -14, -60, 213, 254, -202, 28, 464, -40,
  117, 9, 436, 245, 11, -118, 361, 10, 11, 122, 167]

def fractionalNearFrameSubtreeG2R0310LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0310Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0310LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
