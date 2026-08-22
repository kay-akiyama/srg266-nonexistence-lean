import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0035Mask : ℕ := 5439873267600460

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0035Witness : Array ℤ :=
  #[-25, -222, -115, -248, -263, 170, 75, 33, 45, -36, 99, 0, 98, 194, 4,
  76, 123, 5, -58, 36, -30, 85, 55, -64, -6, -30, 55, -128, 57, 24, 0, 1,
  126, -1, 52, 31, 27, 17, 94, 28, 39, 74, 56, -207, 48, -84, -101, 27, -56,
  97, -5, 76, 154, 20, 135, 7, -6, -28, 5, -104, -137, 45, 23, 45, -28, -3,
  141, 92, 157, -6, 84, 27, -111, -56, -162, 69, 87, 5, -14, -23, 261, -3,
  121, 84, 123, -2, -148, -5, 25, -9, 84, 33, -7, -62, 50, 120, 100, 84, 23,
  41, 12, 9, 221, 75, -10, 67, 77, 68, 28, -5, -101, 24, 17, 48, -110, 62,
  14, -83, 164, 79, -59, -17, 149, -58, -149, -84, 80, 102, 1, -90, -20,
  -11, 156, 12, -35, 104, -12, -48, 78, 2, 134, -132, -51, -53, 171, -12,
  60, -144, -32, -87, -117, -82, 39, -7, -106, 28, -37, 104, 49, 80, -82,
  30, 43, -55, 102, 104, 67, 14]

theorem fractionalNearFrameSubtreeG4R0035_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0035Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0035Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0035Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0035_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0035LowerBoundTable : List ℤ :=
  [76, 2, 293, 2, 2, 329, 108, 2, 251, 651, 251, 163, -111, 394, 358, -163,
  764, 9, -199, 162, 676, 513, 399, 370, 180]

def fractionalNearFrameSubtreeG4R0035LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0035Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0035LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
