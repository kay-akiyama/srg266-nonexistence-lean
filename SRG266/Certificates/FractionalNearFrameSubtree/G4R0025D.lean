import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0025Mask : ℕ := 5354538506488835

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0025Witness : Array ℤ :=
  #[2, -33, 13, 7, -5, -34, 22, 33, 31, -32, 0, -15, -38, 23, 19, 0, 14,
  -22, -11, 18, 56, 8, -3, -17, -37, -41, -34, 21, -24, 1, 87, -57, -2,
  -106, -27, 54, -28, -13, 48, 0, 4, -19, 2, 46, 20, 31, 67, 0, -15, 25,
  -19, -53, -36, 12, 31, -93, 13, -75, 29, 33, 59, 86, 46, 18, -25, 48, 15,
  30, -13, -3, 17, -4, 27, -46, -10, 32, 1, -106, 6, -36, 52, 31, 45, -4,
  26, -6, 6, 11, -69, -26, -6, 30, -50, 40, 12, -34, -15, 36, 2, -14, -17,
  48, 36, -17, -1, 18, -1, -19, -34, -66, 87, 25, -17, -4, -30, -18, -14,
  11, -58, 76, 55, 8, 10, -12, 0, 30, -36, 24, -60, -50, -11, 3, -22, 17,
  -92, -20, -24, 59, 85, -5, 13, 35, 60, -23, 0, -13, 62, -28, 22, 48, 18,
  -25, 18, 7, -63, 34, 22, 48, -45, 24, 66, -28, -25, -34, 31, 62, -18, 27]

theorem fractionalNearFrameSubtreeG4R0025_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0025Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0025Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0025Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0025_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0025LowerBoundTable : List ℤ :=
  [-32, 76, 2, -4, -29, 57, -19, 22, 50, 212, -47, -87, 9, 37, 229, 35, 160,
  131, -54, -111, 3, 93, 10, 119, 160]

def fractionalNearFrameSubtreeG4R0025LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0025Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0025LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
