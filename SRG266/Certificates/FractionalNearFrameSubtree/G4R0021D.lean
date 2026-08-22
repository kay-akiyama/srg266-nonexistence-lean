import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0021`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0021Mask : ℕ := 4887100083775777

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0021Witness : Array ℤ :=
  #[53, 87, -9, 85, 36, 36, 5, -9, -23, -22, -37, 0, 24, 33, -39, -90, -26,
  6, 71, -29, -1, 63, 4, -6, -4, -102, 67, 39, 28, 94, 39, 43, 81, 15, -41,
  -47, -43, -58, 32, 46, 9, -20, -2, 41, -43, 55, 73, -12, -23, 15, 61, 0,
  -20, 1, 17, 48, 63, -69, -84, 63, 14, 7, -53, 25, -55, -37, 26, -36, 42,
  39, 8, -35, 28, 46, 69, 16, 37, 77, 43, -42, 37, 2, 53, -12, -39, -24, 2,
  -72, 2, 31, 29, -34, -15, 5, 6, -24, 15, 67, 5, 3, 55, 32, 42, -32, 62,
  16, -29, 41, -52, -65, -109, -3, 60, 67, 37, 6, -13, -40, -38, -84, -92,
  60, 49, -7, 15, 38, -9, -58, 22, 23, -11, -21, -5, 52, -14, 64, 28, 43,
  14, -13, 18, -27, 44, 51, 5, 3, 15, 29, -27, -21, 1, 40, 24, -38, -47, 17,
  -29, 0, -12, -18, 7, 47, -11, 4, 33, -2, 18, 1]

theorem fractionalNearFrameSubtreeG4R0021_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0021Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0021Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0021Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0021_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0021LowerBoundTable : List ℤ :=
  [25, 3, 81, 4, 2, -17, 138, 121, 125, 36, 71, 310, 57, 9, 271, 168, 292,
  7, 102, 55, -43, 156, 200, 9, 331]

def fractionalNearFrameSubtreeG4R0021LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0021Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0021LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
