import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0066`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0066Mask : ℕ := 5018636322161030

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0066Witness : Array ℤ :=
  #[65, 146, 0, 64, 59, 144, 162, 73, 39, 63, 0, -86, -128, -48, -18, -190,
  -135, -157, -208, -69, -101, 9, -33, 9, 1, -2, 9, 103, 182, 113, 274, 199,
  0, -84, -36, 46, 65, -43, 0, -44, -35, 100, -1, 43, 18, 121, 26, 25, -21,
  30, 46, -2, 70, 0, 24, 129, 94, -140, -96, 0, -69, -10, 42, 97, 33, 106,
  60, 47, 32, 50, 63, 74, -34, 24, 76, -67, 49, 75, -16, 70, 120, 107, 64,
  88, -3, 33, 40, 48, 58, 17, 45, 47, 115, 106, 41, -14, -30, 19, 47, 113,
  77, -12, -94, -7, 0, -10, 116, 80, 25, 49, 89, -14, 105, 52, 5, 11, -136,
  -30, 50, -108, 3, -57, 90, -41, -43, -29, -16, 34, 95, -63, 87, 95, 96,
  -79, -20, -90, 101, -83, 117, -91, -2, 83, -22, -59, -17, -37, -13, -25,
  11, 69, 128, -13, 68, -37, -93, -50, 111, 16, 62, -118, -50, -40, -57,
  -37, -69, 62, -36, 131]

theorem fractionalNearFrameSubtreeG5R0066_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0066Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0066Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0066Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0066_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0066LowerBoundTable : List ℤ :=
  [180, 13, 246, 224, 2, 291, 409, 243, 102, 279, 9, 142, -106, 247, -67,
  152, 238, 228, 624, 336, 361, 108, 557, 517, 326]

def fractionalNearFrameSubtreeG5R0066LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0066Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0066LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
