import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0119`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0119Mask : ℕ := 969515606673768

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0119Witness : Array ℤ :=
  #[37, 27, 73, -89, -47, 33, 57, 90, 42, -47, 32, -5, -37, -4, 193, 81, 32,
  -13, -88, 48, -48, 23, 41, -136, 120, -22, 21, 94, 86, 22, 27, 128, -107,
  4, 22, 151, -131, -90, -146, -57, 141, 36, 8, 120, -35, -7, 89, 81, -106,
  -129, -7, 31, 39, -149, -201, -45, 41, 59, 11, 82, 30, 146, 35, -31, -57,
  75, 67, 57, -24, -4, -9, -17, 73, 25, -122, 14, -145, 112, 100, -9, 137,
  -59, 98, -23, -113, 29, 91, 87, 21, 48, 126, -54, -12, 113, -40, -38, 83,
  50, -19, 31, 106, -61, -7, 85, -116, 42, -57, 6, -10, 18, 1, 20, 113, -8,
  26, -49, -52, 78, 28, 16, 71, 114, -28, 145, 152, -34, 46, 6, 63, 21,
  -141, 91, 4, -3, -16, 127, -59, -105, 140, -79, 47, 90, 87, 191, 25, 20,
  70, -16, 31, 127, 39, 17, -18, 67, -27, 117, -77, -133, -7, -14, -152,
  117, 43, -43, -17, 3, -68, 156]

theorem fractionalNearFrameSubtreeG1R0119_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0119Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0119Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0119Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0119_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0119LowerBoundTable : List ℤ :=
  [125, 290, -75, 306, 120, 116, 414, 172, 281, 311, 159, 9, 190, -51, 194,
  -190, 60, 10, 428, 268, 572, 11, 86, 517, 540]

def fractionalNearFrameSubtreeG1R0119LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0119Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0119LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
