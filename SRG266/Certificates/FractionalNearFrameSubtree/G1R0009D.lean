import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0009`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0009Mask : ℕ := 260478766532881

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0009Witness : Array ℤ :=
  #[111, 147, 106, 158, 113, 251, -259, -210, -65, -77, -248, -206, -128,
  45, 83, 243, -37, 0, -2, 18, 33, 20, -70, 191, -14, -7, -43, -46, -10,
  -19, 83, -157, -90, -55, -133, -38, 73, -33, 34, 147, -31, 114, 124, -39,
  40, -103, -125, 0, 149, 96, 63, -94, 99, 67, 64, -121, -9, -119, 57, -26,
  -124, 206, 79, 0, -186, 7, -30, -80, 19, -99, 32, 148, 39, -135, 42, -28,
  -127, 6, -95, 90, 23, 1, -18, -17, 24, 124, 20, -129, -10, 11, -6, 284,
  65, -48, 192, -208, 47, -158, -167, 60, -34, -80, -8, -2, 59, 110, -65,
  17, 64, 38, 103, -192, -116, 50, -132, 176, -177, -98, 120, -28, -94, 150,
  21, -47, 90, 173, -41, -62, 162, 174, 5, -131, 97, 142, -73, 68, -47, 232,
  39, 92, 54, -33, -19, 13, -45, 151, 24, 40, 134, -91, 38, 136, -178, 53,
  -133, -172, 107, 30, 58, -25, 70, -69, -13, -146, -21, 55, -27, 98]

theorem fractionalNearFrameSubtreeG1R0009_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0009Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0009Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0009Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0009_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0009LowerBoundTable : List ℤ :=
  [-115, 181, -1, -184, 217, 2, 141, 179, 70, 24, 342, 8, -96, 863, -161,
  10, -67, 10, -368, 133, 416, -240, 289, 9, 10]

def fractionalNearFrameSubtreeG1R0009LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0009Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0009LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
