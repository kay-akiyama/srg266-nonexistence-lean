import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0000`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0000Mask : ℕ := 520947763216451

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0000Witness : Array ℤ :=
  #[88, 38, 41, -78, 5, -59, -25, -40, -24, -62, -28, -24, 3, 39, 0, 16,
  130, 15, -158, 159, 54, -32, 6, 0, 62, 28, 52, -62, -89, 4, -42, -53, -21,
  -39, -123, -50, -52, -108, 0, 23, 86, 146, -74, 0, -69, 32, 63, 128, -16,
  103, 90, -47, -43, -49, -24, -5, -37, 44, 109, 39, -17, 85, 0, -39, 58,
  35, -140, 124, 105, -9, 102, 62, 170, 107, 151, -13, -7, 128, 44, 10, -36,
  -37, 146, -37, -69, 56, 94, 40, 89, -41, 103, 33, -38, -30, -12, 81, 91,
  24, -17, 138, 130, -5, 59, 73, 5, -219, -203, -79, -24, -41, -131, -17,
  -58, 113, 67, 2, -199, -143, -59, -24, -66, 56, -79, -59, -27, -148, -117,
  103, 70, 45, -60, 15, -74, -21, -22, -29, 95, -37, 54, -22, -69, 71, 23,
  56, 48, 24, -24, -48, 86, 32, -31, 22, 32, -59, -213, -125, -101, -37,
  -121, -88, -157, -95, -61, 21, 0, -5, -82, -8]

theorem fractionalNearFrameSubtreeG5R0000_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0000Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0000Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0000Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0000_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0000LowerBoundTable : List ℤ :=
  [-149, -329, -35, 132, 3, 20, 89, -46, 31, -143, -95, -470, -347, 186,
  273, -136, -158, -175, 11, 460, -152, 358, 146, 17, 151]

def fractionalNearFrameSubtreeG5R0000LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0000Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0000LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
