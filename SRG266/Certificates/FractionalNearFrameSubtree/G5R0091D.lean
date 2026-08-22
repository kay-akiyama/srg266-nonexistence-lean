import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0091`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0091Mask : ℕ := 5509293184557458

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0091Witness : Array ℤ :=
  #[150, -153, -68, -10, -130, 173, 0, 17, -124, 113, 0, -248, -19, -55,
  -214, 41, 83, -213, -147, 3, -118, 175, 10, 99, -194, 87, -223, 137, -24,
  5, 64, 172, 243, -133, 1, -20, -196, 194, 68, -176, 8, -240, -34, -78,
  -211, 82, 18, -173, -65, -57, 0, 341, -98, 20, 113, 195, -12, 83, 35, 110,
  39, 155, 82, -196, -144, -315, -141, 34, 99, -113, 12, -61, 158, 48, 31,
  167, 152, -80, -142, 290, -193, 81, -15, 130, 13, 19, 106, -105, -217,
  152, -149, 47, 41, 109, 218, 21, -47, -200, -66, -265, -66, 108, -52, 8,
  25, -110, 137, 16, 76, -123, 41, -98, -29, -25, -158, 84, 245, 62, 140,
  28, -106, 108, 71, 172, 174, 218, 55, -49, -189, 194, 174, 142, 217, -153,
  -275, -134, 539, -94, 384, 468, -124, 79, -6, -211, 168, 166, 281, -165,
  252, 112, 64, -38, 45, 223, -21, -191, -1, 48, -45, 37, 301, 374, -342,
  34, -36, 208, 0, 177]

theorem fractionalNearFrameSubtreeG5R0091_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0091Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0091Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0091Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0091_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0091LowerBoundTable : List ℤ :=
  [57, 690, 102, 212, 412, 1, 134, -213, -115, 806, 647, 749, 382, 662, 766,
  -116, -386, 95, 95, 9, 147, 729, 36, 59, 11]

def fractionalNearFrameSubtreeG5R0091LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0091Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0091LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
