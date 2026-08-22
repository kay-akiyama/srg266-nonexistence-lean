import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0163`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0163Mask : ℕ := 6855030207585816

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0163Witness : Array ℤ :=
  #[29, -47, -204, -234, -52, 34, -17, -60, 51, -65, 261, 168, 69, 180, 158,
  8, -53, 152, -45, 6, 127, -44, 146, 68, 14, -207, -206, -75, 217, 170,
  106, -72, -203, -98, 9, 44, -21, -156, -65, -9, 128, 76, -74, 135, -113,
  102, 0, 5, 31, -48, 163, 2, -131, 108, -152, 51, -132, -115, -76, 118,
  245, 145, 135, 99, 120, -41, -125, 64, -7, 9, 161, -50, 203, 40, 306, -99,
  -64, -38, -68, 10, 96, 121, -55, -70, 266, 139, 148, -4, -21, 223, 55,
  167, -10, 44, -11, -7, -148, 85, -41, -87, 68, 224, 98, 4, -112, -11, 48,
  -6, 57, -43, 28, -48, -32, 45, 0, 0, -7, -25, 85, -58, -80, 173, 92, 96,
  78, 71, 62, 40, -45, 172, -15, -109, 5, 74, 57, -60, -157, 135, -64, -64,
  -132, -80, 65, -57, 78, -31, -87, 61, -65, 24, 38, 11, 88, 5, -21, 18, 0,
  164, -146, 20, -41, -1, -126, 27, -62, -85, 180, 7]

theorem fractionalNearFrameSubtreeG3R0163_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0163Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0163Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0163Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0163_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0163LowerBoundTable : List ℤ :=
  [44, 1, 423, 256, 187, 2, 188, 169, -37, 77, -12, 550, -52, 480, 607, 461,
  812, 345, 226, 306, 10, 260, 627, 119, -120]

def fractionalNearFrameSubtreeG3R0163LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0163Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0163LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
