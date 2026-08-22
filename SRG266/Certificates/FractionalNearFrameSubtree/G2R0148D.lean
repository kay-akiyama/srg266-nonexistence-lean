import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0148`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0148Mask : ℕ := 1376224864584330

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0148Witness : Array ℤ :=
  #[11, -15, 185, 228, 287, 107, -61, -2, -148, -88, -38, -52, -116, -48,
  126, -210, -35, -16, -168, 52, 24, 1, 16, -9, -111, 56, 106, -22, 183, 52,
  -124, -5, -57, 3, 33, 140, 190, -46, 19, -125, -30, 163, -169, -40, -47,
  -7, 5, 129, 208, 64, 66, -26, -41, 79, 10, 48, 134, -143, 116, -55, -76,
  67, 63, 21, 327, 126, 113, -49, 114, 85, 64, -197, -122, -66, 271, -145,
  -72, -75, -21, 15, 35, -81, -40, -10, 32, 166, -100, -75, -138, -21, 27,
  -38, 34, -187, 93, -45, -25, -15, 24, 10, -66, 12, -80, -19, 148, 53,
  -103, -62, -18, 117, -157, 73, -69, 61, -32, 6, 55, -71, 136, 142, -129,
  73, -46, -182, -55, -123, 167, 80, -164, -200, 22, -32, 142, -119, -21,
  -260, 150, 61, 135, -41, 27, 101, 22, 55, -6, 175, 143, 48, -167, 62, 42,
  9, -95, 7, -160, 108, 149, 4, -135, 97, 236, 170, -228, 198, -106, -220,
  147, -34]

theorem fractionalNearFrameSubtreeG2R0148_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0148Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0148Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0148Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0148_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0148LowerBoundTable : List ℤ :=
  [-131, 2, 2, 28, 2, 139, 3, 64, 3, 483, 226, 433, -62, 279, 227, 10, 85,
  72, 10, 10, 310, 470, 614, 11, 37]

def fractionalNearFrameSubtreeG2R0148LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0148Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0148LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
