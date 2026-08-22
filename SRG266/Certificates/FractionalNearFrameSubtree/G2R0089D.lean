import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0089`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0089Mask : ℕ := 1213636026149897

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0089Witness : Array ℤ :=
  #[0, -16, -10, -39, -19, 28, -43, 30, -38, -96, -91, 12, 66, 84, -63, -27,
  53, 124, 18, 61, -23, -4, 43, 25, -18, 55, -94, -59, 14, -42, -52, -80,
  -69, -115, -61, -87, 27, 137, 111, 139, -40, -112, -64, 44, 54, 21, 40,
  -74, 39, -47, -31, -32, 52, -66, 66, -12, -127, 70, -9, -143, -10, 40, 2,
  92, 79, 92, -39, -1, -53, 107, 39, -10, -11, -77, 9, 74, -21, -62, -6,
  -31, -57, 19, 34, 56, -14, 14, -63, -39, 40, -32, -2, 52, 64, -26, 0, 68,
  16, -20, -25, -38, 79, -47, 80, 2, -67, 21, -97, -22, 0, -1, -38, -51, 65,
  -75, -30, 38, 104, 0, 24, 47, -45, -23, 8, 7, 4, -74, 66, -61, 13, 12, 11,
  25, -21, -93, -118, -63, -101, 45, 66, 52, -7, 30, -48, 9, -23, 18, -33,
  -112, 59, -38, 70, -13, -38, -40, 41, 45, 19, -37, -9, 85, -5, 9, -25,
  178, -65, -3, -71, -121]

theorem fractionalNearFrameSubtreeG2R0089_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0089Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0089Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0089Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0089_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0089LowerBoundTable : List ℤ :=
  [-130, -108, -156, 24, -29, 1, 3, -24, -47, 81, 192, 10, -231, -23, -357,
  -177, 10, 123, -11, -132, 239, 10, -176, 208, 11]

def fractionalNearFrameSubtreeG2R0089LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0089Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0089LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
