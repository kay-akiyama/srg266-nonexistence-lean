import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0118`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0118Mask : ℕ := 1310252388493857

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0118Witness : Array ℤ :=
  #[0, 54, 46, 38, -75, 39, 21, -21, 71, 56, 147, 47, -105, -71, -131, -60,
  -55, -107, -41, 43, -39, -46, -314, -105, -114, -40, -45, -39, 229, 70,
  115, 318, -248, -17, -191, 0, 182, -2, 151, 30, 164, 45, 96, -40, 228,
  -106, -37, -11, 93, 133, 39, 67, -51, -24, -28, 0, -67, 3, 74, -171, 0,
  -131, -2, -3, 97, 111, 16, -57, -69, 101, 28, -23, 13, -1, -38, 18, -26,
  3, 19, -5, -156, 74, 97, 148, 87, 4, 114, 71, 33, 71, -38, 211, 48, -51,
  -93, 301, 206, 30, 37, 28, 293, -35, -15, 4, 0, 139, 26, 64, -29, 105,
  232, 14, -1, 64, 31, -31, 47, 166, 33, 74, -112, 0, 22, 7, -64, -130, 14,
  -22, -50, -67, 48, 25, 60, 112, -140, -56, 85, -5, -46, -14, 0, -67, 61,
  -10, -11, 21, -5, 29, 36, -32, 64, -24, -34, 94, -48, 122, -111, -51, 18,
  -10, -25, 76, 23, -1, -121, -33, 55, -39]

theorem fractionalNearFrameSubtreeG2R0118_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0118Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0118Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0118Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0118_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0118LowerBoundTable : List ℤ :=
  [24, -90, 274, 181, 183, 438, 151, -44, 196, 269, 282, 39, 10, 381, -134,
  -12, 490, 335, 240, 355, 396, 182, 204, 64, 61]

def fractionalNearFrameSubtreeG2R0118LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0118Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0118LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
