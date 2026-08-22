import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0558`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0558Mask : ℕ := 6841868849154648

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0558Witness : Array ℤ :=
  #[134, 92, 211, 79, 52, -33, 59, 17, -17, -40, 73, 5, -76, -99, -102, 30,
  -39, 64, -125, 14, -12, 16, 11, -27, 38, 72, -42, 18, 100, 87, 193, 38,
  -223, -33, 118, -90, -29, -21, -125, -32, 120, 17, 121, 87, 197, -3, -40,
  6, -135, -39, -28, 82, -97, -167, -105, 223, 208, -195, 143, -34, -53,
  -301, 41, -66, -234, -122, 63, 2, 1, 48, 29, -167, 67, 163, -96, 29, 65,
  73, -102, -39, -136, -75, 64, -97, -12, -46, 90, 63, 4, 8, 179, 52, 148,
  -43, -13, 116, -224, -50, -19, -56, 53, -123, -38, 60, 18, -48, -108, -14,
  36, 64, 67, -138, -2, 0, 72, 300, 11, 14, 159, 10, 133, -23, -17, -21,
  -24, -59, -6, -86, -38, -49, -58, -5, -10, 19, 13, 34, -62, 76, 16, -54,
  95, 99, -49, 53, 167, 6, 53, 194, 14, -81, 21, -15, -132, -2, -47, 94, 12,
  -23, -59, 0, -151, 70, 108, 155, -47, -113, 23, -143]

theorem fractionalNearFrameSubtreeG2R0558_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0558Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0558Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0558Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0558_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0558LowerBoundTable : List ℤ :=
  [-19, 130, 71, -175, 153, 1, -232, 270, 2, 52, 232, 219, -67, -33, 10,
  515, 59, -448, 164, 48, 92, 121, 74, -368, 577]

def fractionalNearFrameSubtreeG2R0558LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0558Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0558LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
