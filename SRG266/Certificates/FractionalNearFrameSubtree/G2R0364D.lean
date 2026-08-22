import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0364`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0364Mask : ℕ := 5714010277385738

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0364Witness : Array ℤ :=
  #[51, 103, 82, 51, 13, 22, -35, -75, 19, 5, 4, -88, -42, -80, 40, -73, 15,
  62, 43, 15, 0, 2, -53, -83, -62, -117, -12, -38, 20, -8, 43, 9, -46, -6,
  -37, 61, 71, 87, 17, 5, -112, 56, 43, 109, -110, -60, 18, 89, 82, 30, -44,
  -40, -21, 55, 46, -7, 47, 0, 45, 26, -101, 9, 56, 7, -34, -22, -94, 60, 3,
  84, -66, 48, 101, 3, -4, 22, 83, -14, 48, 46, -50, 4, 98, 20, 64, 61, 76,
  28, -3, 33, 11, 49, -27, 71, 58, -64, 37, 76, 47, -21, 45, 85, -23, -53,
  -48, 5, -4, -1, -9, -63, -9, 20, -170, -76, -103, -98, 99, -15, 52, 100,
  -14, 71, 43, -42, -10, -6, -6, 71, -54, 46, 4, -43, -8, 52, 51, 22, 45,
  -56, -7, 51, 43, 60, 79, -77, -112, -33, 13, 39, 0, 104, 13, 36, 52, -54,
  -7, -47, 64, 2, 27, 27, -18, 0, 68, 43, 67, -48, 37, 60]

theorem fractionalNearFrameSubtreeG2R0364_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0364Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0364Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0364Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0364_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0364LowerBoundTable : List ℤ :=
  [8, 77, 142, 154, 1, 106, 2, 106, 121, 9, -47, 204, 9, 166, 247, 306, 235,
  -6, 57, 164, 254, 181, 150, 287, 114]

def fractionalNearFrameSubtreeG2R0364LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0364Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0364LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
