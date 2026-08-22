import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0256`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0256Mask : ℕ := 5356462712335884

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0256Witness : Array ℤ :=
  #[40, 67, -22, 66, -37, 27, 22, -5, 19, -29, -35, -17, -64, -56, -12, -25,
  -98, -73, 70, -98, -38, -58, 51, 32, 32, 99, -13, -34, 119, -34, 37, -90,
  -16, 29, -8, 96, 6, -5, 27, 2, 15, 92, 34, -37, -92, 27, 75, 0, -53, -52,
  47, 39, 47, -77, 34, 9, 77, 36, 15, -68, 0, 66, -82, -97, -76, -49, -79,
  -130, -34, 115, 2, 41, 38, 0, 59, -8, 61, 12, 34, 59, -84, 72, -29, 28,
  37, -44, -14, 21, 145, 69, -48, -53, 8, -50, 14, -49, -103, 89, -24, -50,
  8, -86, 38, 84, -7, 4, -90, 54, 43, 111, -74, -64, 95, 112, 16, 146, -84,
  -24, 35, 35, 82, 71, 45, 63, -116, -63, 74, -35, -72, 142, 94, -23, 66,
  -29, -4, -38, 65, 85, 30, 54, -137, -25, -38, 16, 74, -36, 95, -22, 15,
  -12, -9, -133, 75, 57, 92, 31, 0, -33, -102, 88, 0, 71, -8, 22, -33, 24,
  -27, 28]

theorem fractionalNearFrameSubtreeG2R0256_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0256Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0256Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0256Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0256_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0256LowerBoundTable : List ℤ :=
  [-16, 58, 9, 1, 31, 39, 160, 2, 62, 194, 336, 544, 333, 112, 107, -15, 19,
  -66, 210, 114, 9, 32, -19, 211, -157]

def fractionalNearFrameSubtreeG2R0256LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0256Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0256LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
