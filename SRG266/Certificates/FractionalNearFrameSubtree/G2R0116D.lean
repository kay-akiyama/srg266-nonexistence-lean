import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0116`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0116Mask : ℕ := 1310235343362593

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0116Witness : Array ℤ :=
  #[-78, -43, -82, -112, -82, -42, 26, 72, -17, 95, 84, 9, 14, -20, 33, 46,
  0, 45, 14, 14, 45, -19, -29, -31, -19, -37, 34, 37, 30, -36, 2, -11, 26,
  40, 14, -62, -5, 0, -74, 41, 15, -64, 41, -38, -14, -38, 31, 20, 25, -12,
  -45, 33, -9, -3, -44, -14, 7, 45, 48, 73, 3, 1, -39, 15, -71, 63, 43, -27,
  -33, 29, -13, -50, 36, 21, -14, 26, 33, 52, -30, 50, -28, 9, 17, 41, -48,
  -78, -4, 53, 27, -46, 85, -71, 117, 57, 68, 24, 19, -57, 72, 11, -35, -66,
  45, 8, 7, -32, -43, -28, -30, -63, 26, -6, -124, 33, 40, 20, -8, 82, 87,
  -54, -84, 42, 77, 40, 16, 34, 47, 98, 54, -44, 1, -19, -14, 47, -14, 8,
  16, 99, -35, -22, 14, -66, -35, -9, 35, 41, -21, -40, 87, 57, 47, -28, 29,
  1, -24, -5, -20, -55, -77, -4, 16, 19, 49, 40, -16, -39, -62, 1]

theorem fractionalNearFrameSubtreeG2R0116_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0116Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0116Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0116Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0116_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0116LowerBoundTable : List ℤ :=
  [-21, 31, 3, 75, 1, 73, 2, -40, 2, 225, 135, 265, 47, 115, -83, 155, 43,
  -20, 69, 116, -95, -30, 43, 20, 285]

def fractionalNearFrameSubtreeG2R0116LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0116Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0116LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
