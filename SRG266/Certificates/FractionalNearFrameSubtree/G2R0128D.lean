import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0128`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0128Mask : ℕ := 1352178804950090

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0128Witness : Array ℤ :=
  #[-26, -99, -53, -196, -69, -39, 0, 126, 182, 160, 171, -43, -84, -101,
  -156, -106, 61, -45, -7, -172, -73, -90, -38, -46, -8, -71, 100, 45, 36,
  48, -3, 91, -19, 111, 103, -115, -135, 153, 77, -225, -117, -153, -15, 75,
  18, -14, -5, 27, -30, 42, -47, -38, 17, 46, -34, 22, 10, -32, 74, -3, 28,
  44, 44, 54, 65, 15, 84, 48, -79, 96, -43, -4, 61, -53, 56, 99, -98, 144,
  -52, 144, 34, 109, -5, 126, -2, -12, -5, 20, -51, -54, -1, 193, -4, -49,
  -14, 68, -4, -13, -97, 66, 31, -8, 43, -4, 42, -122, -117, -66, -25, -44,
  -61, -5, 32, 113, -147, 20, -36, -85, -8, 39, -59, -56, 27, -3, 89, 41,
  -44, -30, -45, 57, -61, 78, 38, 6, -45, -21, -122, -22, -22, 32, 27, -45,
  -19, 66, -118, 108, -51, -58, -45, 79, 0, 102, 52, 2, -52, -4, 36, 119,
  37, 174, 102, 13, 129, 60, 72, -3, 44, -64]

theorem fractionalNearFrameSubtreeG2R0128_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0128Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0128Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0128Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0128_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0128LowerBoundTable : List ℤ :=
  [-80, 68, 299, -68, -80, 16, 31, -200, -89, 9, -27, -26, -209, 495, 415,
  11, 202, 285, 32, -203, -172, 295, 226, 264, 252]

def fractionalNearFrameSubtreeG2R0128LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0128Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0128LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
