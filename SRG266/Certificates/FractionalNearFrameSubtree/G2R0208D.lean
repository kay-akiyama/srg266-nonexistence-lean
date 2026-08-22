import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0208`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0208Mask : ℕ := 2355827548082721

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0208Witness : Array ℤ :=
  #[0, -15, 42, 13, 31, 10, -5, -10, 27, -25, 96, 8, 49, -11, -12, 48, 15,
  -86, -20, -28, -12, -17, -14, -23, 139, 2, 185, -13, -56, -26, 42, -12,
  64, 11, 49, 7, -48, -30, 53, -128, 66, -3, -22, -43, 50, -6, -85, -2, 52,
  -148, -8, 150, 48, -27, -35, 72, -74, -18, 7, -2, -1, 0, -38, 44, -70,
  -32, 77, -19, -26, 5, 24, 82, 7, 65, -31, -7, -2, 43, -22, -53, -5, -11,
  -32, 30, 30, 133, -3, -41, 12, -73, -19, -18, 82, -4, -58, -16, -91, -99,
  -43, 32, -48, -50, 83, -3, -60, 17, 1, 64, 64, 52, 12, 19, -41, 70, -81,
  -12, -18, 39, 14, -51, -6, 11, -15, 81, 19, 3, 2, -57, 28, -8, 89, 67,
  104, -123, -72, 42, 8, -6, 0, 29, 64, -64, -48, -1, -16, -50, 33, -13, 35,
  -9, 78, 36, -55, 23, 18, 47, 2, -17, 14, 15, 50, 19, -27, -3, 34, -16, 42,
  -67]

theorem fractionalNearFrameSubtreeG2R0208_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0208Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0208Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0208Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0208_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0208LowerBoundTable : List ℤ :=
  [-48, 104, 2, -47, 108, 2, -60, 136, 38, 10, 92, 134, 6, 229, -47, 88,
  184, 10, -24, 433, 11, 9, 12, -98, 10]

def fractionalNearFrameSubtreeG2R0208LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0208Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0208LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
