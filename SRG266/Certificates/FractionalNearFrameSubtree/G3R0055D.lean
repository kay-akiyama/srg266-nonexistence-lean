import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0055`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0055Mask : ℕ := 964600941612120

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0055Witness : Array ℤ :=
  #[57, 85, 63, -37, -26, 47, 56, 20, -30, -48, -9, -73, -79, -5, 23, 8, 27,
  -56, -80, 29, -16, -12, 34, -13, 29, -69, 45, 11, -12, 5, -17, 20, 6, 1,
  9, 12, 10, 50, -25, 11, -119, -4, -7, 3, -13, -9, 1, -2, -5, 10, 8, -6, 0,
  27, -43, -3, 31, -11, 36, 39, 4, 16, -9, -104, -3, -17, 33, 7, 7, 4, 1,
  -8, 30, -9, -20, -23, 20, -12, 16, -14, -39, -33, 28, 48, -40, 13, 10, 13,
  6, 34, 31, 41, -48, 38, 28, 32, -15, -21, -18, 31, -52, 74, -50, 19, 24,
  -9, -18, 4, 29, -35, 46, -83, 19, 1, -23, 60, 1, 0, 26, -11, 36, 16, 14,
  -5, 14, -3, 10, -74, -4, 41, -69, 82, -44, 24, 51, -23, 0, 6, -54, -38,
  15, 58, -45, -32, 16, -2, 35, -73, 26, -13, -9, 41, -47, 81, -39, 35, 31,
  -11, -66, 39, 42, 54, 123, 35, 34, 20, 13, -62]

theorem fractionalNearFrameSubtreeG3R0055_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0055Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0055Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0055Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0055_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0055LowerBoundTable : List ℤ :=
  [-34, 72, 4, -19, 11, 35, 34, 1, 27, 176, 50, -111, 47, 116, -12, -54, 42,
  75, 10, 182, -43, 11, 15, 151, 200]

def fractionalNearFrameSubtreeG3R0055LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0055Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0055LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
