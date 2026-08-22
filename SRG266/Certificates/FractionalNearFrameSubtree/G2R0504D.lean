import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0504`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0504Mask : ℕ := 5811582142198564

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0504Witness : Array ℤ :=
  #[0, -31, 13, 0, -102, 74, 21, -22, 63, -41, 54, 32, -47, 36, 53, -24,
  133, 51, -23, 14, 56, 63, 14, -40, -26, -91, 52, 24, 14, -78, 57, 37, 24,
  120, 59, 0, -27, -47, 32, 65, 44, 19, -113, -56, 126, 78, -29, -21, 44,
  23, 0, -38, -20, -64, 25, 31, 19, 85, -74, -33, 45, 50, 10, -59, 20, 34,
  25, 39, -28, -8, -33, 17, 0, -11, -84, 45, -11, -39, 37, -20, -13, 0, -23,
  -14, -57, -18, -55, 26, -9, -9, -79, 65, -2, 37, -92, 26, 39, 0, -30, -8,
  3, 25, 64, 75, 70, 51, 26, 74, 10, 31, -92, -25, 101, 54, -31, -103, -9,
  7, -13, 17, -54, -23, 27, 16, -33, -8, -22, 15, 81, 46, 27, -6, 4, -46,
  26, -12, -26, -13, 25, -15, -5, 2, 14, 41, 77, -19, 63, 6, -7, -121, 40,
  -62, -17, 65, 6, 53, -44, 50, -11, 22, -27, 28, -8, -66, 19, -7, 68, -7]

theorem fractionalNearFrameSubtreeG2R0504_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0504Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0504Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0504Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0504_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0504LowerBoundTable : List ℤ :=
  [-12, 2, 77, -31, 73, 86, 58, 133, 67, 224, -238, 167, 46, 142, 34, 173,
  223, 9, -83, 103, 100, 191, -19, 13, 536]

def fractionalNearFrameSubtreeG2R0504LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0504Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0504LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
