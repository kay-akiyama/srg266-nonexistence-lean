import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0318`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0318Mask : ℕ := 5389447590437544

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0318Witness : Array ℤ :=
  #[8, -73, -51, 3, -49, -10, -54, 0, -28, 19, 87, 64, 69, 49, 53, -50, 11,
  10, -12, 56, -25, -10, 53, -6, -37, -99, -39, 9, 21, 48, 44, 37, 24, -94,
  -39, 57, -5, -81, -24, -38, -65, -7, -25, -41, 63, 39, 19, -3, -14, 89,
  73, 42, 22, 0, 60, -59, 57, -8, -38, -53, 22, 95, 47, 1, -35, -29, -23,
  12, 39, -70, 41, 44, -25, -38, 48, -9, 27, 18, -3, -13, 27, -41, 30, 26,
  -41, -23, 12, -15, 32, 3, 36, 89, 24, 44, -5, 26, 21, -20, -56, 5, 38, 26,
  -36, -23, -10, 12, -19, 52, -67, -76, -22, 17, -20, 4, 28, 9, 44, 116, 0,
  -5, -46, -6, -33, 28, -28, -49, 0, 64, 11, 48, 7, 45, -99, 46, 15, 18,
  -28, 39, 34, 4, -7, -10, -20, -59, 31, 20, 52, -11, -47, -64, 10, 4, -51,
  39, -35, -134, -1, -79, 0, -73, 1, 47, 0, 96, 37, 40, -124, 50]

theorem fractionalNearFrameSubtreeG2R0318_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0318Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0318Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0318Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0318_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0318LowerBoundTable : List ℤ :=
  [-59, -41, 36, 50, -50, 35, 1, -53, 63, -5, 223, -211, 97, 11, 274, 11,
  203, -92, 119, 72, 85, -42, 10, 42, 143]

def fractionalNearFrameSubtreeG2R0318LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0318Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0318LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
