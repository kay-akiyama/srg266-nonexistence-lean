import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0255`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0255Mask : ℕ := 5356461772840460

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0255Witness : Array ℤ :=
  #[5, 22, -7, 7, 5, 15, 87, 80, 52, 50, 134, -86, -59, 0, -26, -45, -5, -6,
  1, -22, 6, -10, -15, 53, 42, 39, 15, 24, 86, 32, 60, 43, -23, 43, -1, -51,
  -11, -5, 17, -19, -2, -36, 0, -2, 4, 26, 19, 9, 33, 7, -20, -14, -38, -30,
  15, 42, -20, -27, 1, -25, 56, 10, -22, 36, -5, -14, 29, -43, 20, 0, 4, 15,
  -1, 14, 5, 29, 10, 31, -42, 73, 56, -11, 98, -72, 28, -24, 80, 20, -2, 36,
  17, 38, 24, -2, -18, -27, -4, -28, 13, 24, 6, 3, -6, -34, -67, 0, -15, 33,
  -15, -43, 8, 63, 32, 72, 14, -52, -10, -24, 2, -18, 37, 36, -14, 4, 46, 0,
  -11, -74, 61, -27, 50, 49, 7, -5, 8, 18, -10, 47, 36, 67, 26, -2, 43, 16,
  -4, 13, -44, -22, -14, -40, -2, -90, -12, -1, -36, -43, 90, 33, 32, -6,
  -32, 27, 30, 45, 4, 18, 0, -12]

theorem fractionalNearFrameSubtreeG2R0255_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0255Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0255Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0255Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0255_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0255LowerBoundTable : List ℤ :=
  [50, 45, 1, 75, 27, 1, 90, 101, 148, -115, 58, 269, 276, -74, 112, 124,
  122, 133, 225, 150, 230, 506, 16, 114, 88]

def fractionalNearFrameSubtreeG2R0255LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0255Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0255LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
