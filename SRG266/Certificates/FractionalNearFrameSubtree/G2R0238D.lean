import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0238`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0238Mask : ℕ := 5108041868108297

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0238Witness : Array ℤ :=
  #[0, 31, 102, 22, 17, 73, 47, 126, 37, 13, 135, 68, -55, 14, -61, 0, -76,
  -183, 25, -54, -96, -16, -114, 22, -116, -103, -31, 23, 131, 111, 217,
  156, 20, 22, 19, -7, -33, -66, 48, 58, 36, 43, 34, -39, -32, -35, -48,
  -37, 3, 10, 31, 44, 0, -13, 30, -5, 38, 92, -23, 17, 1, -19, 4, 44, 5,
  -23, -26, -33, 44, -37, 8, 38, -1, 19, -15, 4, 15, 33, -4, -19, -9, -45,
  13, 9, 36, 70, -32, -36, -14, -2, 44, 2, -27, 9, 6, 60, 47, 58, 23, -21,
  16, -3, 14, 7, -24, 43, -14, 23, 1, -5, 2, 37, 46, 5, 22, 2, -40, -47, 20,
  32, 11, -5, 13, -5, -27, 31, -50, 23, -11, -15, 3, -38, -55, -11, 18, -23,
  -2, -17, -2, 49, 20, 30, 51, -30, -20, -7, -41, -18, -41, -15, -87, -14,
  -22, -64, -84, 6, -16, 39, -13, -36, -6, -8, -30, -42, 27, 69, 18, 4]

theorem fractionalNearFrameSubtreeG2R0238_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0238Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0238Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0238Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0238_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0238LowerBoundTable : List ℤ :=
  [23, -132, 58, -80, 70, 105, 2, 238, 181, -137, 119, -101, 12, 74, 236,
  -51, 76, -74, 10, 77, -28, -16, 200, 61, 145]

def fractionalNearFrameSubtreeG2R0238LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0238Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0238LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
