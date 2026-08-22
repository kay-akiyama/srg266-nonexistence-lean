import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0121Mask : ℕ := 969519362558376

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0121Witness : Array ℤ :=
  #[-30, -16, -3, -22, -13, -22, -12, 48, 24, 3, -49, 2, 11, 39, 46, 44, 20,
  21, -28, -4, 22, -23, -8, 12, -51, 56, -33, -8, 35, -27, 38, -71, -27,
  -17, -75, 50, -54, -49, 13, 0, -28, 41, -41, 32, -38, 20, -55, -20, -32,
  17, -11, -85, -60, -31, 0, 2, 11, 15, 5, -8, 8, 22, -25, -23, -42, 95, 13,
  -8, 28, -62, -15, 7, -10, 3, -36, 20, 1, -42, 50, -10, 28, 1, -47, 9, 2,
  27, 49, -26, 81, 3, 72, -37, 32, -51, -101, 46, 28, -32, -19, 25, 0, 6, 5,
  4, 2, 21, -53, -19, -7, -11, 19, -41, 3, -30, 34, 10, 108, 9, 26, 28, 12,
  -3, 36, -10, 56, -47, 5, 40, 60, 34, -75, -1, 2, 34, 14, 43, 30, 44, 23,
  -3, 7, -29, 62, 82, -19, -7, 27, 5, 23, -20, 10, -87, 4, -44, 24, -5, -52,
  11, 54, -39, 64, -19, -78, 29, -69, -13, -23, -15]

theorem fractionalNearFrameSubtreeG1R0121_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0121Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0121Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0121Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0121_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0121LowerBoundTable : List ℤ :=
  [-46, 57, -105, 60, 2, 8, -19, 2, -24, 9, 9, -15, 122, -124, 8, 36, -86,
  -10, -72, -8, 320, -43, 224, -179, 9]

def fractionalNearFrameSubtreeG1R0121LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0121Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0121LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
