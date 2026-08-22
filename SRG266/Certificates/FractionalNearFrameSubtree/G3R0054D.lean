import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0054`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0054Mask : ℕ := 964600501223640

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0054Witness : Array ℤ :=
  #[-7, -6, 33, -14, 28, -25, -2, 3, -40, -41, -34, -9, -15, 36, 6, 8, 37,
  -24, 32, -13, 27, 61, 7, -23, -43, -86, -14, -40, -26, -5, 56, -21, 26,
  -27, -40, 84, 60, 99, 31, -14, -58, -62, -3, 16, 26, -30, 8, -1, -9, -17,
  0, 1, 14, 39, -22, 5, 59, 0, 61, 15, 10, 27, 43, -28, -24, 11, -9, 3, -8,
  16, -11, 30, 6, 23, 15, 34, 10, 64, 31, -50, 53, 13, -42, -18, 14, 9, -36,
  16, -19, 48, 1, 39, 28, 8, -45, -38, -32, -34, 59, -19, -2, 12, -47, 13,
  -3, -9, -7, -19, -35, -17, -17, -25, 27, 54, 0, -5, 1, 16, -2, -61, -21,
  22, -3, 48, -16, 28, -51, 3, -6, -27, 10, -23, -13, 23, -27, -13, -16, -7,
  -58, 8, -16, 39, 0, -52, 7, -25, -2, 3, 24, 37, -45, 23, -53, 26, -18, 12,
  8, 33, 28, -2, 31, 22, 29, 7, 41, -8, 24, -20]

theorem fractionalNearFrameSubtreeG3R0054_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0054Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0054Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0054Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0054_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0054LowerBoundTable : List ℤ :=
  [-20, 2, 49, 47, -88, -27, 110, 34, -91, 68, 68, 5, -95, 96, 5, 171, 9,
  81, 12, 143, 76, -21, 106, 65, -47]

def fractionalNearFrameSubtreeG3R0054LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0054Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0054LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
