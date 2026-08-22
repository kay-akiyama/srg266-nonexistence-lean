import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0167`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0167Mask : ℕ := 6856954164139160

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0167Witness : Array ℤ :=
  #[-27, -37, -50, 25, 7, -42, -15, -46, -62, -30, 156, 65, 12, 86, 14, 13,
  6, -4, 16, 4, -8, -6, -3, 32, 29, -38, -94, 53, -21, 71, 7, -24, 6, -31,
  -50, -53, 26, 26, -1, -30, 40, 0, 16, 21, 5, 72, -18, -13, 39, -106, 4,
  73, 46, 81, -41, -34, -23, -8, -4, 77, -22, 71, 76, 16, 51, -29, -136,
  -82, -39, -37, -31, 10, 49, 93, 139, -21, -34, -16, 0, -84, -28, 29, 31,
  73, 35, 31, -17, -58, -15, -24, 68, -7, -51, -25, -102, 13, 57, -1, -11,
  0, -73, -10, 35, 5, 33, 12, -18, 20, -4, 87, 43, 110, -3, 55, 12, -5, -49,
  -108, -23, 24, 48, 19, -14, 48, 51, 130, -24, -19, 31, 63, 100, 11, 50,
  89, -35, 35, -37, 139, 3, -5, 28, -41, 52, -30, 75, -2, -51, 1, 33, 0, 15,
  -10, 0, -85, -41, 88, -2, -84, 3, 42, -72, 49, -149, -16, 11, -157, 41,
  -21]

theorem fractionalNearFrameSubtreeG3R0167_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0167Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0167Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0167Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0167_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0167LowerBoundTable : List ℤ :=
  [5, 76, 42, 3, -41, 24, 32, 2, 153, 24, 181, 42, 420, -120, 127, 246, 199,
  11, 160, -333, 335, 70, 49, 9, -33]

def fractionalNearFrameSubtreeG3R0167LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0167Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0167LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
