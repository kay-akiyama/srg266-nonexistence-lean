import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0053`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0053Mask : ℕ := 964394795770956

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0053Witness : Array ℤ :=
  #[60, 24, 62, 90, 56, -2, 33, 21, -87, -52, 1, -39, 23, -81, 0, -128, -51,
  -53, -68, -23, -39, 18, -15, -22, 135, 23, 8, 77, -7, 69, -53, -21, 39,
  -9, 0, 25, 20, -20, -1, 0, -4, 6, 21, -22, -9, -50, -25, 6, 44, 88, -1, 4,
  -21, -12, 32, 67, -55, 37, 4, 0, 57, 16, -49, -19, 23, -82, -13, 68, 18,
  -31, 4, 45, 19, 12, -2, 29, -29, 71, 6, -15, 14, 0, 27, 0, -9, 36, -6,
  -46, -13, -2, -23, -35, -10, -64, 66, -63, 30, -15, 60, 4, -3, -30, 23, 3,
  -24, 15, 25, 45, 2, 15, -34, 21, -8, -12, -26, 16, -18, -17, -20, -23, 12,
  64, 42, -70, 43, 27, -16, -41, -24, 5, 19, 10, 55, 105, -7, -5, 22, -25,
  7, -35, -80, -4, -28, -70, -72, -9, 24, 59, -5, -9, 19, 76, 18, -39, 36,
  -21, -25, -3, -32, -65, 0, -38, 13, -13, -27, 108, 34, 0]

theorem fractionalNearFrameSubtreeG3R0053_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0053Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0053Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0053Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0053_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0053LowerBoundTable : List ℤ :=
  [-51, 2, 2, -2, 37, 30, 61, 0, -6, 228, 106, 3, -187, 8, 97, 106, -64, 71,
  12, -169, 110, 84, 59, 124, -30]

def fractionalNearFrameSubtreeG3R0053LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0053Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0053LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
