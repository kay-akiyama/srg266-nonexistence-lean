import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0140`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0140Mask : ℕ := 6846508810278034

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0140Witness : Array ℤ :=
  #[11, 53, 27, -17, 28, -4, 2, -22, 5, 10, 4, 5, -20, 62, 50, -3, 36, 84,
  -18, 10, 10, 10, 40, -27, 9, 8, -17, 32, -35, 23, 49, 8, 20, 22, -19, -43,
  -22, 18, -17, 16, -28, -24, 80, 56, 59, 11, -63, -59, 25, -38, -79, -51,
  -15, -41, 34, 35, -54, -66, -47, 9, -8, 17, 23, 16, -34, -14, -67, -40,
  -17, 39, -39, 41, -12, -47, -10, -11, 9, -17, 25, -54, -1, 0, -21, 27, 3,
  -53, 42, -35, -39, 16, -11, -44, -34, 36, -7, 38, -18, 20, 25, -69, -16,
  3, 3, 40, 6, 5, 21, 33, 65, 45, -44, -46, 24, 37, -1, -28, -56, -27, -1,
  3, 62, 7, 11, 26, 44, 49, 15, 26, 35, 27, 10, 13, -8, 33, 26, -53, 2, -70,
  15, -44, -27, 2, 21, 36, -32, 41, -25, -3, -54, -7, -19, 27, -15, 21, 8,
  13, 13, -11, 9, 52, -8, -58, -34, -20, 0, -82, 4, -37]

theorem fractionalNearFrameSubtreeG3R0140_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0140Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0140Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0140Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0140_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0140LowerBoundTable : List ℤ :=
  [-82, -38, 2, -15, -67, 35, -38, 2, 2, 128, 20, 2, 122, -132, 136, 33,
  -25, 9, 19, -36, 203, 12, 11, 11, 55]

def fractionalNearFrameSubtreeG3R0140LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0140Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0140LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
