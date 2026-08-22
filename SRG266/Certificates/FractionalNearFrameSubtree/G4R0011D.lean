import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0011Mask : ℕ := 4739630372801029

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0011Witness : Array ℤ :=
  #[13, -19, 18, -58, -36, -49, 42, 78, 66, 15, 91, -64, 17, -40, 33, 0, 26,
  -50, -1, -43, -61, -38, -30, 2, -8, 15, -4, 50, -9, 69, 53, 71, 21, 64,
  12, 33, 57, 55, -58, -107, -82, -27, 69, 93, 51, -41, -62, -12, -35, -40,
  29, 22, 28, -30, 52, 23, -26, -60, -13, -16, 17, 42, 14, 0, -29, 81, -17,
  -25, -1, 19, -36, 5, -18, 44, 39, -38, -67, 28, -28, 6, 26, -42, 11, 31,
  5, 16, 11, 3, 6, 43, 20, -4, 55, 5, 13, -16, 10, -4, -8, 1, -24, 64, 56,
  59, 54, 7, -9, 10, -22, 5, 15, 35, -26, 14, 19, -25, -15, 18, 1, -10, 18,
  69, 9, -9, -13, 2, 8, 27, -3, 9, 9, 60, -12, -23, -9, 0, 3, -20, 16, -17,
  52, -22, 1, 22, -19, 29, 39, -15, 39, 28, 40, 20, -22, -20, -123, -32, 1,
  -18, -12, -102, -1, -2, 0, -50, -40, -38, -68, 1]

theorem fractionalNearFrameSubtreeG4R0011_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0011Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0011Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0011Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0011_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0011LowerBoundTable : List ℤ :=
  [0, -83, -13, 3, 87, 70, 119, -2, -16, 120, 55, 90, 55, 10, 86, -17, -57,
  11, -55, 173, 28, 31, 156, 149, 102]

def fractionalNearFrameSubtreeG4R0011LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0011Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0011LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
