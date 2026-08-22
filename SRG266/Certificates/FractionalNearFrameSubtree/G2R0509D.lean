import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0509`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0509Mask : ℕ := 5812243867812180

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0509Witness : Array ℤ :=
  #[66, 7, 43, -39, -62, 59, 12, 43, 56, 22, -61, 43, 33, 18, 19, -51, -15,
  6, 11, -38, 33, -8, -3, -15, 12, 24, 21, 2, -38, 2, 36, 36, -18, -78, -64,
  -77, 64, -16, 3, -40, -33, -20, 62, 31, 19, 16, 29, -15, -67, -6, -71,
  -16, 57, -26, -45, 65, -27, -19, 6, -19, 79, -16, -28, -3, -48, -35, 65,
  -20, 1, -92, 46, -57, 51, 20, 30, 31, 36, 34, -1, -3, -13, 30, -70, 43,
  32, -68, 49, -21, 64, -2, -22, 7, -57, 18, -5, 30, 36, -10, 22, -42, 47,
  -7, 46, 99, -35, 23, -32, 43, 55, 37, -2, 57, 29, -1, -12, 10, -68, -43,
  32, 8, 14, -47, -39, -6, 32, -51, -10, -75, 29, 42, -70, -7, -13, -22, -5,
  -20, 13, -54, -8, 25, -52, 25, 51, -8, 33, 10, 16, -13, 39, -46, 4, 59,
  18, -60, 57, -19, -51, 11, 7, -23, 24, -1, 10, -51, -50, 39, 13, -16]

theorem fractionalNearFrameSubtreeG2R0509_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0509Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0509Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0509Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0509_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0509LowerBoundTable : List ℤ :=
  [-48, -56, 28, 2, -2, 3, 2, 3, 1, 29, 63, -33, 10, 96, -43, 82, 129, 308,
  69, 66, 126, 35, 9, -178, 9]

def fractionalNearFrameSubtreeG2R0509LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0509Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0509LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
