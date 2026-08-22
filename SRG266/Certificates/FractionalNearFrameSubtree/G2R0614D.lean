import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0614`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0614Mask : ℕ := 9609404036532745

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0614Witness : Array ℤ :=
  #[0, -27, -3, 34, 35, 84, 11, 2, 35, 4, 10, 22, -104, -15, -45, -37, 0,
  -44, 32, 9, -53, -10, 18, -68, -61, -24, -7, -64, 67, 42, 72, 80, 79, 26,
  55, 71, 17, -30, -9, -42, -21, -42, 7, 29, -35, 46, 72, -4, 27, -6, -36,
  5, -23, -2, -52, -44, 21, -68, 13, 24, 39, -36, 1, 52, 17, -36, 42, -23,
  7, 33, -25, 5, 48, -15, 24, -84, -22, 21, 27, 23, 41, 5, 3, -59, 7, -47,
  -44, 33, -52, -51, 24, -27, -74, -11, 22, 22, -13, 31, -4, -22, 1, 16,
  -32, -8, -8, -101, -33, 17, -71, -23, -27, -91, 30, -20, 1, 1, 13, 0, 44,
  -14, 20, 63, -70, 59, 77, 14, 24, 63, -23, -18, 39, 10, 31, 18, -9, 6, -9,
  78, -1, -43, -44, -14, -35, -49, -32, -6, 58, 10, 17, 41, 77, -92, 86,
  -53, 49, -64, 12, 8, 2, 57, -51, -22, 77, -10, -72, -25, -41, 64]

theorem fractionalNearFrameSubtreeG2R0614_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0614Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0614Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0614Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0614_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0614LowerBoundTable : List ℤ :=
  [-57, 1, 39, -19, 10, 2, 2, -122, 69, 49, 2, 9, 174, 9, -20, 73, -52, 9,
  -168, -15, 10, 177, 10, 33, -75]

def fractionalNearFrameSubtreeG2R0614LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0614Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0614LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
