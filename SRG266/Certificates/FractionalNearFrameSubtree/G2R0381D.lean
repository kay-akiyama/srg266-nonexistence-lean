import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0381`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0381Mask : ℕ := 5738185200976274

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0381Witness : Array ℤ :=
  #[46, 8, 56, 52, 1, 26, 54, -9, 32, -10, -4, -25, 1, -54, 3, -73, 0, 0,
  -39, -77, -80, 54, 12, 44, 32, -102, 89, 88, 109, 58, -18, -63, -44, 7,
  48, 137, 6, -23, -11, -1, -23, 22, -42, -18, 0, 53, -5, -43, 29, -2, 6,
  48, 38, -90, -36, -19, -19, -34, 73, -8, -1, 71, 3, -22, 9, 34, 23, -29,
  14, 59, -26, -24, 13, -10, -10, 42, -36, 43, 32, -43, 10, 23, -16, 4, 11,
  9, 26, -3, -2, 74, -93, 19, 13, 55, 34, -16, -14, -26, 36, 14, -92, 53,
  14, 1, 18, -25, 19, 43, 59, 52, 52, 0, -29, -19, -48, -75, -68, -74, -7,
  -100, 13, -8, -23, -37, 66, -43, 43, -55, 12, -59, 58, 5, 0, 56, 18, 21,
  -55, 86, 2, -16, -8, 34, 10, -60, 27, 81, -73, -18, 41, 44, -68, 1, 28, 7,
  16, -8, -37, -53, -47, 10, 34, -23, 15, -5, -43, 89, 47, 51]

theorem fractionalNearFrameSubtreeG2R0381_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0381Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0381Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0381Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0381_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0381LowerBoundTable : List ℤ :=
  [-38, -15, -14, 19, -12, 49, 1, 72, 124, 131, 180, 85, 19, 165, -28, -116,
  -29, -127, 28, 122, 261, 18, 205, 256, 10]

def fractionalNearFrameSubtreeG2R0381LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0381Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0381LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
