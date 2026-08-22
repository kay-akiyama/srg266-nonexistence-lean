import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0259`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0259Mask : ℕ := 5367647912530570

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0259Witness : Array ℤ :=
  #[24, 34, 5, 72, -50, 51, 46, 122, 16, 35, 153, -35, 33, 49, 29, -146, 79,
  50, 68, 60, 15, -17, 38, 14, -34, 8, 27, 7, 115, -1, 32, 17, -18, -48, 2,
  14, -26, -63, -31, 0, 65, 74, 112, 11, -6, -98, 14, -74, 9, -73, 36, -25,
  149, 27, 91, 47, 93, 120, -123, -34, 128, 9, -134, -68, -41, -74, 58, -34,
  22, -75, -14, -21, -24, 85, 12, 3, 69, -25, -6, 37, -1, 62, -23, 22, 21,
  -126, 96, 161, 72, 51, 18, 28, -11, 98, 46, 4, -133, 62, 91, 31, -6, -29,
  8, 150, 20, 19, -156, 42, 23, -2, 45, -24, 97, -18, 122, 127, 37, 114,
  -59, 38, 48, -93, 77, -76, 29, 20, -37, 28, -45, -113, 31, -113, -98, -33,
  85, -99, 46, -38, 1, 17, -98, -19, -26, -5, 59, 38, -36, 44, -1, -5, 80,
  -76, 50, -207, 13, -93, -31, -10, -75, -1, -145, 17, 41, 0, 38, -50, -233,
  9]

theorem fractionalNearFrameSubtreeG2R0259_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0259Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0259Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0259Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0259_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0259LowerBoundTable : List ℤ :=
  [5, -212, 1, 122, 72, 201, 297, 236, -2, 231, 100, 306, -194, 10, 9, -32,
  -31, 105, 558, 169, -149, -115, 202, 9, 157]

def fractionalNearFrameSubtreeG2R0259LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0259Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0259LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
