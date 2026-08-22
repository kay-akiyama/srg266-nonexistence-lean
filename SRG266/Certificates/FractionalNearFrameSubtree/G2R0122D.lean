import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0122`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0122Mask : ℕ := 1316514450363409

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0122Witness : Array ℤ :=
  #[5, -29, -69, -41, -48, -59, -87, -74, -38, -5, -12, -59, 67, 47, 98, 97,
  48, 18, -44, 49, 20, 26, 36, -25, -5, -7, 30, 5, -15, -45, -98, -37, 48,
  -84, -91, -95, 43, 36, 112, 58, -13, -73, 25, -74, 192, -8, -6, 66, -70,
  10, 54, -43, -42, 13, 52, -39, 9, 15, 60, 86, 32, -75, -70, 65, 54, -77,
  28, 31, 17, 12, 17, -7, 46, 8, 36, -62, 58, 41, 50, 37, -18, 19, -71, -83,
  49, 75, -33, -6, -22, -24, -10, -37, 91, 1, -2, -40, -50, -33, -52, 38,
  77, -63, 31, 0, -83, -84, -21, -61, -57, -7, -24, -43, -59, 93, 149, 2,
  -29, 13, -2, 43, 79, 39, 27, 54, -1, -17, -3, 82, 47, 6, -4, 43, 4, -3,
  -31, 31, 22, -6, -12, 35, -50, -77, 13, -4, 35, 15, 32, -13, 16, 10, 48,
  -49, -20, 64, -75, -25, 40, 0, -9, -21, -59, 23, -13, -60, 5, -71, 39, 2]

theorem fractionalNearFrameSubtreeG2R0122_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0122Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0122Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0122Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0122_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0122LowerBoundTable : List ℤ :=
  [-103, 1, -74, 15, -82, 3, 28, 2, -54, 148, 78, 35, 9, 166, -89, 128, -73,
  10, -29, 127, 94, 41, 11, 9, 596]

def fractionalNearFrameSubtreeG2R0122LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0122Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0122LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
