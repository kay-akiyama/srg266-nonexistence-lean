import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0180`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0180Mask : ℕ := 1387742356750552

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0180Witness : Array ℤ :=
  #[109, -7, 32, 10, 0, 18, -4, -21, 40, -79, 8, 7, 67, -21, 103, 30, 14, 7,
  3, 1, -13, -10, -45, -59, 63, 4, -13, -27, 101, 19, 88, 17, -12, 11, -91,
  17, -49, 3, -58, -35, -17, -80, -99, -35, -52, 71, -7, 166, 86, -70, 2,
  -34, 38, 65, 40, 34, -83, -1, 20, 69, 65, 6, -11, 40, 20, -23, -84, 41,
  42, -34, 16, -23, 31, 23, 0, 3, 33, 80, 1, -31, -18, -5, 22, 36, -18, -28,
  -92, 22, 44, 24, -41, 2, -15, -82, 85, 6, -22, 50, 84, -22, -33, 19, -7,
  -73, 79, 81, 16, -41, 18, -1, 48, -2, 21, 5, -13, 10, 67, 14, -39, 21, 18,
  -33, -39, -15, 44, 18, -20, -18, 3, 8, 70, -16, 1, 7, 12, 53, -13, -88,
  -13, 57, -86, 37, -59, -75, -3, 27, 101, -101, 102, -15, 6, -18, 58, -44,
  -28, -19, 46, -19, 18, -5, 24, 14, -2, -76, 57, -64, 59, 14]

theorem fractionalNearFrameSubtreeG2R0180_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0180Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0180Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0180Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0180_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0180LowerBoundTable : List ℤ :=
  [-22, 4, 2, 11, -15, 95, 41, 145, 86, 51, 66, 95, 10, 8, -81, 9, -66, 11,
  170, 447, 60, 164, 121, 9, 329]

def fractionalNearFrameSubtreeG2R0180LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0180Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0180LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
