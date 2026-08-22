import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0491`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0491Mask : ℕ := 5811179488732684

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0491Witness : Array ℤ :=
  #[85, 38, 0, -22, 53, 34, 83, 46, 97, -3, 45, -150, -138, -70, -91, -107,
  14, -154, -82, -38, -176, 37, 82, -41, 60, -105, 138, 20, -20, 119, 80,
  -6, -9, 136, -45, -84, 140, 117, 107, 83, -83, -75, 83, 0, -11, -91, 3,
  41, 18, 153, 77, -45, 6, 83, -56, 1, 75, -28, -26, -16, 4, 58, 79, 9, 61,
  18, -50, -62, -80, 143, -65, -9, -12, 77, 39, 52, -33, 120, -37, -40, 7,
  -6, 17, 41, 32, -37, -50, 37, -11, -43, 80, 37, -12, 17, 137, 2, 40, -21,
  -24, 49, 54, 47, -24, 35, 35, -73, -32, 80, -46, -116, -13, -17, -24, 53,
  -14, 14, -12, -49, 66, 109, 52, 101, -58, -38, 1, -43, 47, 25, -56, 13,
  77, 60, -87, -24, -58, 2, 69, -181, -50, -39, 72, 17, 9, -107, -63, 62,
  37, -13, 73, -16, 118, 46, -86, 30, 31, 0, 65, 89, 17, -9, 169, 11, 43,
  37, 6, 97, 27, 25]

theorem fractionalNearFrameSubtreeG2R0491_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0491Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0491Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0491Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0491_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0491LowerBoundTable : List ℤ :=
  [48, 161, 283, -15, 46, 38, 315, -46, 112, 190, 328, 10, 9, 205, 638, 174,
  114, 162, -100, 108, -234, 202, 194, 239, 9]

def fractionalNearFrameSubtreeG2R0491LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0491Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0491LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
