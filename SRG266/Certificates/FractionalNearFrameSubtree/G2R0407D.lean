import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0407`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0407Mask : ℕ := 5742489130047920

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0407Witness : Array ℤ :=
  #[29, 0, 24, -66, -122, -14, 40, -9, -11, -5, 70, 104, 60, 2, 73, 3, 76,
  -30, 14, 24, 36, -45, 1, -115, 39, -22, -9, 16, -25, -1, -25, 17, 10, -49,
  29, 8, -36, 89, -33, 53, 54, 101, -38, -49, 122, 89, -17, -43, 7, 9, 57,
  -28, -50, 57, 29, -43, -16, -55, -13, -1, 53, -100, -56, -30, -5, -2, 85,
  14, -80, 13, 4, 31, 32, 141, 94, -31, 1, 50, 38, -15, -56, 15, -8, -23,
  37, -35, 10, -22, -30, 105, -26, 33, 76, 50, -6, 12, 54, 30, -51, -90, 91,
  105, 64, 67, 22, -1, 33, -50, 34, -84, -22, 5, 74, 43, 63, 30, 86, 39, 52,
  27, 35, 20, 120, -96, -21, -77, -34, 16, 12, 17, -26, 30, 51, -49, 40,
  -27, -16, -16, -60, 80, -69, -67, 99, -82, -48, 37, -83, 118, -21, 86, 97,
  58, 43, -15, 73, 54, -29, -49, -78, -57, 56, -8, 47, -45, 53, 63, -102, 2]

theorem fractionalNearFrameSubtreeG2R0407_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0407Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0407Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0407Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0407_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0407LowerBoundTable : List ℤ :=
  [83, 37, 44, 99, 151, 101, 2, 164, 56, 361, 92, 177, -97, 313, 55, 147,
  -4, 9, 56, 299, 44, 324, 273, 288, 155]

def fractionalNearFrameSubtreeG2R0407LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0407Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0407LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
