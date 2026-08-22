import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0343`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0343Mask : ℕ := 5668754362640905

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0343Witness : Array ℤ :=
  #[-378, -108, -120, -151, -126, -128, -20, 0, 6, 38, 92, 37, 96, 72, 103,
  77, 108, 191, 72, -99, 105, 16, -59, -57, -43, 48, 26, 111, 21, -1, -84,
  37, -199, 1, -49, -42, -101, 31, 78, 88, 42, -42, -36, 8, 120, -135, -183,
  29, -5, 154, 96, 185, 15, 35, 42, 83, 147, 171, 95, 20, 64, 49, 93, -49,
  -93, -33, 44, 22, -122, -115, 120, -73, -12, 2, 25, 19, 79, -27, -76, 22,
  -31, 85, 42, -11, -21, 75, -66, 3, 4, 43, 42, 86, 40, 44, -45, 46, 3, 95,
  24, 12, -10, 178, 70, 61, 50, -43, -10, 63, -3, 45, 15, -23, 6, -1, -30,
  -18, -71, -84, -40, 203, 19, 48, -15, -14, 101, 20, 83, -75, 15, -2, -8,
  38, 45, 7, -31, -79, 1, 60, -84, -47, -11, 35, -28, 30, -28, -88, -5, -97,
  -55, 2, 79, 142, 57, -30, 22, 127, -2, 13, 23, 80, -16, -33, -36, 27, -2,
  -18, 1, -99]

theorem fractionalNearFrameSubtreeG2R0343_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0343Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0343Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0343Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0343_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0343LowerBoundTable : List ℤ :=
  [53, 28, 91, 245, 107, 149, 0, 1, 1, 339, 10, 95, 103, 70, -32, 49, 48,
  81, 169, 341, 252, 128, 442, 168, 326]

def fractionalNearFrameSubtreeG2R0343LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0343Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0343LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
