import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0119`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0119Mask : ℕ := 1310254267484705

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0119Witness : Array ℤ :=
  #[-190, -48, -183, -71, -102, -50, 44, 86, -11, 122, 34, 165, 37, 93, -80,
  34, 0, 156, 83, 0, -68, -7, -23, 53, -10, 1, -78, -87, 75, -20, 11, 100,
  0, 19, 5, 9, 13, -9, 35, 51, -15, 2, 32, -53, 43, 80, 46, -25, -8, 7, -10,
  1, -15, -19, 52, 34, 59, 24, -7, 43, 5, 121, 9, 110, -59, -36, 15, 12,
  -25, -21, -17, -18, 23, -13, 36, 35, 80, -12, 43, 24, 18, -38, 14, -9, 14,
  35, -2, -21, 27, 8, -26, -12, 49, 30, -19, 91, -52, 12, 40, -49, 16, -18,
  37, 25, -51, -5, -41, -25, 74, -59, 57, -43, -65, -59, 57, 45, 127, 74,
  37, 39, 3, 31, -66, 0, 24, 0, -2, 74, 18, -10, 47, -7, 37, 0, 41, -54, 29,
  26, -5, -64, -49, -8, 55, 15, 33, 87, 65, 1, 74, 30, -47, -34, -4, 3, 1,
  75, -23, -22, 11, -65, -22, 73, 30, 56, 5, -32, -29, -49]

theorem fractionalNearFrameSubtreeG2R0119_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0119Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0119Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0119Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0119_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0119LowerBoundTable : List ℤ :=
  [90, 70, 83, 37, 3, 251, 207, 3, 2, 367, 102, 227, 69, 1, 42, 151, 355,
  -90, 99, 56, 43, 110, -1, 507, 302]

def fractionalNearFrameSubtreeG2R0119LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0119Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0119LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
