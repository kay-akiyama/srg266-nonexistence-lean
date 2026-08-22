import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0616`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0616Mask : ℕ := 9609554158670097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0616Witness : Array ℤ :=
  #[-8, -29, -60, -102, -123, -116, 0, 111, 103, 25, 5, 44, 22, 35, 128,
  -10, 0, 47, -113, -61, 16, 23, -91, -58, -67, 15, 19, 68, 7, -20, 30, 244,
  30, 66, -49, -61, 10, -50, -37, -95, 201, 135, 123, 123, 50, -211, 94, -6,
  -59, -54, 43, 96, 31, -15, 10, -2, 48, 1, 47, 54, -11, 23, 29, 14, 37, 5,
  -75, 3, 102, -17, -4, 17, -14, -41, 50, 23, -2, -27, -50, 25, 23, -12,
  -11, -15, -1, 26, 36, 19, 43, 4, 53, 69, 37, 3, 56, 45, 54, 32, 32, 41,
  -16, 82, -25, -2, 1, 76, 57, 26, 52, 45, -24, 50, 74, -13, -13, 76, -72,
  -68, 23, 9, 42, 21, 113, 9, 5, -15, -2, 28, -14, 43, -14, -69, 5, -40, -8,
  163, -17, 15, -54, 19, -13, 23, 36, 21, 12, 75, -18, -15, 167, -15, 24,
  24, -28, 8, -7, -44, 27, 4, 47, 9, -118, 13, -144, -81, 7, -41, -41, -154]

theorem fractionalNearFrameSubtreeG2R0616_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0616Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0616Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0616Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0616_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0616LowerBoundTable : List ℤ :=
  [77, 2, -52, 286, 117, 92, 2, 216, 40, 9, 78, 123, 40, 198, -12, 293, 109,
  272, 622, 153, 257, 9, 17, 108, 326]

def fractionalNearFrameSubtreeG2R0616LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0616Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0616LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
