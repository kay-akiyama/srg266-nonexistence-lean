import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0068`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0068Mask : ℕ := 828789646084888

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0068Witness : Array ℤ :=
  #[-40, -19, -23, 23, -19, -88, -31, -9, -81, 59, 2, 33, 55, 21, -78, -14,
  -80, -2, 41, -29, 15, -4, 63, 26, -32, 96, 57, 33, 10, 5, 7, -20, -19, -1,
  22, -19, 46, -37, -98, 59, 60, 46, -51, 36, 26, 34, 16, 35, -24, -8, 8,
  -33, 29, 44, -20, 53, 0, -6, -25, -12, -5, 24, -59, 3, -22, -27, 45, 42,
  44, 92, -7, 25, 34, -11, 28, -67, 95, -36, 84, -8, -42, -23, 6, -37, 9,
  115, 21, -50, -19, -28, -30, 20, 22, 56, 87, 76, 32, 15, -11, -16, -11, 6,
  13, -39, -18, -74, -43, 63, -26, 50, 0, 121, 55, 19, 54, 0, 84, 64, 7, 74,
  -66, -41, -24, -32, -17, 34, 70, -18, 54, -75, -8, 59, 44, 77, 6, -14, 15,
  9, -31, 21, 62, -8, 1, 9, 117, -5, -8, -12, -55, 54, -32, 14, -8, 8, 45,
  76, 6, 27, -17, 73, 0, -7, -42, 28, 30, 48, 96, 24]

theorem fractionalNearFrameSubtreeG1R0068_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0068Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0068Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0068Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0068_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0068LowerBoundTable : List ℤ :=
  [61, 189, 50, 131, 148, 2, 223, -43, 71, 61, 402, -4, 224, 331, 228, 18,
  127, 461, 224, 68, -35, 96, 53, 237, 33]

def fractionalNearFrameSubtreeG1R0068LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0068Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0068LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
