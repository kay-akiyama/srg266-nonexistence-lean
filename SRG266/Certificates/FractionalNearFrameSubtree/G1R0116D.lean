import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0116`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0116Mask : ℕ := 969502726359272

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0116Witness : Array ℤ :=
  #[-57, -86, 6, 6, -39, -21, 34, -25, -54, -35, 56, 48, 54, 19, -29, -70,
  -1, 5, -29, 33, 37, 54, -12, -24, 8, -53, -67, -17, -39, -133, -57, -106,
  62, 63, -35, 0, 73, 88, 74, 0, 17, -19, -124, -89, -86, -17, 15, -9, 74,
  32, 62, 51, -20, 56, 46, 83, -52, 56, -16, 50, 59, -70, -37, -53, 76, 14,
  -74, 25, 15, -7, -5, -35, -32, 6, -30, 17, -23, -26, 72, 12, 0, -20, 77,
  42, 31, 80, 38, 20, 48, -5, 82, 10, 21, 2, -19, -46, -15, -5, -13, 7, -13,
  31, 37, 23, 65, 41, -21, 20, -8, 37, -3, -26, 31, -75, -13, 52, -14, -36,
  -47, 26, 22, 3, 40, -41, -39, 27, 23, -50, -34, 23, -22, -26, -118, -41,
  48, -21, -6, 72, 45, -11, 0, 95, 25, 2, 37, 35, -22, 35, -44, 14, -11,
  -34, 2, -76, 30, 26, 30, -23, -11, 15, -8, 20, 33, -16, 30, -27, 35, 24]

theorem fractionalNearFrameSubtreeG1R0116_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0116Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0116Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0116Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0116_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0116LowerBoundTable : List ℤ :=
  [-37, 1, 71, 61, -54, -17, 25, 32, 2, 180, 216, -41, 134, -148, 242, 55,
  45, 210, 66, 76, 129, -68, -158, -62, -20]

def fractionalNearFrameSubtreeG1R0116LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0116Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0116LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
