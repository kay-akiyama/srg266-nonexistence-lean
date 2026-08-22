import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0116`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0116Mask : ℕ := 5388415928994594

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0116Witness : Array ℤ :=
  #[-30, -33, 27, 28, 64, 70, -112, -190, -57, -64, -78, 24, 71, 85, 120,
  -14, -61, -45, 2, 11, 44, -16, -65, 18, 37, 69, 0, 39, -5, 56, 33, -34,
  -32, 40, 8, 61, -31, 17, 14, -15, -25, 32, 67, -2, 39, -22, 7, -18, 25, 8,
  -16, 0, -23, -39, 112, 26, 10, 10, 0, -107, -116, 9, 38, 37, 64, -172, 6,
  -17, -58, 58, 14, 11, -8, -40, 33, -5, 4, -95, -5, 36, 26, 13, 1, -41,
  -30, 38, 41, 53, -54, 2, -39, 17, -11, 47, 1, -36, -95, -9, 21, -7, -7, 4,
  18, 1, -70, -11, -15, 43, 14, 102, 45, 106, 20, 54, -35, 58, 30, -16, 1,
  -26, 38, 189, 96, -62, -12, -18, -65, -1, 23, -5, -33, -23, -40, -14, -55,
  -1, 41, 20, -53, 23, 20, -26, -42, 4, 54, 38, -11, 5, -52, -7, 62, 14, 41,
  -19, -1, -91, 64, 4, -54, -23, -39, -97, 33, -23, 9, -2, -183, 0]

theorem fractionalNearFrameSubtreeG3R0116_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0116Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0116Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0116Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0116_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0116LowerBoundTable : List ℤ :=
  [-54, 1, -167, 3, 73, -22, -24, 97, -30, 98, 10, 71, 97, -124, 10, 52, 23,
  10, 35, 9, 79, 72, -106, -13, 10]

def fractionalNearFrameSubtreeG3R0116LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0116Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0116LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
