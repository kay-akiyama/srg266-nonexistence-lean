import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0623`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0623Mask : ℕ := 9749070739129106

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0623Witness : Array ℤ :=
  #[-4, -8, 15, 16, 21, -48, -59, -71, 125, 6, -18, -39, -70, -28, 52, 0,
  -23, -11, -8, 6, -55, -51, -36, -37, -12, 86, 52, 27, 39, 57, 137, 96, 63,
  -107, 10, -71, -104, -89, 9, 75, -43, 80, -23, -67, 45, 14, 34, 20, -181,
  -101, 19, 37, -23, 1, -21, 128, 186, 31, 13, -22, 13, -8, 12, -9, -4, 30,
  -3, -31, -25, 43, 24, -43, 38, -47, -43, 14, -53, 59, 13, -1, 5, -4, -39,
  41, -7, 65, 24, 22, 44, 25, -18, -4, -17, -10, -46, 39, 1, 66, 17, -11,
  61, 42, 91, 64, 0, -51, 43, 0, 42, -84, -44, 4, 56, 165, -49, 12, 5, 47,
  29, 36, 99, -55, 6, -5, 54, 39, 45, -7, -24, -46, -13, -22, -74, 66, 23,
  -86, -65, -81, -87, -83, 7, 38, 11, 0, 24, 4, 51, -26, -15, 58, 38, -10,
  4, 2, 56, 14, -3, -16, 7, 13, 17, 59, -4, -16, 49, -17, -75, -97]

theorem fractionalNearFrameSubtreeG2R0623_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0623Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0623Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0623Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0623_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0623LowerBoundTable : List ℤ :=
  [27, 160, 156, 1, 74, 81, 16, 2, -110, 15, 62, 78, 36, 10, 140, 97, 209,
  123, -52, 198, 166, 9, -295, -55, -60]

def fractionalNearFrameSubtreeG2R0623LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0623Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0623LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
