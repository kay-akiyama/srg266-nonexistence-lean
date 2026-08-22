import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0007`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0007Mask : ℕ := 268054952810641

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0007Witness : Array ℤ :=
  #[-215, -181, -207, -160, -183, -158, -102, -66, -107, -4, -42, -11, 223,
  231, 204, 249, 231, 220, 39, -1, 83, -9, 65, 4, 30, 38, 37, 95, -30, -133,
  -57, -144, 23, -4, 13, -29, -45, 32, 19, -57, -25, 49, -69, 85, 59, 39,
  22, -14, 146, 30, 4, 96, 46, -44, 26, 120, 11, -48, 12, 82, -47, 120, -39,
  -13, 86, 47, 67, 4, 10, -13, -12, -7, -46, 113, 70, -50, 6, 33, 27, 17,
  72, -69, 5, 52, 16, 22, 5, -17, -27, -17, -17, 41, -102, -70, -95, -2, 39,
  49, -17, -4, -44, -19, 4, 2, 31, -4, -64, -67, 11, -71, -57, -99, -38,
  -49, -65, 205, 175, 41, 35, 69, 56, -44, 7, 68, -41, 17, 56, -64, 65, 13,
  25, -87, -49, -10, 61, 65, -128, 4, 43, -180, -77, 4, 76, 94, -11, 49, -3,
  20, -18, 63, 91, -2, 101, -54, 23, -45, 54, 61, -94, -30, 59, 36, -34, 69,
  25, -4, 12, -8]

theorem fractionalNearFrameSubtreeG3R0007_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0007Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0007Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0007Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0007_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0007LowerBoundTable : List ℤ :=
  [29, 78, 136, -9, -27, 84, 25, -74, 149, 315, 207, -143, 161, 285, -93,
  221, 95, 72, -56, 93, 278, 230, 196, 296, 146]

def fractionalNearFrameSubtreeG3R0007LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0007Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0007LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
