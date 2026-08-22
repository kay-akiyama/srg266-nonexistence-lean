import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0372`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0372Mask : ℕ := 5737061270888842

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0372Witness : Array ℤ :=
  #[-17, 29, -39, -42, -7, -37, 66, 71, 32, 0, 47, -46, 17, 37, -13, -43,
  66, 46, -53, -39, -39, 13, 44, 27, 14, -12, 56, -33, 27, -15, 109, 95,
  -13, -27, -109, 19, -32, -10, -31, -19, 25, -7, 41, 8, 60, -10, -23, -19,
  10, -36, -3, -76, 1, -15, 1, 6, -14, 32, 69, -12, -27, 56, -16, -54, 8,
  45, -55, -11, -83, -76, -26, 37, -7, -1, 54, 52, -8, 7, -6, 36, -55, -42,
  52, 12, -12, -4, 54, 26, 17, 34, -10, 46, 33, -65, 25, 15, -8, -37, -43,
  46, 24, 11, -11, 0, 26, 59, -7, 17, 36, -27, -34, -50, 1, 1, -21, 6, 42,
  -34, 64, -42, -82, -58, 51, -6, 11, -44, -18, -10, 45, 12, 39, 30, -38,
  61, 25, -12, 35, 50, 6, -17, 14, 22, 14, -18, -9, 0, 27, 56, 48, -11, -17,
  -1, -52, 18, 74, -76, -1, -16, 4, -49, 3, -26, 47, 15, 44, 17, 5, 37]

theorem fractionalNearFrameSubtreeG2R0372_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0372Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0372Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0372Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0372_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0372LowerBoundTable : List ℤ :=
  [-3, 50, 45, -7, -24, 33, 36, 33, 23, -2, 243, 34, 24, 76, 222, 201, -11,
  11, 82, 8, -78, -131, 29, 234, 203]

def fractionalNearFrameSubtreeG2R0372LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0372Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0372LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
