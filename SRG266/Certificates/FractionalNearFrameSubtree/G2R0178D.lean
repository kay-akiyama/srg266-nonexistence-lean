import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0178`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0178Mask : ℕ := 1386797329236184

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0178Witness : Array ℤ :=
  #[-11, -41, 20, 1, 28, 31, -44, 45, -40, 31, 14, 31, -12, -14, 111, 1, 77,
  74, 132, 17, -80, 52, -49, -21, -134, -67, -116, 23, 46, -52, -4, 28, 69,
  -49, -121, -10, -7, 55, -38, 29, 44, 9, -61, -9, -38, 82, 23, 19, 35, 89,
  -22, -25, -3, -35, 8, 61, 17, -17, 49, -29, 13, -50, -1, 63, 46, 58, 4,
  -51, -80, 147, 35, -40, -48, 2, 88, 26, 113, 86, 39, -21, 2, 68, -49,
  -110, -109, -48, -3, 51, -30, -24, -30, 33, -62, 34, -38, 51, -48, -13,
  -47, 101, -31, 29, 97, 75, -85, 6, -28, 21, -66, -45, -33, -50, 11, -50,
  31, -3, -42, -80, 76, -58, -19, 98, 7, 101, -33, -33, -11, 17, 98, -4,
  -60, 48, 45, 63, -26, -24, 67, -49, -96, -56, -11, 19, 27, -50, -40, -4,
  -76, -14, -20, 9, 158, 35, 11, 36, 25, -23, 49, -28, -55, 43, -52, 4, 15,
  72, 117, 26, 85, 93]

theorem fractionalNearFrameSubtreeG2R0178_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0178Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0178Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0178Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0178_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0178LowerBoundTable : List ℤ :=
  [-34, 83, 89, 98, 1, 81, -71, -34, 2, 399, -149, 59, -107, 245, 9, 9, 85,
  240, 353, 455, 83, -86, -120, 9, 248]

def fractionalNearFrameSubtreeG2R0178LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0178Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0178LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
