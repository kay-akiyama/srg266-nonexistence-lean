import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0104Mask : ℕ := 5721631250655497

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0104Witness : Array ℤ :=
  #[-157, -249, -141, -65, 249, -156, -124, 2, 0, 159, 46, -203, 81, 17, 0,
  343, -85, -239, 0, 82, -151, -14, 152, -89, -156, 37, 10, 100, 25, -76,
  132, -16, 167, -28, -23, 236, 39, -95, -45, 0, -212, -213, 71, 30, 12, -2,
  48, -57, -3, 29, 19, -21, 45, -60, 0, -105, 38, 10, -102, -51, 34, 34, 7,
  65, 211, 124, -177, 214, 126, 90, -1, 114, -77, -51, 5, 4, 220, 116, -1,
  -51, 20, -89, -171, 50, 13, -43, -70, 81, 0, -34, -32, 88, -38, -131,
  -153, -27, -48, 91, 0, -61, 59, 34, 201, -57, 101, 58, 6, 69, 105, 86, 31,
  -61, 24, -79, 122, 53, -55, -25, -120, 139, 24, 60, 154, 36, 28, 97, -48,
  94, -39, 175, 138, 58, -96, 158, -50, 118, -41, -44, 95, -4, 6, -14, -25,
  92, 62, -99, 98, 37, 54, 153, -39, 68, -62, 24, 245, 41, 178, 178, 253,
  -136, -16, -66, 283, 34, 215, -165, -163, 188]

theorem fractionalNearFrameSubtreeG5R0104_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0104Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0104Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0104Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0104_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0104LowerBoundTable : List ℤ :=
  [117, 461, 304, -25, 105, -136, 61, 62, 143, 295, 573, 484, 799, 303, 360,
  117, 543, 10, -68, 9, 601, 523, 24, 560, -47]

def fractionalNearFrameSubtreeG5R0104LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0104Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0104LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
