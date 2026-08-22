import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0090`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0090Mask : ℕ := 1213640151121993

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0090Witness : Array ℤ :=
  #[-34, -107, -61, -83, -98, -8, 0, 18, 46, -2, 58, 74, 0, 24, -70, -25,
  26, 143, 30, -4, 33, -87, -128, -27, 56, 6, -42, -12, 0, -17, 79, 19, -1,
  11, -17, -13, 62, 61, -216, -140, -92, 38, 39, 101, 230, -155, -33, 66,
  68, -15, 8, -40, -9, 22, -62, -98, 67, -43, 28, -53, 42, 77, -1, 23, -25,
  -3, -87, 57, -21, 30, 95, -5, -32, -39, -118, 6, -81, 92, -54, 25, 47, -2,
  74, 27, 0, 89, 1, 126, 71, 44, -7, 46, -26, -27, -33, 14, 11, 152, 31, 20,
  -70, -1, 116, 30, 70, -6, -74, -26, -70, -68, -61, -31, -57, -6, 73, -13,
  112, 54, 25, -96, 77, 13, -49, 65, 20, -70, -6, -81, 43, 23, -39, -42, 1,
  -58, 31, 1, -53, -28, 23, 8, -66, 132, -1, 8, -17, -88, 29, 36, -27, 70,
  -53, -60, -70, -10, 0, -79, 44, -18, 6, 103, -51, 44, -4, 118, 25, -37,
  -92, -66]

theorem fractionalNearFrameSubtreeG2R0090_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0090Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0090Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0090Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0090_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0090LowerBoundTable : List ℤ :=
  [-58, -73, 0, 100, -98, 21, 2, -21, -79, -245, -130, -23, 99, 101, 210,
  172, -290, 41, -23, 193, 305, 105, -230, 184, 97]

def fractionalNearFrameSubtreeG2R0090LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0090Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0090LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
