import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0304`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0304Mask : ℕ := 5387246707130968

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0304Witness : Array ℤ :=
  #[-94, 56, -38, 10, 90, 28, -34, -6, 5, 82, -84, -8, 82, 1, -51, -22, -11,
  61, 25, 14, -24, -50, 4, 11, 38, 41, 146, 38, -4, 50, 86, 21, 0, -26, 0,
  -54, -6, -19, 129, 24, -11, -136, 87, -54, 74, 78, 2, 82, -31, -44, 38,
  62, 61, -11, -95, 33, 97, 25, 21, -64, -58, -3, -23, -39, 31, -235, -43,
  -12, 20, 47, 87, -70, 23, 113, 10, -3, 23, 31, -36, -66, 38, 66, 106, 48,
  -80, 17, -71, -42, -16, 81, -97, -96, 120, -9, -59, 71, -31, 22, -6, 10,
  76, -11, -140, 46, 47, 35, 19, -50, -36, -57, 50, 188, -19, 2, 5, 30, 15,
  11, 65, -32, -64, 21, 22, 24, 4, -97, 176, 31, -62, 40, -84, 20, 26, 22,
  -51, 77, 73, -105, 58, -29, 18, -26, -23, 56, 74, -79, 28, -62, 33, 128,
  16, 79, 25, -39, -108, -6, 113, -188, -23, 46, 69, 44, 98, 2, 154, -53,
  -293, 63]

theorem fractionalNearFrameSubtreeG2R0304_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0304Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0304Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0304Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0304_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0304LowerBoundTable : List ℤ :=
  [-17, 101, 1, 75, -22, 56, 116, 13, 93, 357, 157, 77, 377, 11, 469, 140,
  452, 90, -47, -44, 242, -58, 285, 11, -293]

def fractionalNearFrameSubtreeG2R0304LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0304Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0304LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
