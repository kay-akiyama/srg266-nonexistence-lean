import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0186`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0186Mask : ℕ := 6866710651874828

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0186Witness : Array ℤ :=
  #[-85, -15, 0, -60, -26, 8, 107, 13, -86, -10, -2, 61, 223, 64, 144, 126,
  33, 79, 141, 55, 72, 60, 113, -51, 124, 47, -28, -166, -78, 10, -69, 5,
  -5, -31, 178, 73, -21, -42, 5, -50, 97, 65, 85, 11, -32, 39, 56, -31, -30,
  -126, 15, 91, 93, -161, -14, 138, 64, 13, 39, -42, 47, 138, -100, -47, 70,
  24, 85, 4, -100, 155, 108, 107, 39, 44, -113, -166, 24, -14, 29, -21, -20,
  -32, -75, 97, 155, -17, 104, -185, 38, -82, 134, 60, 75, 6, 58, 2, -82,
  99, 73, 24, 10, -114, 110, -40, 2, -33, 116, -125, 13, 7, -18, 117, -5,
  47, 31, -42, 17, -10, -23, 105, -32, 31, -34, -8, 134, -47, -15, 51, 19,
  -153, 96, 53, -87, 142, -19, 163, 116, 42, -94, -12, 17, -65, -40, -4,
  166, 58, -100, 28, 142, 6, 53, 0, 101, -74, -53, 38, 6, 6, 70, -45, 71, 9,
  -32, 0, -138, -43, -73, 40]

theorem fractionalNearFrameSubtreeG3R0186_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0186Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0186Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0186Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0186_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0186LowerBoundTable : List ℤ :=
  [128, 71, 4, 248, 139, 163, 112, 248, 287, 634, 416, 89, 16, 152, -155,
  463, 153, 21, 313, 222, 657, 344, 71, 203, 482]

def fractionalNearFrameSubtreeG3R0186LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0186Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0186LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
