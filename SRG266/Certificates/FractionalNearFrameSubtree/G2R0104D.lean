import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0104`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0104Mask : ℕ := 1281871276904963

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0104Witness : Array ℤ :=
  #[74, 66, 18, 77, 21, 62, -66, -206, -126, -119, -107, -150, 0, 55, 85,
  93, 117, -2, -35, 168, 141, 205, 63, 72, -104, 186, 145, 165, 66, -225,
  -267, -214, -129, -277, -1, 87, -10, 36, -94, -15, 66, 14, -50, -25, 126,
  26, 303, 35, -49, 13, -51, -56, 31, 20, 88, 91, 63, 221, -112, -18, -28,
  7, -9, 80, -17, 88, -2, -59, -122, -11, 20, 0, 100, 79, -113, -86, 12, -5,
  -25, 56, -1, 31, 65, -1, -77, -32, -202, 76, 5, 0, 55, -12, 34, 29, 131,
  102, 141, 69, -3, -32, -13, 33, 31, 12, 2, 2, 8, 0, -84, -12, -4, -67, 29,
  -48, -119, 242, -12, 43, -49, 24, 2, 34, 144, -82, 15, 31, 27, 1, 3, 20,
  27, 2, 64, 34, 52, 8, 45, 99, 8, -84, 15, -74, 17, 21, 88, 122, -44, -46,
  61, -17, 69, 50, -130, -52, 43, -96, 145, 72, -74, 25, 0, 104, -134, 46,
  -4, 151, 365, -240]

theorem fractionalNearFrameSubtreeG2R0104_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0104Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0104Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0104Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0104_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0104LowerBoundTable : List ℤ :=
  [81, 284, 324, -107, 1, 165, 1, 2, 199, 827, 68, 129, 101, -55, 307, 305,
  593, 48, 237, 112, 332, 44, -36, -317, 317]

def fractionalNearFrameSubtreeG2R0104LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0104Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0104LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
