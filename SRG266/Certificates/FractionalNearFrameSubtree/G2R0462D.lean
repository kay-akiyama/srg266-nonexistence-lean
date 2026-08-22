import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0462`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0462Mask : ℕ := 5807428941320594

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0462Witness : Array ℤ :=
  #[-42, 46, -70, -13, -31, -92, -28, 74, 29, -22, -3, -39, -20, 103, 2, 15,
  28, 111, 22, 48, 34, 102, -18, 53, 4, -4, 42, -91, -92, -23, 3, 22, -63,
  35, -22, 54, 64, 12, -52, 72, 89, 15, 141, 77, 40, -28, -146, 18, 21, 1,
  35, -54, -132, 16, -37, 25, -13, 99, -67, 2, 60, 14, -50, -121, 34, 17,
  -17, 45, 16, 5, 0, 50, 4, -39, 75, 50, -12, 52, -71, 11, -43, 47, 11, 0,
  11, 8, -9, 17, 26, -16, 2, -18, 4, 3, 56, 7, 51, -36, 100, -42, -2, 39,
  124, 98, -46, 72, 102, -24, 71, 55, 100, 198, -59, 6, -16, -9, -9, 37, 60,
  39, 10, -86, 11, -62, -61, -23, 63, 8, 11, -22, -32, 64, -58, -58, 57, 64,
  -29, 21, -8, -9, 55, -19, -4, 45, 95, -17, 12, 33, 21, -45, -49, 56, 193,
  -127, -67, 28, -119, 88, -92, 42, 80, 40, 12, -61, 36, -18, -19, 38]

theorem fractionalNearFrameSubtreeG2R0462_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0462Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0462Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0462Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0462_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0462LowerBoundTable : List ℤ :=
  [53, 62, 148, 2, 215, -3, 149, 1, 72, 10, 743, -241, 106, 324, 262, 82,
  65, 86, 213, 162, -22, 231, 288, 541, 32]

def fractionalNearFrameSubtreeG2R0462LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0462Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0462LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
