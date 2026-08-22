import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0609`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0609Mask : ℕ := 7073667964704274

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0609Witness : Array ℤ :=
  #[18, 147, 94, 26, 12, -49, 60, -30, -17, -110, -155, 53, 60, 53, 143, 0,
  145, -67, 64, 14, -14, 125, 30, -111, 117, -87, 62, 74, 44, -88, -20, 4,
  -82, 44, -32, -80, 94, -55, 86, -21, -8, 40, 87, 60, 58, 28, -12, -96, -4,
  -24, 42, 85, -11, -191, -41, -34, -93, -32, 21, -13, 7, -29, 96, -38, -70,
  98, -28, -15, -39, -62, -25, 19, -23, 24, 42, -24, -20, 11, -59, 38, 2,
  60, -2, -11, 134, -27, -47, 181, -76, -28, 116, -12, -20, 23, -4, -98, 54,
  4, 90, 32, -154, -106, 76, 124, 153, 97, 30, 25, 70, 3, 0, -115, -30, -29,
  -10, 49, 93, 50, -37, 63, 138, 40, 15, -20, 16, 122, -20, 90, 112, 107,
  44, -53, 30, 68, -17, 40, 2, -35, 4, 79, 91, 12, -17, 83, -1, 54, 3, 37,
  67, 18, 39, 58, -19, -3, -5, -25, 51, -43, -47, -34, 17, -78, -55, -28,
  -56, -74, 13, -32]

theorem fractionalNearFrameSubtreeG2R0609_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0609Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0609Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0609Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0609_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0609LowerBoundTable : List ℤ :=
  [41, 156, -111, 1, 106, -14, 378, 136, 151, 168, 481, 225, 90, 168, -93,
  -194, 162, 56, 10, 399, 203, 411, 188, 683, 203]

def fractionalNearFrameSubtreeG2R0609LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0609Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0609LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
