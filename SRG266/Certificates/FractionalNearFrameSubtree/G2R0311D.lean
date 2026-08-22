import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0311`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0311Mask : ℕ := 5388384123589282

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0311Witness : Array ℤ :=
  #[12, -31, 12, -48, 17, -39, 0, -119, -61, -60, -45, -6, 53, 42, 101, 51,
  65, -55, -43, -39, -78, -21, -61, -42, -86, -70, 70, 130, 86, 31, -37, 37,
  80, -134, -94, -3, 79, -12, -23, -32, 100, -21, 41, 44, 64, 75, -183,
  -136, 141, 53, 56, 28, -67, -10, 14, -16, 9, -11, -72, 96, 47, -38, -49,
  26, 118, 73, -87, 56, -38, 45, -41, 30, 14, -10, -30, 47, -58, 4, 39, 31,
  36, -17, 80, -2, -95, 31, -4, -7, 11, 10, -76, -21, 88, 92, -97, -110, -4,
  -44, -53, 45, -105, 3, 104, 124, 62, 31, 8, 20, -92, 3, 0, 26, -1, -50,
  -36, 3, 52, -11, -44, 74, 100, 71, 49, -33, 72, 4, -69, 70, 29, -45, 0,
  26, 45, 85, 47, 20, -30, 74, -40, -17, 100, -38, 27, 38, -34, 36, 12, -49,
  39, 25, 93, -9, 9, 45, 16, -27, -91, -75, 14, 21, 21, -11, -101, -27, -82,
  -64, 42, -112]

theorem fractionalNearFrameSubtreeG2R0311_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0311Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0311Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0311Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0311_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0311LowerBoundTable : List ℤ :=
  [-12, 58, 37, 3, 2, 2, 1, 2, 62, 179, 93, 11, 214, 100, 61, -9, 9, -83,
  -145, -135, 141, 256, 33, -174, 168]

def fractionalNearFrameSubtreeG2R0311LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0311Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0311LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
