import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0524`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0524Mask : ℕ := 6771601635529233

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0524Witness : Array ℤ :=
  #[-105, -143, -87, -109, -182, 0, -112, 91, 18, 19, 207, 82, -80, 99, 38,
  81, 9, 168, 4, -13, 13, -54, -17, 0, 36, 40, 28, 19, -44, -21, -88, -7,
  -8, -5, 32, -29, -3, 145, 16, -23, 22, 45, -34, 8, -55, 41, 91, 13, 8, 9,
  0, -17, 33, 48, 0, 4, 0, 1, 35, 40, -78, 47, -29, 76, 14, 16, 20, 21, 2,
  -56, -46, -60, -15, -16, -34, 88, -12, 4, 30, -79, -8, -25, -112, 18, 62,
  -59, 22, -19, 16, 25, -23, 15, -6, 7, 42, 65, 11, 49, 15, 51, 42, -5, 19,
  -91, -68, -248, -85, -69, -158, -104, 55, 72, 164, 126, 16, -13, -31, -26,
  7, 22, 35, 113, -23, 13, 108, -4, 14, -96, -50, -41, 54, -17, 38, -5, -33,
  18, -65, -61, 37, 10, 16, 125, 20, 123, 28, -34, -35, -142, 38, -33, 2,
  -49, -20, 0, 129, 95, 8, 29, 0, 2, -4, -35, 49, 8, 16, 33, -61, 23]

theorem fractionalNearFrameSubtreeG2R0524_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0524Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0524Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0524Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0524_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0524LowerBoundTable : List ℤ :=
  [-43, 58, 73, -79, 88, 213, -228, 2, 20, 10, 5, 227, 49, 46, 69, 10, 296,
  -154, -253, 0, 193, -137, 364, 10, 213]

def fractionalNearFrameSubtreeG2R0524LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0524Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0524LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
