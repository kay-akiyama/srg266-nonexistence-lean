import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0453`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0453Mask : ℕ := 5794198866481832

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0453Witness : Array ℤ :=
  #[-35, 67, -57, 82, 109, -40, 65, 45, -61, 37, 3, -37, -20, -53, -52, 40,
  34, 18, 84, 27, 76, 104, 61, -3, -87, -66, -55, -112, 2, -79, -37, 16, 34,
  -27, -60, 79, 39, -18, -6, 76, -21, -113, 38, 20, 110, 33, -13, -13, -19,
  -73, -54, 36, -5, 25, 39, -19, -19, -2, 35, -26, -57, 105, -119, -31, -98,
  -42, -62, -41, 209, 93, -84, 88, 130, 6, 41, -26, -31, -48, 0, 25, 59,
  -35, 6, -21, 61, -47, 60, 8, -72, 33, 42, 38, 61, 114, 8, -106, -58, -22,
  -31, -129, 18, -1, -63, 27, -37, -37, -63, 13, 58, 68, 42, -44, -1, -47,
  -55, -77, -69, -22, 0, 71, -154, -59, -40, -7, 12, 0, -8, 69, -53, -27,
  11, 46, 1, -48, -121, 59, -92, 138, -92, 57, -5, 57, -3, 23, 7, -12, 9,
  -77, -51, 2, -55, -80, -6, 23, 12, 4, 0, 60, 83, 59, -4, 127, -16, 33, 72,
  45, 91, -30]

theorem fractionalNearFrameSubtreeG2R0453_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0453Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0453Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0453Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0453_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0453LowerBoundTable : List ℤ :=
  [-49, -3, 8, 1, 79, 25, -85, -56, -8, -38, -192, 111, -160, 162, -118,
  140, 11, 75, 241, 24, 317, -10, 171, 10, -204]

def fractionalNearFrameSubtreeG2R0453LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0453Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0453LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
