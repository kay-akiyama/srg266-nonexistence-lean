import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0604`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0604Mask : ℕ := 7040959386326534

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0604Witness : Array ℤ :=
  #[-86, -38, -12, 7, -110, -138, 67, 9, -35, -8, 38, 20, 0, -34, 133, 6,
  -60, -35, -4, -94, -119, 49, -13, 18, 61, -30, 9, 15, 0, 55, 8, 21, -15,
  -55, -30, 65, 31, 71, 117, -19, -21, 22, 17, 14, 42, 14, 19, 45, 80, 34,
  21, -39, 33, -34, -93, -96, 31, -61, -63, -1, -8, -84, -39, -3, 49, 22, 0,
  -73, 71, 12, 29, 9, -73, 8, -37, -63, -72, -23, 70, 9, 62, -79, -68, -71,
  42, 44, 118, 56, 73, 55, -27, 57, -61, -72, 108, -22, 81, 62, 111, 113,
  12, -7, 47, -32, 104, -17, -26, 130, 78, -21, 74, 24, -30, -124, 8, 65,
  -49, 104, -68, -19, -16, -30, -49, -127, -58, -110, 108, 73, -57, 105,
  -53, -15, -34, -69, -100, 64, 101, 66, -117, -8, 109, -29, 38, 17, -29,
  -10, -40, 4, 75, 6, 88, -14, -112, -58, -68, 31, -64, -61, 143, 111, 1,
  56, 27, -50, -4, 71, 3, 59]

theorem fractionalNearFrameSubtreeG2R0604_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0604Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0604Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0604Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0604_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0604LowerBoundTable : List ℤ :=
  [-37, 3, 3, 12, 34, 3, 103, 1, -18, 365, 230, 9, 44, 315, -93, -89, -98,
  167, -8, 11, 305, 189, 10, -91, -24]

def fractionalNearFrameSubtreeG2R0604LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0604Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0604LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
