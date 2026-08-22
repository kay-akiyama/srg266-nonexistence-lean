import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0041`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0041Mask : ℕ := 955873587201094

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0041Witness : Array ℤ :=
  #[-65, 88, 2, 49, 48, 128, 5, -44, -107, -245, -218, 77, 146, 137, 33,
  314, 13, -52, 104, 182, -12, 364, 15, 225, 42, 44, 46, -137, -53, -195, 0,
  -413, -108, 61, -99, 106, 101, 128, 157, -128, -155, 272, 37, 44, -105,
  24, -48, -134, -73, -57, 29, 20, 0, 179, 147, 19, 52, 97, 211, 1, 104,
  239, -9, 153, -31, -33, -261, 61, 90, -16, 0, -40, 14, 42, -74, -57, 94,
  -147, -8, -63, 44, 104, 68, 38, 35, -70, -42, -28, 20, -112, 15, -92, 118,
  -12, -75, 16, 9, 67, -98, 148, -153, 12, -45, 86, -38, -37, 35, 138, 122,
  -10, 50, -103, 54, -72, -51, -171, -111, 50, -172, 76, 132, 144, -96, 125,
  -30, 45, -154, 60, 24, 87, 8, 202, 21, 186, -147, 179, -19, -33, 47, -74,
  -33, 7, 3, -197, -47, 103, 115, 54, 11, 155, -37, -13, 95, 40, -50, 10,
  88, -61, 57, -38, 118, -83, 5, -154, 104, 243, 3, 219]

theorem fractionalNearFrameSubtreeG3R0041_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0041Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0041Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0041Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0041_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0041LowerBoundTable : List ℤ :=
  [48, 277, 52, 0, 283, 2, 19, 247, 337, 379, 437, 302, -71, -223, 202, 674,
  71, 333, 262, 28, 495, 121, 9, 462, 710]

def fractionalNearFrameSubtreeG3R0041LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0041Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0041LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
