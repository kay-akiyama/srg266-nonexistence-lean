import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0397`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0397Mask : ℕ := 5740368101753250

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0397Witness : Array ℤ :=
  #[-98, -115, 6, -13, -98, 112, 41, -25, 93, 186, 88, -88, -38, -48, -232,
  5, -134, -30, -143, -68, -41, -96, -13, -41, 98, -185, 139, 22, 199, 133,
  -124, 13, -27, 25, 65, 72, -19, -113, -22, 0, -43, 206, -84, 127, 99, 61,
  -159, -9, -119, -133, -91, -44, 45, 267, -159, 92, -56, -61, -97, 95, 44,
  -96, -87, 139, 166, 65, 6, -63, 133, 63, 14, 125, -190, -57, 14, 42, -60,
  21, -114, -152, 156, 76, -25, -1, -92, 25, 0, -39, -142, 6, 32, -34, 0,
  267, -64, 54, -53, 36, -275, -155, 132, -108, 67, -34, 7, 0, -27, 77,
  -217, -99, -2, -26, -42, 245, 30, -47, -103, 107, 8, -115, 18, -79, 27,
  48, 194, 6, 8, 49, -100, 256, 153, 127, 50, -59, -188, -65, -98, -128, 82,
  87, 131, -53, -143, 143, 104, 6, -149, 0, -137, 54, -48, 32, 234, -104,
  -136, 65, 189, -55, -111, 117, -7, -85, -46, 89, 62, 112, 26, -139]

theorem fractionalNearFrameSubtreeG2R0397_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0397Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0397Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0397Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0397_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0397LowerBoundTable : List ℤ :=
  [-136, -44, 84, -347, -4, -110, 74, -122, -162, 174, 520, 361, -77, 529,
  660, -142, 404, -473, -249, -444, -306, 9, 367, 223, -253]

def fractionalNearFrameSubtreeG2R0397LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0397Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0397LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
