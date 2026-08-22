import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0105`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0105Mask : ℕ := 1281879849800707

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0105Witness : Array ℤ :=
  #[12, -172, -225, -126, -151, -120, 150, 89, 78, 47, 21, 109, 0, -36, 184,
  -18, 93, -160, 62, 66, -48, -36, 79, 67, -32, 178, 28, -72, 71, -114, 0,
  -85, -86, 41, 189, 85, -23, -23, -111, 125, 203, 20, -48, -96, -124, -252,
  87, 5, 2, 126, 75, -200, -34, 8, 42, 81, -21, -27, 20, 62, 3, -8, 104, 4,
  43, 59, -31, 78, 54, 16, -19, 68, 69, -91, 45, 35, 131, -62, 80, 82, 70,
  108, 79, -78, 99, -18, -103, 6, 49, -101, 50, -72, -99, -15, 112, 82, 11,
  86, -34, 87, 40, -27, -110, -19, -11, 0, -41, -73, -47, 49, -170, -29, 16,
  -87, 13, 209, -62, 52, -20, -14, 108, 120, 124, -95, 102, -48, 23, 43, -1,
  -45, 38, 92, -6, -33, -38, -86, -215, 43, 64, -109, -26, 22, 109, 161,
  122, 134, -84, 49, 88, -40, -71, -62, -88, 196, -1, 6, 216, 81, -1, 53,
  30, 192, -5, -15, -33, 196, 169, 31]

theorem fractionalNearFrameSubtreeG2R0105_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0105Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0105Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0105Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0105_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0105LowerBoundTable : List ℤ :=
  [63, 298, 418, 2, 1, 114, 3, 377, -68, 342, 108, 404, 100, 307, -110, 556,
  175, 151, 168, 258, 12, 109, -358, 18, 1023]

def fractionalNearFrameSubtreeG2R0105LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0105Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0105LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
