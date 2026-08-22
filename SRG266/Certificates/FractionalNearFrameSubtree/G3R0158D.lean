import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0158`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0158Mask : ℕ := 6850692102269608

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0158Witness : Array ℤ :=
  #[2, -75, -82, 45, -130, 51, -89, 127, 37, 9, 117, 78, 151, 213, 157, 178,
  154, 173, 82, 4, 220, -10, 104, 158, -129, -217, -101, -337, 154, 183, 91,
  23, -20, 46, 108, -33, -92, -198, -23, -173, 40, -50, 171, 55, 9, 206,
  -259, -147, -58, -286, 165, 4, 210, 66, -128, -14, 203, -148, 38, 95, 128,
  -41, -62, 44, 191, -1, -38, 94, -59, -118, -99, -86, 12, -45, -87, -85,
  -60, 121, -37, 242, -38, 10, -8, 146, 86, -36, -39, -181, 76, -118, -12,
  41, 18, -237, -8, 45, 104, -166, 104, 124, 13, 11, -13, -111, 130, -55,
  -5, 1, -47, -21, -60, -24, 7, -108, 10, -91, -146, -191, 234, 70, 200,
  -130, 120, -86, 2, -73, -15, -27, -10, -37, 140, 159, 15, 118, 84, -120,
  172, -6, 116, -384, 71, 12, -37, 34, 5, 133, 76, 61, -41, 113, -8, -118,
  149, 179, 69, -69, 112, -288, 6, 174, 61, -173, -65, 208, 67, 173, 26,
  161]

theorem fractionalNearFrameSubtreeG3R0158_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0158Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0158Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0158Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0158_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0158LowerBoundTable : List ℤ :=
  [16, 195, 148, 97, 18, 2, 21, 239, 2, 506, -315, 339, 175, -99, 466, 444,
  -593, 464, -194, 706, 305, 11, 882, 273, 584]

def fractionalNearFrameSubtreeG3R0158LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0158Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0158LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
