import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0043`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0043Mask : ℕ := 956355154086306

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0043Witness : Array ℤ :=
  #[-182, -139, -107, -192, -126, 26, 55, -12, 92, -113, 150, 30, 164, 111,
  198, 252, -125, 103, 82, -36, 65, -20, 32, -46, -76, -157, 50, -50, 254,
  -146, -52, -63, -1, 47, -130, 136, 174, 317, -115, -125, 142, 160, 37, -5,
  73, 54, -19, -60, -30, -4, 309, -62, -71, 106, 29, -103, -78, -46, 35,
  -78, -62, 128, 65, -78, 40, 38, -128, 70, 17, 131, 59, -243, -57, 209, 28,
  -22, 73, 35, 21, 255, -68, -25, -96, 127, -254, 34, 177, 256, -31, 34,
  121, -24, -174, 126, 71, 21, 58, -258, -78, 67, 46, -136, 52, -41, -30,
  -286, 83, 91, 229, 37, 203, 29, 140, -40, -129, 52, -50, 135, -7, 159,
  -110, -89, -124, 200, 133, 151, -109, 200, -86, 182, -42, -50, 39, -127,
  -110, 16, 50, 46, -181, 134, 68, -67, 190, 2, 53, 264, -18, -22, -99, -45,
  103, 282, 117, -50, 137, 195, -50, 0, -163, 61, 261, -94, 117, -36, -24,
  -59, 122, 96]

theorem fractionalNearFrameSubtreeG3R0043_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0043Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0043Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0043Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0043_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0043LowerBoundTable : List ℤ :=
  [90, 306, 197, -202, 93, 298, 184, 2, 371, 1322, 1303, 351, 271, 789, 15,
  -345, 529, -3, 418, -91, 10, 1598, -252, 302, 118]

def fractionalNearFrameSubtreeG3R0043LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0043Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0043LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
