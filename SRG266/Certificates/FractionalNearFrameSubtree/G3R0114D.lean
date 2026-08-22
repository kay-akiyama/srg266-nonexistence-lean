import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0114`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0114Mask : ℕ := 5387182189092372

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0114Witness : Array ℤ :=
  #[228, 248, 66, 163, 97, -56, 66, 2, -280, 57, 49, -69, -215, -145, -19,
  -270, 18, -155, -295, -77, -224, 81, 31, 64, 203, 31, 172, 74, -108, 35,
  92, 132, 65, -35, -40, -34, 69, 8, 103, -257, -26, 28, -125, -15, -53,
  110, 103, 228, -160, 25, -120, 99, 134, -139, -42, 23, 103, 75, -16, 5,
  -100, 54, -87, 16, 182, -67, -57, 35, 106, -158, -35, 70, 39, 278, -152,
  237, 145, -143, -272, 169, -149, 117, 130, 357, -94, -29, 43, -141, -90,
  177, 142, 53, 90, -59, 293, 93, -287, 76, 160, 51, 4, -155, -40, 171, 14,
  -155, -24, -189, 8, -39, 293, -5, 257, 123, 51, 58, -38, 191, -77, -40,
  271, 421, -36, 129, 6, -218, 285, 0, -23, -10, 188, 134, 176, -113, 151,
  31, -66, 106, 140, -108, -102, 251, 37, 248, -20, 36, 207, 89, 210, -110,
  109, 146, -40, 120, -184, -105, -292, 232, 82, 185, 57, 292, 51, -40, 35,
  18, 0, 180]

theorem fractionalNearFrameSubtreeG3R0114_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0114Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0114Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0114Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0114_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0114LowerBoundTable : List ℤ :=
  [205, 745, 453, 1, 382, 380, 0, 503, 1, 1310, 424, 623, 308, 441, 222,
  751, 722, 211, 252, 105, -48, 306, 303, 643, 243]

def fractionalNearFrameSubtreeG3R0114LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0114Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0114LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
