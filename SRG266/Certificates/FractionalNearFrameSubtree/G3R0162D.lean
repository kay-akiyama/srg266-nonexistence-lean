import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0162`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0162Mask : ℕ := 6850842413144880

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0162Witness : Array ℤ :=
  #[64, -146, -141, -85, 109, -236, -123, -306, -5, 311, -163, -1, 130, 78,
  27, -102, 70, -16, 177, -122, 11, 53, 381, 353, -209, -156, -49, 29, 274,
  0, 97, 380, 181, -230, -483, -220, 102, 83, 153, 132, -127, -247, -211,
  -252, -101, -174, -336, -352, 321, 518, -142, -183, -167, 479, 274, -120,
  273, 215, 147, -13, 131, -61, 90, -344, -205, -46, -86, 328, 515, -56,
  -53, 49, 321, 136, -350, 10, -65, 117, 149, 205, 104, -24, 78, -73, -94,
  197, 147, 106, 81, -16, 222, -84, 95, 132, -23, 63, 245, 0, 158, -100,
  219, 269, -81, -210, -43, -420, -320, 9, -75, 280, -158, 120, -56, 18,
  -374, -198, -178, -363, 234, -85, -18, -1, -323, -186, 85, -69, 6, -408,
  0, -58, -49, -23, 22, -340, -167, 43, -158, 88, -204, 76, -38, -232, 74,
  346, 68, -114, 119, -69, 150, 341, 36, -72, 0, 57, 107, -139, 63, -180,
  178, 154, -61, 316, 27, 82, 301, 216, -258, 130]

theorem fractionalNearFrameSubtreeG3R0162_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0162Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0162Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0162Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0162_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0162LowerBoundTable : List ℤ :=
  [-229, -212, 267, 2, 1, 218, -474, 607, -344, 368, -1203, -24, -33, 241,
  20, 444, 9, 657, 54, 873, -269, 847, -151, -667, 1670]

def fractionalNearFrameSubtreeG3R0162LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0162Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0162LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
