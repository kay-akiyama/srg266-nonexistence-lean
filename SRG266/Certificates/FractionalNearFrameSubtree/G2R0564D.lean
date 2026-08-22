import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0564`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0564Mask : ℕ := 6846346201110026

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0564Witness : Array ℤ :=
  #[-39, 176, 184, 127, 262, 495, -13, -252, -476, -318, -267, 47, 201, 53,
  383, -362, -200, 8, -173, 216, 315, 121, -14, 44, 32, -239, 50, -103,
  -293, 56, -270, -11, 509, 9, 52, 174, 328, -210, 16, -35, 351, -104, -10,
  306, -85, 345, -164, -309, 0, -247, 323, 280, 300, -21, 122, 328, 154,
  174, -115, 305, 136, 34, -243, 112, -589, 146, 390, -260, -38, 99, 77,
  -37, -11, -142, -56, -239, 283, 1, 56, 50, 179, 351, 269, -321, -172,
  -151, 52, 277, -135, -192, -21, 317, 100, 289, -9, -188, 13, 129, -180,
  -234, -176, -300, -160, -31, 258, -234, 112, 191, 257, 498, 110, -56, 199,
  -208, 8, -61, -408, -303, 137, 523, 159, -412, -214, 76, 180, -14, -72,
  283, 82, -125, 281, 258, 69, 307, -594, 113, 483, 204, 395, 344, 509, 357,
  -79, 143, -85, -298, 446, 264, 79, -167, 445, -41, 569, -373, -7, -155,
  -489, -162, 263, 13, 218, 75, 158, -352, 39, -370, -511, -36]

theorem fractionalNearFrameSubtreeG2R0564_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0564Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0564Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0564Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0564_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0564LowerBoundTable : List ℤ :=
  [65, 591, 1, 394, 93, -63, 602, 894, 2, 485, 1345, 1685, -40, 10, 1925,
  843, -87, 2, 276, 371, 861, 290, -301, 36, 597]

def fractionalNearFrameSubtreeG2R0564LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0564Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0564LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
