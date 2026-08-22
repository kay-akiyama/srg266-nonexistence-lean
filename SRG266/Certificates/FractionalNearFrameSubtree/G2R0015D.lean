import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0015Mask : ℕ := 676919867197961

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0015Witness : Array ℤ :=
  #[-1387, -882, -44, -546, 203, -499, -594, -591, -1192, -1562, 144, 0,
  1233, 479, 1268, 1125, 616, 796, 306, -335, -180, -211, -124, 527, -305,
  17, -897, -592, 68, 671, 757, 98, -1564, -778, -467, -126, -151, 1096,
  1215, 1224, -231, -714, -336, 84, 980, -64, -588, 296, 189, 228, 127, 97,
  371, 432, -134, 0, -660, 660, -309, 270, 168, -124, 99, 260, -120, 114,
  745, 158, -11, 672, 284, 746, -261, -172, -58, -4, -215, 276, 83, 408,
  -320, 461, -498, -1271, 447, -401, 938, -390, 58, -431, 183, -92, 267,
  381, 199, 918, 143, 505, 145, 320, 421, 18, 167, 7, -257, -128, 428, -853,
  -421, 475, 69, -473, -23, -209, -276, -134, -281, -588, -362, -326, 274,
  -36, 261, -408, 378, 183, -212, 310, 171, -373, -418, -746, 238, 825,
  -455, 124, 362, -104, -138, 466, 197, 130, 570, -288, 277, -340, -194,
  343, -33, 70, 417, 231, 663, 755, -176, 395, 415, -313, -531, 571, -550,
  -197, -486, -335, -1040, -507, -373, -401]

theorem fractionalNearFrameSubtreeG2R0015_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0015Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0015Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0015Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0015_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0015LowerBoundTable : List ℤ :=
  [-815, -876, -198, 935, 655, 397, -1623, 32, 118, -248, 2322, 100, -1359,
  391, 2465, 693, -149, 1628, 99, 891, 459, 100, 2350, 100, 895]

def fractionalNearFrameSubtreeG2R0015LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0015Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0015LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
