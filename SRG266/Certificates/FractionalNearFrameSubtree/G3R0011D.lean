import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0011Mask : ℕ := 745180736948739

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0011Witness : Array ℤ :=
  #[1149, 1304, 0, 699, 60, -100, 972, -58, 1066, 1153, 239, -215, -661,
  -616, -1955, -461, -1660, -1630, 1009, -1007, -1049, -960, -1330, -617,
  1098, -971, 0, -1052, -629, 1024, 789, 940, 1237, 1628, 359, 380, 196,
  169, -851, -321, -292, -250, -476, -417, -260, -377, -353, -273, -208,
  227, 221, 82, -60, 83, -43, 46, 28, -241, -192, -11, 128, -23, -62, 39,
  187, 55, -233, -884, -439, -88, 63, 257, -118, 36, 132, 42, 196, -627,
  984, -43, 171, 392, -194, 191, 332, 340, 229, 476, -568, 46, 30, 343, 171,
  175, 192, 88, 213, -271, 100, -242, 198, -470, -29, 225, 149, 253, 267,
  246, 291, 241, 709, -564, -429, -708, -432, -560, -454, -153, 341, -92,
  77, 177, -76, -762, -80, 478, -121, -180, -152, -475, 140, 764, -299,
  -123, 365, -290, -231, -534, 328, 133, 157, -19, -303, -925, 36, 1, -133,
  -46, -329, 200, 96, 192, 424, 556, 289, -186, 140, 566, -1004, -147, 266,
  907, 403, 10, -838, 688, 396, 679]

theorem fractionalNearFrameSubtreeG3R0011_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0011Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0011Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0011Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0011_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0011LowerBoundTable : List ℤ :=
  [-512, 32, 386, 30, 33, 31, -290, 32, 349, 1215, -116, -603, -2403, 1301,
  809, 369, -1966, -289, 100, 163, -2006, 101, -1492, 1718, 1246]

def fractionalNearFrameSubtreeG3R0011LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0011Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0011LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
