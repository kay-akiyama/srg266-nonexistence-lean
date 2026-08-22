import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0097`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0097Mask : ℕ := 1244199147254793

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0097Witness : Array ℤ :=
  #[205, 0, 236, 64, -668, -1, 0, 3, -681, -669, 472, 301, 869, 223, 59,
  -551, 0, -243, -324, 443, -23, -1053, -51, 616, 1306, 197, 344, -587, 111,
  411, -150, -212, -350, -312, -552, -16, 620, 300, 398, 0, 552, -229, -238,
  -728, 446, -69, 165, -184, 1202, 763, 450, 252, -314, -707, 182, 730,
  -595, 156, 190, 202, 493, -158, 578, -1096, -154, 275, 218, 0, -271, -266,
  440, 37, -392, -148, -251, 313, 63, 532, 376, -463, -85, -70, 173, -168,
  276, -95, -2, 448, -333, -1558, 1553, 965, 620, 1067, 378, 396, -277,
  -764, 85, -170, -63, -504, 150, 276, -198, 348, 592, -681, -438, 59, 521,
  -609, -1215, -811, -688, 713, 188, 91, 1184, -1039, -122, -650, 105, -547,
  233, -157, -803, 1218, -299, 407, -78, 1116, 115, -223, 1040, -308, 353,
  172, 886, 478, -212, 659, 162, 312, 80, 482, 618, 202, -810, -344, 294,
  -254, 290, 147, -476, -497, -11, -684, -376, -461, -978, 223, 367, 543,
  320, -186, 386, 664]

theorem fractionalNearFrameSubtreeG2R0097_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0097Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0097Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0097Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0097_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0097LowerBoundTable : List ℤ :=
  [-146, 653, 660, 57, 33, 1362, -148, 916, 696, 1281, -341, 21, -859, 2685,
  1903, 2326, -1735, -1221, 2224, 100, 2292, -1514, 994, 101, 2447]

def fractionalNearFrameSubtreeG2R0097LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0097Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0097LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
