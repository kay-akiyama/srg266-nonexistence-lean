import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0011`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0011Mask : ℕ := 268054951841937

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0011Witness : Array ℤ :=
  #[302, -205, 218, -1468, 451, -789, 880, -232, -36, 0, 96, 4, 1330, -589,
  0, 444, -1356, -1002, -215, 398, -233, -2072, 154, 771, 1006, -183, -672,
  -190, 1162, 589, 1119, -560, -68, 120, 699, 434, 1237, 339, 43, -177,
  -572, -366, -1498, 836, 371, 859, 359, 0, -311, 1647, 1383, -1286, -1041,
  -15, -204, 798, 76, -51, -195, 182, 350, -160, -533, 97, 99, -437, 1413,
  734, 957, -309, 618, 795, 137, -158, 337, -918, -1144, -138, 451, -604,
  581, 1483, 749, 1064, 988, -170, 1232, -75, 246, 715, 51, 1070, 341, 416,
  610, 944, -2157, -894, -529, -384, -124, 63, 395, -151, 374, 361, 2037,
  -341, 172, -999, -1694, 59, 468, 712, -1897, 923, 2552, 721, 539, 336,
  -234, -566, -1572, 1207, -647, 529, 305, 300, -34, 347, 1127, -719, 350,
  -635, 1347, -62, 466, -533, -571, 0, -80, -1166, 592, 236, -664, -88, 704,
  609, 371, -1916, 607, 211, -179, 487, -1890, 536, -732, -553, 119, -133,
  401, 1119, 128, 277, 239, -266, 2339, -1215]

theorem fractionalNearFrameSubtreeG2R0011_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0011Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0011Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0011Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0011_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0011LowerBoundTable : List ℤ :=
  [-225, -32, 2219, 291, -185, 769, 466, 464, 3408, 582, 1113, 2871, 101,
  4794, 250, 3159, 99, 2306, 2105, 3710, 6987, -1494, 2783, 1593, -3140]

def fractionalNearFrameSubtreeG2R0011LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0011Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0011LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
