import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0545`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0545Mask : ℕ := 6833383389643922

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0545Witness : Array ℤ :=
  #[485, 283, 408, 307, 357, 44, -322, 46, -394, -507, -506, 417, 145, 177,
  270, 184, -304, -178, -39, 269, 60, -242, 600, 227, 92, -76, 41, 81, 136,
  348, 108, -311, -292, 66, 0, 748, 298, 63, 164, 132, 611, -276, 173, -113,
  129, -38, 111, 196, -300, -370, 304, 264, 222, -174, 16, -105, 325, -468,
  119, 0, 21, -61, 372, -103, -54, -55, 69, 250, 241, -239, 216, -135, -289,
  -338, -71, -161, 449, 99, 348, 128, -258, 248, 52, -557, -471, 133, 156,
  580, -424, -132, -364, -90, 389, -280, 1, 135, 84, -250, -65, 62, -283,
  346, 469, 413, 22, -206, 297, 320, 173, 589, 167, 375, 731, 154, 434, 40,
  -5, 114, 535, -277, -107, -326, -465, 0, -241, -353, 536, -37, -355, 144,
  -243, -391, -416, 56, 160, 231, -30, 378, 16, -333, -159, -56, 99, -34,
  59, -172, 263, 629, -63, 342, -369, 254, -243, 618, 323, -288, 807, -247,
  -335, 160, -143, -79, 25, 67, -368, -334, -105, -290]

theorem fractionalNearFrameSubtreeG2R0545_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0545Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0545Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0545Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0545_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0545LowerBoundTable : List ℤ :=
  [131, 3, -148, 536, 2, 2, 953, 934, 740, 815, 893, 821, 1153, 184, 371,
  967, 10, 1160, 1379, -189, 1567, 757, 198, 422, 174]

def fractionalNearFrameSubtreeG2R0545LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0545Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0545LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
