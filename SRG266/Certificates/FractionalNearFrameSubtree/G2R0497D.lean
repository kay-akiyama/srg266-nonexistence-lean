import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0497`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0497Mask : ℕ := 5811361958450328

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0497Witness : Array ℤ :=
  #[1069, 277, -21, 51, -386, 393, 191, 541, -491, -343, 642, 318, -289,
  -203, 612, 138, 519, 26, 62, -315, 361, -13, -372, -739, 84, -204, -116,
  -203, 1242, 807, 36, 56, -17, -314, -628, 516, -334, -138, -568, -563,
  244, -70, -202, 267, -159, 477, 449, 513, 141, -879, 451, 9, 753, 179,
  566, -151, -517, -102, -502, 439, -385, 502, -123, 138, 274, 46, -133,
  791, 552, -533, 88, 518, -269, 296, -64, -49, 281, 11, -110, 434, -35,
  601, 243, -1216, 245, 441, -739, 153, 256, 143, -781, -1145, 520, 305,
  -308, 28, -63, -145, -244, 141, 530, -454, -72, -100, 384, -121, 194, 566,
  817, 724, 636, 256, 270, 507, 285, 978, -472, -887, 347, 431, -352, -119,
  206, 160, 79, -264, 293, -434, 112, 564, 326, 669, -160, 2, -114, 512,
  -102, 92, 310, 431, -99, 32, -400, 286, 510, -1, 650, -108, -125, 87, 613,
  56, 146, -223, -245, 707, 521, 448, 0, -171, -282, -513, -248, -585, -21,
  264, 406, 529]

theorem fractionalNearFrameSubtreeG2R0497_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0497Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0497Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0497Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0497_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0497LowerBoundTable : List ℤ :=
  [441, 1467, 842, 1002, 33, 640, 143, 1693, 1752, 2085, 2718, 1821, 1112,
  1559, -136, 1498, 2750, -315, 998, 1136, 863, -120, 99, 328, 2687]

def fractionalNearFrameSubtreeG2R0497LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0497Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0497LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
