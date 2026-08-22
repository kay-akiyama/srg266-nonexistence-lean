import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0271`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0271Mask : ℕ := 5369795968095384

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0271Witness : Array ℤ :=
  #[221, -83, 257, 458, 841, -74, -311, 337, -973, -359, 253, 304, 778, 218,
  -53, -392, -314, 231, -233, 346, 842, 553, -457, 422, 398, -120, 947, 18,
  1697, 793, 260, 875, 71, -1119, -2567, 2019, 1037, -62, -458, -1029, 713,
  424, 394, -163, -1022, 0, 0, 565, 225, 273, -65, 719, 205, -619, -287,
  -319, 555, 1834, 579, 510, 127, 222, -1494, 349, 508, -440, -1004, 112,
  -498, -1548, -872, 589, 861, -265, -347, -859, 563, 252, 469, 375, 210,
  -263, -254, 668, -956, -364, 446, 810, -1451, -823, 310, 344, 270, -797,
  -51, -204, -502, 807, -292, 616, 244, -537, 324, -356, 1166, 806, -579, 0,
  -1043, 1164, -22, -642, -148, -176, 137, -841, 1358, 576, 2157, 1417, 405,
  -386, -1150, -261, -1283, -132, -15, -1398, -630, 241, 893, -94, 208,
  1310, 284, -634, 202, 2065, 1442, -1464, 1020, -243, 554, 420, -31, -982,
  437, 609, 0, 1115, 606, -108, -1784, 622, -1829, 1023, 73, -1003, -678,
  -179, -1123, -59, -24, 452, -407, -103, -1026, -682]

theorem fractionalNearFrameSubtreeG2R0271_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0271Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0271Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0271Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0271_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0271LowerBoundTable : List ℤ :=
  [-466, 32, -392, -12, 931, 381, 32, 424, 2307, -1600, 1084, 2227, 614,
  -80, 2920, 3464, 5647, 1703, 825, -446, -370, -2451, 101, 100, 100]

def fractionalNearFrameSubtreeG2R0271LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0271Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0271LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
