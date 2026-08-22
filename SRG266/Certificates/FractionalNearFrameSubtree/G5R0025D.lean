import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0025Mask : ℕ := 1109736349992018

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0025Witness : Array ℤ :=
  #[336, 641, 250, -15, 9, 401, -205, 37, -600, -614, -1002, 247, 110, -360,
  266, -451, 208, -20, 459, -124, 250, 85, 240, 33, 419, 215, -582, -293,
  -224, -490, -114, 197, -162, -145, 222, 1043, 1359, -1166, 1074, 1907,
  1101, -1790, -1593, -866, -1835, -175, -250, -265, 23, -407, -452, 338,
  657, 905, -20, -489, 928, 629, 698, 116, 473, -80, -895, -1007, -59, -122,
  213, 708, -188, 329, 54, -102, -912, -302, -112, -39, -391, -345, 87, 262,
  270, -36, 492, -103, 459, 149, -7, 143, 697, -659, 632, 508, 204, -596,
  190, 65, -922, -115, 128, 369, 291, 542, 212, 547, 532, -442, 268, 369,
  99, -362, -96, 0, -574, 228, 61, -585, -166, -322, -195, 942, 262, -613,
  841, 504, -719, -330, -218, 167, 527, 56, 956, -136, 155, 305, -246, -93,
  170, -456, 9, -366, 323, -564, 645, 20, 0, 168, 506, 444, 499, -223, 712,
  403, 592, -93, 442, 368, 798, -274, 617, -1073, 77, -142, 268, 567, 96,
  458, 187, 469]

theorem fractionalNearFrameSubtreeG5R0025_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0025Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0025Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0025Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0025_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0025LowerBoundTable : List ℤ :=
  [-123, 1338, 32, 31, 500, 730, 269, 888, 244, 2206, 99, 1407, 2524, 1760,
  2067, -1071, -986, 1230, 377, 694, 153, 1532, 1536, 2608, 335]

def fractionalNearFrameSubtreeG5R0025LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0025Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0025LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
