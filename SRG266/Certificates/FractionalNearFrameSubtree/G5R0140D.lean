import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0140`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0140Mask : ℕ := 6847513977624849

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0140Witness : Array ℤ :=
  #[-274, -470, 277, 227, 230, -253, -1032, -534, 437, 96, 238, 421, 1115,
  300, 498, 373, -91, 471, -405, -15, -299, 497, 401, -47, 791, -427, -68,
  229, -605, -82, 54, 450, 241, -301, -568, 313, 316, -87, 97, 88, 93, 84,
  574, 754, -92, -227, 370, 324, -180, -386, -590, -849, 1327, -462, 259,
  22, -835, -893, 668, -550, 689, 126, -383, -796, 424, 231, 332, 1116, 498,
  -206, -244, 534, -970, -624, 331, 619, -824, -146, 36, 37, -312, 348, 166,
  358, 420, -34, 22, -830, -545, -167, -23, 575, 149, -277, 317, 103, 233,
  -209, -420, 277, -159, 280, 486, 681, 479, 795, 797, 635, -351, -145,
  -286, -593, 806, 513, -18, 663, 833, 89, 759, -432, 26, -13, 749, 268,
  -834, -508, 1341, -798, 672, -483, -371, 537, -471, -79, 250, -500, 95,
  470, -682, -57, -559, -628, -232, 230, -362, 403, -1, -1307, 830, 147,
  -128, -439, -515, -204, 254, -453, 161, 316, 261, -596, 193, -42, -491,
  -263, -11, 171, 525, -502]

theorem fractionalNearFrameSubtreeG5R0140_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0140Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0140Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0140Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0140_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0140LowerBoundTable : List ℤ :=
  [-39, -562, 478, -258, 1472, -835, 1096, -382, -486, 401, 2675, 592, -456,
  1545, 2764, -385, 100, -356, 2742, 632, 2068, 1983, 1840, 992, -591]

def fractionalNearFrameSubtreeG5R0140LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0140Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0140LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
