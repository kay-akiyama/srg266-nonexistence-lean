import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0170`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0170Mask : ℕ := 1380467336397156

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0170Witness : Array ℤ :=
  #[584, -91, -301, -636, 843, -1113, -951, -627, 0, -205, -349, -245, 417,
  1517, 770, 1347, 1074, -136, -586, -781, -1593, 15, -53, 54, 522, 68, 14,
  608, 430, 216, -1384, 108, 86, 2208, 781, -154, 863, -1705, -61, -203,
  576, -1508, 1061, -572, -154, -58, 1894, 186, 1425, -984, -438, 148, 209,
  640, -640, 1045, -1014, -314, -386, -986, -1105, -125, 46, -644, 0, 361,
  491, 747, -609, -397, 809, 148, 657, 620, 795, -427, -410, -583, 647, 199,
  591, -488, 439, -403, -31, 113, 131, 214, -414, 504, 46, 32, 1280, 607,
  256, 288, -156, -802, -960, -1776, -1236, -910, -466, 88, -520, -1048,
  -836, 204, 938, 392, 416, -208, -55, -435, -281, 323, 100, -283, -941,
  -517, 557, 1308, 202, -688, 1203, 266, -35, 384, -399, -355, -265, 145,
  -226, -319, -945, 1190, -532, 628, -729, -1384, 1545, -504, 388, 25, 15,
  -930, -10, -850, -603, -390, 327, 475, -959, 912, 798, -420, -101, 17,
  715, -313, 994, 280, 338, 821, 75, -387, 213, -178]

theorem fractionalNearFrameSubtreeG2R0170_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0170Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0170Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0170Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0170_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0170LowerBoundTable : List ℤ :=
  [-1039, 290, 32, -1723, 32, 32, -460, 180, 33, -780, -2042, 3918, 695,
  1233, 1913, -2453, 1308, 100, -3736, 1775, 256, 1253, 1005, 3473, 101]

def fractionalNearFrameSubtreeG2R0170LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0170Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0170LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
