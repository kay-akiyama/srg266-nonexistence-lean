import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0572`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0572Mask : ℕ := 6847325316789772

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0572Witness : Array ℤ :=
  #[253, 52, 72, -8, -143, -358, 392, 218, 330, 813, 908, -561, -589, -20,
  -302, 320, 319, 44, 0, 896, 371, 174, 512, -483, 90, -497, -53, -450,
  -256, -235, -38, 206, -71, -230, 413, 869, -461, -355, -65, 0, -166, 437,
  59, -89, 148, 189, 301, -381, -534, -340, 80, 237, 190, 0, -456, 113, 173,
  327, 175, 4, 370, 346, 419, -773, 158, -111, -283, 174, -127, 447, 683,
  250, 514, -71, 640, -236, 149, 0, -11, -147, 569, 116, 633, -165, -683,
  -54, 507, 408, 400, -259, 62, -486, -258, 378, -334, 492, -285, 154, -145,
  -410, 235, -126, -29, 400, 250, 101, 352, 193, -176, -511, 215, 41, 382,
  -16, 82, 198, -285, 205, -110, -101, 94, -269, -27, -145, 1, -447, -16,
  276, 56, -305, -233, -121, -463, 528, 353, 404, 116, 296, -456, -529, 240,
  -298, -68, 863, 60, 37, -67, -874, 154, -265, -666, 568, -312, 496, 545,
  239, 117, 778, -114, 252, -41, -57, 123, 129, 592, -538, -228, -93]

theorem fractionalNearFrameSubtreeG2R0572_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0572Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0572Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0572Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0572_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0572LowerBoundTable : List ℤ :=
  [201, 824, 556, 1223, 144, 31, 901, 31, 714, -1008, 2072, 631, -222, 100,
  100, 1134, 99, 1817, -370, 315, 1783, 2186, 1041, 878, 806]

def fractionalNearFrameSubtreeG2R0572LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0572Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0572LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
