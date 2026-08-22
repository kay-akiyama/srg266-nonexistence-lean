import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0034`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0034Mask : ℕ := 522033320214740

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0034Witness : Array ℤ :=
  #[195, 689, -796, -555, -669, -843, 518, 1775, 860, -612, -212, -416, 873,
  -8, -607, -701, 17, -496, -324, -255, 224, 380, -94, -896, 827, 910, 505,
  398, -313, 584, 25, -73, -574, -895, -314, 252, -364, 659, 0, 828, 469,
  435, 576, -390, 0, 134, -532, -92, 605, 795, -992, 76, -211, 0, 122, 644,
  517, 868, 292, -823, -949, -928, -113, -514, 510, 300, 420, 92, -236, 795,
  83, -325, -217, -672, -163, -211, -582, 567, 57, -146, -794, -2, 640,
  -246, 205, 271, -275, 793, -312, -238, -241, -272, -188, 148, 277, 202,
  -61, -156, -716, 479, 68, 103, 379, 612, 1311, -345, 154, -827, -744,
  -747, -114, 54, 585, 1167, 69, 216, 596, -530, 895, 533, -177, 439, 729,
  -226, -1375, -602, -992, 415, -118, 687, 432, 57, -361, 0, 647, 716, -21,
  445, -1654, -1021, 770, 339, -14, 626, 637, -349, 678, 196, 328, 212,
  1109, 874, 127, 270, -663, 796, 770, 442, 1010, -12, -571, 0, -1156, -377,
  -1024, -649, -760, 120]

theorem fractionalNearFrameSubtreeG1R0034_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0034Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0034Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0034Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0034_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0034LowerBoundTable : List ℤ :=
  [-532, 361, 513, 182, 455, -664, 611, -369, 13, 1138, 2210, 1967, 1869,
  2877, 1530, 1427, 823, -899, 1332, 633, 2635, 1896, -721, 100, -1595]

def fractionalNearFrameSubtreeG1R0034LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0034Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0034LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
