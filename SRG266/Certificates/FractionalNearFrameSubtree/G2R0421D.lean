import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0421`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0421Mask : ℕ := 5776751034011146

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0421Witness : Array ℤ :=
  #[401, -506, -282, 253, 64, 0, -315, -249, -301, -844, -1241, 817, 1058,
  774, 771, 425, 607, -504, -699, 274, -136, 901, 540, -450, 764, -578, 645,
  608, -475, 528, 95, 425, 607, -600, 77, 53, 542, 697, -370, -579, 240,
  -228, -11, 260, 675, 549, 552, -97, -372, 239, -12, 636, 388, -41, 43,
  373, 249, 33, 158, -490, -452, 124, -344, 0, 671, -204, -127, 355, 426,
  -14, -245, -68, -187, 348, -303, -375, 539, 110, 36, -730, -35, 113, 275,
  -197, -305, -122, -763, -283, 312, 258, -297, 70, 310, -33, 189, 146, 213,
  -113, -90, 233, -384, 346, 350, 253, 627, 245, -4, 378, 464, 997, -319,
  -471, -906, -582, -687, -390, -194, -81, -28, 547, 288, 14, -414, 91,
  -105, 111, -566, 113, -622, 494, -280, 572, 29, -470, 438, 381, 25, 348,
  54, -219, 60, 9, 93, 699, 420, 443, 908, 407, 337, 260, 578, 104, -925,
  -147, 610, -1054, -920, 86, -391, -408, -294, -495, 136, 117, 124, -54,
  -169, 379]

theorem fractionalNearFrameSubtreeG2R0421_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0421Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0421Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0421Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0421_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0421LowerBoundTable : List ℤ :=
  [50, 32, 590, 32, 1211, 1054, 617, 969, 247, 2100, 98, 1977, -320, 1447,
  2206, -804, 101, -47, 100, 110, 198, 99, 2104, 1889, 100]

def fractionalNearFrameSubtreeG2R0421LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0421Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0421LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
