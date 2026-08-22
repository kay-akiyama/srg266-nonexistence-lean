import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0013Mask : ℕ := 659482165758473

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0013Witness : Array ℤ :=
  #[-721, 90, 326, -430, 169, -756, -31, -330, -571, -1029, 0, -26, 383,
  633, 69, 512, 499, 696, 583, 0, 457, 261, -160, 57, -240, -653, -928, 3,
  -169, -54, 117, -125, -566, 67, 142, 250, -40, 371, 449, 262, -223, -584,
  207, -418, 457, 88, -487, 402, 205, 69, 331, -9, 507, -418, 758, 166,
  -481, 575, 328, -417, 624, 13, -22, -239, 386, -401, 503, 26, 343, -106,
  -302, -74, -176, 110, 9, -211, 190, -11, 537, 55, 448, 92, -39, 3, -117,
  -3, 433, 28, -447, 6, 113, -373, -22, 406, -207, 194, 38, 436, 212, 319,
  408, 496, 524, -112, 17, 336, 749, -620, -631, -483, 9, -632, -12, 166,
  -182, -69, -207, -74, -312, 637, -357, -398, -280, 120, -1, 127, 375, 168,
  53, -68, -53, 122, -5, 81, 264, 282, -478, 871, 369, 498, 815, 368, -326,
  0, -461, -791, 281, -12, 230, -290, -138, -257, 264, -569, 233, -565,
  -580, -210, 547, -703, -554, -595, -278, -215, -474, -253, 483, -585]

theorem fractionalNearFrameSubtreeG2R0013_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0013Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0013Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0013Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0013_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0013LowerBoundTable : List ℤ :=
  [-653, -763, 32, 685, 32, 605, 31, -63, -383, -2556, 2412, 505, -2617,
  892, 235, 1151, 114, 334, 1942, -850, 1235, -650, 233, 955, 2029]

def fractionalNearFrameSubtreeG2R0013LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0013Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0013LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
