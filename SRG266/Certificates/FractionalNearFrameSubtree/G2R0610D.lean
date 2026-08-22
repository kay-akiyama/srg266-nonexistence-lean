import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0610`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0610Mask : ℕ := 7076070797578864

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0610Witness : Array ℤ :=
  #[318, 138, 642, -625, -376, 345, -769, 435, 302, 450, -858, 389, -704,
  -387, 275, 41, -251, 165, -23, -71, 321, -350, -167, -32, -333, 373, -603,
  -610, -242, 177, 21, -149, -434, -496, -12, 35, 361, -739, -58, -896, 535,
  1114, -301, 94, 0, 133, 402, 418, -438, 78, -131, 316, 30, -390, -507,
  -95, -861, -699, -129, 782, 501, -614, 737, -269, 320, 915, 493, 91, 196,
  235, 53, -1137, -572, 815, -442, -570, -160, 272, 219, -900, 520, 542,
  487, -289, 445, -271, -176, 13, -415, 565, 567, 179, 595, 645, 312, 458,
  232, -679, 874, -4, -905, -476, 749, 334, -2, 34, 543, 39, 966, 0, 198,
  -823, 188, -658, -20, -714, 392, 682, 775, -304, 13, 546, 1083, 212, -240,
  -447, 33, 289, 52, 7, 692, 99, -90, 497, 918, 682, -99, -45, -122, 100,
  66, -12, 513, -392, 120, -395, -118, -1054, 726, -298, -1044, -1093, 340,
  803, -725, 566, 1110, 343, 469, 834, -263, -69, 479, 500, -42, 1, 508,
  175]

theorem fractionalNearFrameSubtreeG2R0610_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0610Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0610Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0610Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0610_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0610LowerBoundTable : List ℤ :=
  [140, 1130, 659, 654, 806, -165, 423, 32, 31, -959, 1042, 1867, 1893,
  1760, 2945, -90, 2085, 923, -500, 141, 998, 13, 2866, 99, 238]

def fractionalNearFrameSubtreeG2R0610LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0610Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0610LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
