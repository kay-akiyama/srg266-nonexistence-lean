import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0371`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0371Mask : ℕ := 5716139060711832

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0371Witness : Array ℤ :=
  #[-247, 128, -299, -19, 463, 139, -249, 29, 419, -308, 1057, -58, -120,
  -112, 122, 294, -437, 331, -42, 976, 274, 92, 510, 495, 198, 136, 0, -519,
  -485, 424, 580, -113, 423, 190, -262, -687, 231, -640, 51, 46, 812, -21,
  223, 1035, -13, 719, -742, -3, -103, 550, -84, 53, -659, -472, -1298,
  -340, -360, 439, 58, -34, 338, 332, 293, -17, -187, 1116, -144, 596, 850,
  -316, -613, -177, -451, -911, 606, -770, 148, -82, -136, -204, 363, 295,
  245, 177, 87, 316, -340, -232, -45, 132, 148, -107, -243, -307, 402, 458,
  -514, 119, 199, -219, -355, -384, 515, 146, -61, 211, 26, -502, -415,
  -387, -1033, 306, 526, -203, -135, -159, -119, 37, -302, 7, -153, 159,
  -168, -368, 45, 496, 147, 1281, 620, 314, -223, 158, 191, 448, 714, 297,
  -151, 179, 88, 109, -290, 48, -151, 414, -43, 181, 649, 305, 665, 522,
  753, 330, 663, -639, 149, 763, 291, 478, -510, -161, 68, -536, 162, -289,
  711, -149, 147, -216]

theorem fractionalNearFrameSubtreeG2R0371_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0371Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0371Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0371Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0371_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0371LowerBoundTable : List ℤ :=
  [181, 1465, 252, 807, 979, 2085, 0, -338, -62, 1994, 2237, 99, 691, 660,
  2016, -639, -625, 777, 1907, -1660, 1217, 1949, 964, 3457, 1975]

def fractionalNearFrameSubtreeG2R0371LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0371Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0371LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
