import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0145`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0145Mask : ℕ := 1039476058279064

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0145Witness : Array ℤ :=
  #[391, 1259, 1200, 762, -440, -19, 431, -1092, -1249, -652, -376, 1901,
  -296, 211, -160, 1496, 1883, -363, 687, 59, -1028, 1211, 343, -34, 670,
  -862, 410, -805, -1504, -1742, -1389, -881, 870, 2088, 2285, 1236, -114,
  -621, -760, 937, 1625, 1016, 1181, 458, -518, -641, 1406, -575, -1133,
  -1791, 1244, 636, 1211, -1789, -273, -140, 1184, 147, -84, -75, -1346,
  116, 206, -2097, 2101, 264, -240, 999, -303, 200, 740, -27, 1239, 24,
  -141, 2056, -25, 449, 117, 883, -294, 110, 331, 553, -729, -720, -196,
  1296, 946, -65, 526, 1667, 307, 229, 1408, -1650, 1791, 788, 1525, 472,
  297, 1195, 395, 703, -411, -126, -48, 460, -391, -927, -1498, -508, 401,
  1272, 2957, 291, 1443, 1540, 999, 736, 476, -409, -507, -3123, -458, -694,
  49, 383, 1239, 425, -134, 2026, -1754, -432, 749, 71, -610, 310, 834,
  -762, 216, 729, -1446, -1005, 429, 707, 244, -15, 1390, -726, -1225, -365,
  1782, -954, 74, -294, -617, 224, 408, -1260, -645, 627, 493, -203, 197,
  -289, -1978, 1632]

theorem fractionalNearFrameSubtreeG1R0145_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0145Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0145Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0145Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0145_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0145LowerBoundTable : List ℤ :=
  [1039, 230, 1467, 2794, 3331, 1774, 2919, 31, 1957, 101, 3517, -1012, 100,
  3159, 944, 1816, 100, 6761, 4090, 100, 6266, 1515, 2130, 4844, 2889]

def fractionalNearFrameSubtreeG1R0145LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0145Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0145LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
