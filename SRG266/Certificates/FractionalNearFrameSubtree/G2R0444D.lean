import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0444`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0444Mask : ℕ := 5789870011422218

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0444Witness : Array ℤ :=
  #[-1018, 691, -631, -2, 902, -932, 1472, 1136, 1228, 5, 2455, -9, -637,
  1082, -960, -781, 328, 515, 554, 661, -337, -391, 327, 189, -1357, 549,
  183, 933, 1430, 587, 365, 855, 839, -1352, 1012, 743, 34, -977, 8, 1583,
  132, 1619, 943, 174, 526, -837, 591, -439, 854, 283, -102, -770, -702,
  517, 423, 1084, -1017, 1441, -427, 665, 784, 787, -710, -366, -609, -1146,
  31, 401, 157, -793, -225, -720, 292, 1304, 205, 394, -1232, -203, 753,
  790, -1223, 525, 817, 954, -239, -281, 604, -289, 215, -2827, 1216, -961,
  -600, -281, -64, 1597, 688, 1004, 1401, 183, 680, 437, 1963, 58, 331,
  -685, 694, -2110, -2045, -823, 1901, 184, 1183, 418, 506, 313, -241, -232,
  1523, -1575, -725, -440, 295, 17, 134, 545, -570, 783, -1384, -682, -68,
  -49, -616, -1401, -1124, -1485, -291, 1476, -900, -2047, 1069, 211, -1839,
  770, 211, 801, -940, 1548, 135, 247, -1948, -858, 258, -837, 871, -1190,
  -685, -510, 1096, -601, 1582, -2137, -171, 1628, -263, 523, -2224, -524]

theorem fractionalNearFrameSubtreeG2R0444_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0444Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0444Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0444Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0444_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0444LowerBoundTable : List ℤ :=
  [-207, -3519, 909, 32, 32, 3815, 4250, 31, 32, 2858, 338, -4065, -1497,
  3310, 1037, 100, 3247, -436, 2234, -903, -1923, 1882, 1832, 101, 4549]

def fractionalNearFrameSubtreeG2R0444LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0444Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0444LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
