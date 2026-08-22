import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0427`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0427Mask : ℕ := 5784225380475530

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0427Witness : Array ℤ :=
  #[-1033, -566, 225, -2206, -701, -720, -699, -407, 119, -1117, -917, 117,
  3309, 2595, 1419, 373, 645, 690, 214, 620, 1059, -557, 596, 516, 250,
  -208, -877, -1437, -1276, -737, -986, 99, -713, -468, 243, 223, 386, -189,
  290, 717, 1082, 831, 24, -47, -84, 401, -946, -993, 1111, 1336, 1315,
  1048, -584, -750, -737, -1308, -1636, 696, 639, 97, 0, 314, 260, 2277,
  796, -160, -74, 192, 103, 96, 706, -2, 347, -45, 880, 549, -322, 341, 48,
  -355, 482, 979, 28, -618, 134, 485, 360, 518, -316, -544, 936, 115, 163,
  538, -77, 1638, 376, 141, -103, 315, 174, 155, 399, -389, -191, 519, -387,
  307, 457, 311, 925, -951, -14, 1149, 716, 276, 348, 408, -136, 540, -1187,
  -97, 423, 1264, -165, 734, -1440, 92, -666, 815, 226, 174, -1008, 73, -15,
  -1019, 811, -1022, -569, -1199, 1472, 815, 56, 791, 276, -1023, 26, 696,
  -864, 716, 511, 702, 956, -320, 729, -788, 958, 0, 625, -28, 1479, 199,
  133, 1267, 250, 1023, -912, 602]

theorem fractionalNearFrameSubtreeG2R0427_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0427Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0427Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0427Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0427_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0427LowerBoundTable : List ℤ :=
  [747, 2652, 2773, 642, 2691, 896, 32, 31, 3339, 101, 1895, 101, 4890,
  5210, 907, -7, 4787, 2844, 1533, -1351, 2022, 347, 99, 2440, 4547]

def fractionalNearFrameSubtreeG2R0427LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0427Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0427LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
