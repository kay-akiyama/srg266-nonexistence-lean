import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0124`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0124Mask : ℕ := 1345573166678598

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0124Witness : Array ℤ :=
  #[-830, -457, -83, -1133, -1788, -914, 521, -430, 253, -518, -347, 532,
  611, 1206, 632, 1421, 547, -699, -958, -1691, -1303, 711, 107, 936, 623,
  41, -9, -184, -155, 0, 1530, -196, 319, 880, -79, -775, -210, 717, 605,
  -1313, -1068, 238, 269, 0, -861, -1174, 94, -552, -197, -1289, -814, -815,
  1702, 545, 213, -716, -966, -1245, 2108, -484, -138, 946, -968, 751, -276,
  -312, -1286, 523, -196, -273, 744, -1272, 429, 257, -942, -517, 680, -904,
  15, -606, 520, 626, -223, -237, 643, -281, -932, 918, 311, -500, 36, 321,
  317, 1068, 839, 60, 833, 789, -456, -273, 831, 378, -267, -170, 35, -367,
  387, 1526, 143, -243, 950, 643, 559, -71, 802, -159, -1654, -1596, -155,
  180, 21, 371, 415, 376, -1387, 159, -418, -667, -641, 952, -110, -123,
  -1180, -486, 813, 408, 337, 201, -306, -218, 71, -735, 695, -31, -685,
  431, 906, -965, -34, -259, 383, 830, 511, 650, 241, -37, 749, -83, 574,
  -52, -190, -1304, -420, 680, 1069, -477, -715, 1172]

theorem fractionalNearFrameSubtreeG2R0124_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0124Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0124Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0124Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0124_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0124LowerBoundTable : List ℤ :=
  [-1442, 31, -495, 1333, -679, -2143, 31, 114, 544, -33, 839, 3502, 1064,
  2004, 99, -221, -1435, 847, -400, 3412, 100, -1799, 99, -2184, -3082]

def fractionalNearFrameSubtreeG2R0124LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0124Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0124LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
