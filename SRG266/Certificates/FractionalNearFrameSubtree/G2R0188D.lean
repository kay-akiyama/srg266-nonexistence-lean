import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0188`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0188Mask : ℕ := 1393404032828504

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0188Witness : Array ℤ :=
  #[-275, -481, -288, 304, -358, -398, -32, -262, 0, 517, -48, -51, 668,
  -248, -15, -786, -236, -476, -501, 399, 461, 367, 103, 106, -743, -172,
  160, 193, -617, -165, 291, -610, 1042, -1416, 577, 62, 364, -443, -504,
  -392, 366, -651, -1120, -647, -227, -513, 719, -247, -107, -112, 1003,
  911, 336, -322, -751, -642, -190, 565, -144, -310, -1, 15, -464, -127,
  267, 522, -260, 616, 645, 1227, 72, 579, -835, 368, -112, 308, 642, -484,
  -175, 26, 649, -12, 564, -311, -1094, -173, 1310, 1063, -311, -230, 286,
  40, -513, 66, 120, -1169, -261, 152, -144, 846, -471, 101, -470, 227,
  -458, 906, -565, -470, -1056, -1616, 787, 1315, 417, 150, 41, -196, 26,
  1235, 198, -356, -471, -780, 293, 786, -822, -68, 422, 16, 392, 334, -233,
  -194, 445, 529, 450, 388, 347, 0, -295, 459, -439, -109, -1038, -728,
  -704, 518, 730, -491, -495, 776, -543, -450, 105, -461, 287, 532, 923,
  -175, 193, -23, -282, -302, 168, 37, 201, 697, 524, 319]

theorem fractionalNearFrameSubtreeG2R0188_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0188Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0188Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0188Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0188_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0188LowerBoundTable : List ℤ :=
  [-876, 531, 286, 32, 1081, -1155, 192, -772, -910, 1030, 101, 653, -2476,
  2426, 2482, 680, -2810, 2833, 375, 873, 1536, 100, 100, -469, -2409]

def fractionalNearFrameSubtreeG2R0188LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0188Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0188LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
