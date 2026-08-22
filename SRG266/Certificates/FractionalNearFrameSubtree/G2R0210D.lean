import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0210`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0210Mask : ℕ := 2361440280224771

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0210Witness : Array ℤ :=
  #[0, -217, 4, 1149, -1029, 0, -322, 66, 655, 482, -709, -298, 0, -431,
  978, -139, 369, 1813, 56, -3, 224, 1088, 250, 1087, -238, 504, 0, 138, 58,
  -430, -1107, 203, -538, -962, 563, 75, -587, -361, 1532, 1376, 743, 240,
  -345, 245, -315, -258, 683, 657, 910, 799, -299, -589, -659, -564, -102,
  -327, -733, -467, -201, 840, -260, -223, 409, -61, 296, 46, 98, -13, 648,
  139, -146, 7, 297, 255, 673, 679, 234, -174, 546, 29, 25, -231, 142, -677,
  113, -94, -299, -476, -618, -435, -565, -79, 103, 94, 193, -164, 724, 941,
  742, -756, 343, 155, -193, 59, -740, -205, -128, 169, 528, 491, 95, -30,
  -86, 0, 358, 638, 317, 226, 664, -92, 605, 309, 70, 986, -397, -494, 126,
  -197, 318, -474, -183, 716, 746, -449, 472, -1293, -613, 666, 196, 276,
  346, -129, -221, -394, 304, 318, 51, 108, 1098, 127, 808, -233, 94, -414,
  613, 230, -956, -198, 42, -163, 423, -57, -233, -569, -585, 56, -158,
  -882]

theorem fractionalNearFrameSubtreeG2R0210_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0210Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0210Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0210Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0210_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0210LowerBoundTable : List ℤ :=
  [361, 31, 519, 225, 2218, 839, 887, 1075, 32, 2795, 527, 1773, 2083, 101,
  99, -1415, 101, -159, 1566, 112, 2107, 3218, 421, 3583, 383]

def fractionalNearFrameSubtreeG2R0210LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0210Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0210LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
