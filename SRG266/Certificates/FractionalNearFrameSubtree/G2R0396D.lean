import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0396`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0396Mask : ℕ := 5740365283266978

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0396Witness : Array ℤ :=
  #[-421, 459, 577, 646, -348, 807, -324, -436, -169, -258, 0, 336, 582,
  879, 617, 719, 107, 1194, 486, -166, -490, 900, 425, 549, 301, 408, -122,
  -576, -743, -283, -467, -733, -263, 308, 1010, 24, 828, -97, 628, -349,
  98, 818, 92, 548, 529, 590, -366, -166, 197, -36, 749, -9, 376, -648, 330,
  -963, 215, 69, 294, 0, 115, 720, 540, 296, 179, 168, 546, 615, 424, 589,
  -215, 241, 753, -315, -398, 298, -310, 438, -589, 236, -384, 356, 23,
  -205, 284, 495, -406, 263, 504, 1, 993, -255, -16, 1008, 382, 844, 1038,
  482, 238, 128, -468, 398, 809, 554, -501, 314, -713, 1147, 93, 115, -199,
  -874, 145, 451, 664, -742, 66, -480, -1376, 369, 92, -395, 459, -449, 380,
  748, 1058, 77, -1034, 525, -381, -977, 538, -175, -338, 577, -115, 1062,
  349, 606, -965, -548, 658, -39, 280, 202, 173, -336, 514, 118, 244, 336,
  -292, -737, 464, 74, 677, -630, 332, 25, 943, 90, 432, 320, 444, 226, 243,
  16]

theorem fractionalNearFrameSubtreeG2R0396_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0396Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0396Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0396Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0396_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0396LowerBoundTable : List ℤ :=
  [1436, 923, 2093, 1673, 503, 2811, 1160, 1669, 1658, 2196, 2833, 1414,
  622, 100, 2736, 2084, 3081, -1993, 3232, 2679, 3553, 1176, 2947, 4439,
  4711]

def fractionalNearFrameSubtreeG2R0396LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0396Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0396LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
