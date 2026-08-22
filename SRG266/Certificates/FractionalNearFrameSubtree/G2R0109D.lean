import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0109`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0109Mask : ℕ := 1288470477116419

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0109Witness : Array ℤ :=
  #[-350, -2, 877, -275, 0, -81, -172, -345, -136, 0, 12, -33, -329, -108,
  -96, 521, 456, 95, -444, 225, 427, 106, 111, 144, 396, 351, 611, 501, 551,
  -216, -328, 0, -121, -221, -528, -404, 726, -692, -261, 461, 371, 182,
  -349, -401, -322, -78, 45, 137, -352, -184, 196, -86, -104, 490, 429, 519,
  177, -373, 437, -229, -13, -95, -30, 416, 289, -858, 762, -265, 373, -258,
  -437, -330, -356, 553, 512, -199, -367, 108, 36, 18, 552, -85, 40, 471,
  -903, 1010, -505, 266, 1, -9, 23, 526, 52, 241, -997, 931, -143, 195, 217,
  48, 15, 412, -144, 223, -1104, 975, -400, -11, -181, -101, 202, -531, 290,
  132, -162, 407, 335, 323, 194, 39, 327, -64, 721, -436, 78, 92, 151, 120,
  617, -238, 230, 262, 193, 173, 117, 305, 356, 45, -319, -261, 97, 0, 165,
  -110, 115, -131, -67, 43, 191, 361, 190, -407, 27, -91, 335, -5, 334, 315,
  -85, 319, 257, 0, -269, -53, -155, 174, 42, -331]

theorem fractionalNearFrameSubtreeG2R0109_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0109Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0109Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0109Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0109_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0109LowerBoundTable : List ℤ :=
  [679, 917, 33, 2422, -807, 32, 1635, -57, 1365, 1579, 101, 2072, -404,
  -2302, 1708, -263, 2391, -95, 384, 68, 1114, 1336, 1197, 100, 24]

def fractionalNearFrameSubtreeG2R0109LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0109Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0109LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
