import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0172`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0172Mask : ℕ := 1380481688867428

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0172Witness : Array ℤ :=
  #[119, 222, 0, 335, 296, -856, 553, -639, -20, -191, -93, 123, 54, -4, 1,
  64, 571, -12, 218, 177, -147, 60, 492, -39, 331, 642, 0, -20, -134, -27,
  -39, -575, 204, -285, 950, 172, -341, 857, -34, 18, 269, -458, -234, -438,
  18, -1056, -187, -221, 895, 313, -27, 327, 111, 724, 64, -48, -425, -526,
  494, -352, 286, -13, -332, 192, -103, -15, -380, 91, -162, 603, -44, 576,
  -199, -566, 692, -497, -469, 770, 1063, 366, 410, -809, -302, 769, 88,
  251, 676, -428, -185, -638, 256, 472, 811, 415, -298, -165, -17, -888,
  103, -53, 505, 511, 249, -427, 121, 450, -64, -47, 844, -367, 314, -280,
  740, -983, 816, 717, 721, 337, 608, 166, 433, 371, 811, -96, -578, -1056,
  -415, 620, 146, 352, -184, 488, 436, 291, 150, 31, 81, 154, -267, -170,
  499, 15, -67, -103, 175, 171, 8, -338, -258, -248, 1090, 279, 346, 543,
  -51, -597, 546, 107, 308, -597, -410, -311, -169, -700, 240, 238, -15,
  214]

theorem fractionalNearFrameSubtreeG2R0172_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0172Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0172Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0172Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0172_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0172LowerBoundTable : List ℤ :=
  [141, 661, -659, 865, 1866, 1668, 31, 1004, 936, 976, 2129, 2576, 1424,
  1218, 1888, -982, 457, 3351, 958, 1987, -2054, 1907, 1953, 1182, 100]

def fractionalNearFrameSubtreeG2R0172LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0172Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0172LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
