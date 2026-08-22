import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0141`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0141Mask : ℕ := 1361656587601034

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0141Witness : Array ℤ :=
  #[324, 826, -338, 168, -134, -75, 693, -412, 0, -208, 364, 722, -43, -319,
  -369, 482, 546, 148, -257, 474, -593, -242, 165, -236, -478, -539, -7,
  676, 559, -233, 16, 69, -122, 409, 798, -203, -192, 204, 366, -27, -585,
  -741, -290, 297, -45, -27, 131, 225, 204, 156, -164, 438, -288, 253, -61,
  444, -167, 418, 214, 44, 422, -74, 352, -24, -88, 679, -34, 588, -383,
  -262, 410, 532, 302, -430, -62, -354, -716, -326, -375, -164, 151, -377,
  350, -482, 55, 266, -97, 126, 404, 792, -311, -244, 226, -894, 494, 767,
  -343, 306, 388, 756, -84, 328, 278, 252, -251, 118, 101, 95, 188, -392,
  185, 426, 468, 391, 637, 290, -52, 236, -103, -422, 1, 250, 407, -53, -3,
  -221, 90, 508, 319, -62, -46, -360, 525, -689, -45, -234, -49, -525, 260,
  -175, 280, -44, 258, 325, 764, 16, -196, -118, 394, 187, -270, -590, 359,
  -107, -98, 161, 835, 693, 244, -448, 65, -452, -72, -148, -128, -329, 759,
  554]

theorem fractionalNearFrameSubtreeG2R0141_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0141Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0141Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0141Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0141_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0141LowerBoundTable : List ℤ :=
  [433, 635, 941, 122, -15, 774, 1548, 980, 130, 1205, 1337, 302, 683, 3014,
  2431, 454, -175, 1961, 648, 591, 100, 840, 1861, 2439, 1959]

def fractionalNearFrameSubtreeG2R0141LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0141Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0141LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
