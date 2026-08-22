import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0439`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0439Mask : ℕ := 5786301965186324

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0439Witness : Array ℤ :=
  #[0, 228, 96, 149, -27, 83, 118, 105, 117, 225, 104, -126, -113, -99,
  -264, 56, -78, 42, -95, 119, -75, -275, -234, -190, -18, 49, 287, 398,
  196, 158, 0, -268, -270, 293, 133, 27, 243, 162, -32, 62, 73, 62, -16, 47,
  39, 177, 62, 235, -41, 203, -2, 3, -138, -157, -319, 88, -66, -27, -55,
  -60, 83, 182, 83, -191, 142, 106, 227, 351, 322, -223, -350, 45, -97,
  -155, 87, 13, -29, 0, 61, -95, 99, -127, -36, 103, 168, -1, 54, 57, -66,
  27, 43, -141, 58, 186, 38, 118, 128, 219, 310, -204, 209, 47, 100, -104,
  133, 58, 262, 331, -31, -38, 127, -38, -52, 227, -143, -159, -76, 47, 37,
  153, 207, -20, 173, 82, -56, -175, 53, 94, 150, 138, 98, -40, -32, 7, 124,
  -137, 97, 2, 318, -41, 251, -77, -153, -119, -76, 104, -62, 168, 39, 25,
  147, -22, 150, -95, -342, 50, 255, -22, -81, -51, -174, 15, 56, 184, 347,
  -21, 4, 78]

theorem fractionalNearFrameSubtreeG2R0439_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0439Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0439Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0439Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0439_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0439LowerBoundTable : List ℤ :=
  [338, 376, 625, 557, 507, 220, 138, 362, 325, 924, 22, 10, 635, 51, 536,
  274, 616, 280, 145, 274, 409, 357, 1361, -54, 1124]

def fractionalNearFrameSubtreeG2R0439LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0439Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0439LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
