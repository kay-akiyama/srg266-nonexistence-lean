import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0138`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0138Mask : ℕ := 1358769432265802

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0138Witness : Array ℤ :=
  #[-26, -116, -83, -19, -55, -98, 60, 189, 44, 227, 358, -53, 54, -186, 99,
  -129, 3, 189, -19, -40, -73, 6, -52, -34, -171, -34, 90, 254, 141, 234,
  110, -77, 74, -15, -71, -446, -95, 56, 45, 164, -59, 100, 155, 321, 211,
  162, 86, 109, -145, 52, -107, -3, -91, 125, 117, -11, 11, -62, 133, -84,
  52, -56, 154, 26, 30, 39, 196, 307, -56, 119, -78, 57, -44, -72, 353, -10,
  -169, 297, 206, -125, -39, -35, -80, -165, -2, 118, -109, 60, -83, 88,
  206, -71, 87, -201, -39, 245, 113, 114, 79, -51, 122, 89, -67, -91, -93,
  215, 23, 108, 142, 14, -320, -18, 109, 143, -127, -40, -185, -243, -133,
  18, 72, -69, 113, 52, 27, 75, 252, 184, 18, 218, 93, 142, 248, -3, 266,
  -155, -113, 0, -79, -53, 297, -79, -150, 75, -248, 3, 27, -13, -207, 106,
  -205, -262, -183, 2, 263, 188, 86, -95, 18, -78, 65, 248, -66, 340, -9,
  142, 245, -133]

theorem fractionalNearFrameSubtreeG2R0138_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0138Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0138Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0138Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0138_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0138LowerBoundTable : List ℤ :=
  [172, 132, 494, 69, 72, 253, 77, 362, 302, -66, 122, 693, 725, 390, 557,
  865, 609, 703, 10, 10, 256, 611, 557, 567, 750]

def fractionalNearFrameSubtreeG2R0138LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0138Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0138LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
