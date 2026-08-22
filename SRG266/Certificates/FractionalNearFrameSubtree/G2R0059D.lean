import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0059Mask : ℕ := 953985034813642

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0059Witness : Array ℤ :=
  #[20, 32, -131, 0, -11, -34, 49, 0, -55, -75, -111, 91, 128, 18, -190, 32,
  88, 17, -7, -13, -51, 15, -23, -59, -44, 27, 72, 102, -89, 73, -108, -152,
  41, -105, -41, 412, 310, -70, -181, 204, 237, 171, -257, -453, -299, 65,
  -19, -76, 32, -148, 221, 62, -159, -177, -150, 120, -106, 21, -41, 29,
  138, 71, -80, 101, -57, -38, 50, -102, -106, 120, 36, -6, -123, 96, -33,
  -7, 75, 76, 61, -28, 68, -22, 99, 43, 136, -11, -94, -5, 44, -5, 71, -6,
  -14, 49, -178, 143, 18, 37, 10, -1, -29, 59, -32, 11, 41, 315, -52, 71,
  -62, -29, 121, 93, -61, 116, 46, 14, -58, 140, -11, -38, 121, 35, 2, 149,
  95, 41, 156, 173, -63, 5, -8, 77, 82, 50, 50, -23, 28, -11, 0, 52, 52, 39,
  140, -33, 193, 70, 2, 29, 95, 0, 285, 147, -42, 0, -222, -68, -49, 31, 59,
  -73, -65, 85, 154, -53, 164, 261, 291, 19]

theorem fractionalNearFrameSubtreeG2R0059_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0059Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0059Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0059Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0059_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0059LowerBoundTable : List ℤ :=
  [126, 707, 41, 311, 90, 547, -129, -135, 474, 1091, 9, 21, 574, 236, -157,
  -497, 267, 233, -51, -174, 407, -148, 498, 537, 444]

def fractionalNearFrameSubtreeG2R0059LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0059Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0059LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
