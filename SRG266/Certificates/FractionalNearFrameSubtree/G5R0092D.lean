import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0092`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0092Mask : ℕ := 5509293373295378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0092Witness : Array ℤ :=
  #[-90, 100, 1, -49, -159, 75, 0, 2, 41, 34, 72, -84, -62, -53, 5, -68, 38,
  148, 72, 82, -39, -52, -97, -115, 62, 71, 33, 124, 13, 53, -17, -59, -135,
  -31, 7, -34, 188, 147, -13, -169, 73, 127, 152, 67, -22, -44, 53, 57, 23,
  -7, -39, -6, 5, -52, -56, 0, -113, -5, 140, -1, -117, 20, -87, 6, 61,
  -310, 82, -127, 108, 100, -52, -72, -127, -74, -14, 48, -88, -55, 32, 82,
  167, 45, 111, -241, 0, 83, -54, -34, 80, 27, 2, -46, -3, -2, 138, -8, 23,
  -63, -132, 164, -69, 7, 60, 20, 17, -25, -6, -8, 110, -69, -61, 67, -25,
  -53, 65, -56, 59, 142, 89, -68, 10, 10, 29, 56, 41, 91, -4, -72, -37, 5,
  -41, 239, 20, -68, -20, -66, -90, 60, -3, -105, -138, -118, 56, -119,
  -133, 1, -52, 179, 43, 64, -61, 0, 33, 62, -4, 85, -5, 47, 68, -28, 19,
  -58, 188, -18, 12, 84, 52, -51]

theorem fractionalNearFrameSubtreeG5R0092_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0092Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0092Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0092Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0092_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0092LowerBoundTable : List ℤ :=
  [-83, 111, 10, 1, 168, -200, 150, -5, -11, 130, 316, 9, 90, 188, -316,
  -13, -46, 418, 254, -51, 208, 263, 7, -170, 81]

def fractionalNearFrameSubtreeG5R0092LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0092Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0092LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
