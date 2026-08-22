import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0554`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0554Mask : ℕ := 6840734689474060

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0554Witness : Array ℤ :=
  #[18, 87, -34, -37, -88, 54, 131, -51, 32, 75, -68, 27, 163, 109, -18,
  -12, 145, 155, 48, 26, -45, 102, 101, -68, -32, -124, 90, 139, -23, 0, 13,
  -61, -5, 142, 55, 129, -73, -55, 27, -23, -129, 43, 25, 86, 38, 58, 10,
  35, 58, 91, -56, -40, -36, -76, 59, 29, -96, -74, -18, -46, -40, 17, 136,
  179, 114, 101, 47, -107, -167, 22, 28, 0, 74, -53, -106, 51, -14, -6, 42,
  -58, 61, -20, 61, -78, 3, 29, 12, 102, -27, 124, 89, 12, 98, -2, 81, 78,
  17, 50, 8, 51, 42, 16, 53, 81, 182, 0, 129, -61, 93, -50, 14, 95, -47,
  -129, 18, -38, 30, 171, -58, 61, 138, 86, -172, -63, -73, -122, 108, 83,
  -63, 49, 172, 15, -5, 93, 157, 32, 17, 59, 15, 16, 162, -29, 58, 150, -24,
  99, -35, -20, 60, -85, 85, 157, 9, 27, -97, 159, 49, 6, -40, -49, -88, 27,
  -1, -2, 81, -130, 84, 8]

theorem fractionalNearFrameSubtreeG2R0554_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0554Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0554Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0554Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0554_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0554LowerBoundTable : List ℤ :=
  [203, 267, 262, 315, 442, 254, 188, 320, 109, 331, 422, 344, 164, 142, 10,
  125, 85, 85, 218, 311, -62, 566, 781, 486, 487]

def fractionalNearFrameSubtreeG2R0554LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0554Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0554LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
