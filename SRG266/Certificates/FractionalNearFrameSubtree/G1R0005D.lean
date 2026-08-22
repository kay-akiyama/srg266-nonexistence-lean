import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0005`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0005Mask : ℕ := 252782197950725

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0005Witness : Array ℤ :=
  #[140, 118, 128, 14, 0, -62, 60, -46, 108, 0, -126, -119, -98, -52, -28,
  1, -122, -166, -22, -107, -166, -204, -266, 104, -25, -47, -110, -196,
  236, 151, 298, 164, 136, 44, -16, -1, 28, 9, 1, -71, -45, -8, -66, -71,
  17, 109, 32, -9, 34, -33, -247, -114, 84, 103, -43, -45, -9, -4, 61, -31,
  -96, 20, 18, 37, 53, -38, -39, 41, 42, -104, -126, -108, 28, -35, -49, -8,
  21, 51, 70, -26, -94, -33, -62, 92, 61, -76, 7, 35, 31, 56, -16, -126, 3,
  176, 94, -91, 46, 68, 75, -79, -136, 64, 47, 66, 99, -20, 84, 126, 62,
  -45, 64, 64, -15, -136, 0, 51, -25, -49, 170, 108, 34, 118, -1, -149, 57,
  56, -21, -8, 14, 100, 24, -74, 20, 178, -105, 31, 36, 33, 74, -48, 3, 101,
  71, 35, -115, 151, 89, -9, 125, 123, -99, 108, 143, 92, -250, -50, -179,
  -2, -78, -138, 72, -158, -144, -3, 6, -50, 42, -48]

theorem fractionalNearFrameSubtreeG1R0005_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0005Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0005Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0005Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0005_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0005LowerBoundTable : List ℤ :=
  [-203, 1, -31, 52, -137, 1, -96, 1, 83, 484, 129, 405, 202, 432, 87, 14,
  269, -63, -138, -2, 227, -156, -289, 10, -75]

def fractionalNearFrameSubtreeG1R0005LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0005Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0005LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
