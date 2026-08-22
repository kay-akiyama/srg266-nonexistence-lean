import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0156`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0156Mask : ℕ := 1039890591748464

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0156Witness : Array ℤ :=
  #[-44, -40, -47, -30, 33, 50, -22, 35, 14, -39, 19, -73, 83, -24, -86, -3,
  -35, 4, 5, 36, -8, -15, 44, -42, -33, -34, 36, 33, -24, -12, 5, -75, 35,
  31, 15, 15, 115, 26, -5, -18, -38, 54, 33, 21, -65, 54, -29, 47, -46, 10,
  28, -5, -73, 19, 0, 32, -15, -14, 23, 15, 13, 10, -16, 104, 77, 73, -35,
  -39, 36, -56, 5, 54, 68, -1, 1, 23, -8, 59, -28, 108, 40, 22, -5, 48, -97,
  8, -61, -8, 52, -72, -47, 11, 53, 70, 29, -12, -57, 27, 11, 109, 77, -39,
  -56, -97, 135, 101, -8, -44, -105, -67, 62, -92, -9, 6, -70, -47, -39, 56,
  -33, -31, -60, -24, -40, 90, -50, -122, -183, -4, 73, 112, -2, -41, 25, 9,
  -128, 84, 39, 67, 98, -111, -73, 2, -2, -55, 2, 57, 135, -47, -19, 127,
  72, 38, 35, 56, 5, 20, 25, 134, -142, -60, -8, -15, 4, 103, 117, 196, -24,
  42]

theorem fractionalNearFrameSubtreeG1R0156_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0156Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0156Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0156Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0156_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0156LowerBoundTable : List ℤ :=
  [-6, 35, 186, 145, -63, 56, 99, 1, 50, 80, 427, 134, -96, 11, -1, 325,
  103, 212, 203, -71, 9, -227, 105, -42, -60]

def fractionalNearFrameSubtreeG1R0156LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0156Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0156LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
