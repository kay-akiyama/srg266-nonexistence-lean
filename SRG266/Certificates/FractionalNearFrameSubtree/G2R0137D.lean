import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0137`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0137Mask : ℕ := 1354102948144204

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0137Witness : Array ℤ :=
  #[34, -44, 0, 31, -108, -59, 148, 33, -17, 145, 1, 6, 65, 24, -29, 0, -70,
  -72, -73, 77, -42, -62, 70, -32, 49, 69, 20, 45, 79, 100, 31, 78, 76, -45,
  134, -111, -133, 235, 175, 20, 154, -88, -3, -197, 22, -5, 110, -19, 70,
  -71, -43, -23, 121, 76, 104, 61, -66, 80, 43, 0, -41, -6, 46, 48, 8, 110,
  83, -82, -136, -169, 50, -36, -28, 62, 59, 57, -65, 112, 221, -81, -36,
  -17, -18, 5, -71, -6, -99, 42, 28, -94, -7, -92, 115, -68, 73, -113, 51,
  -375, 107, -17, 51, 4, 96, 156, 45, 123, 106, -124, 92, 118, 0, -81, 153,
  75, -44, 19, 195, 198, -113, 44, 26, 112, 38, 126, -49, -67, 76, 136, 2,
  -65, 25, 55, 95, 137, 121, 286, 207, -45, 30, -34, 9, -101, -164, -34,
  -122, 70, 72, -59, 57, 43, 138, 172, -5, 56, 79, -18, 219, 29, -27, -45,
  -114, 28, 208, 52, -5, -97, 45, -8]

theorem fractionalNearFrameSubtreeG2R0137_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0137Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0137Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0137Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0137_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0137LowerBoundTable : List ℤ :=
  [201, 311, 236, 312, 228, 234, 339, 2, 302, 656, 915, 462, 432, 338, 598,
  41, 358, 248, 181, 125, -5, 181, 332, 67, -415]

def fractionalNearFrameSubtreeG2R0137LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0137Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0137LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
