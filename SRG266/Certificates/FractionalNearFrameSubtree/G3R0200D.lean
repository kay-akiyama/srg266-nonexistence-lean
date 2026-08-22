import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0200`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0200Mask : ℕ := 6874408910709912

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0200Witness : Array ℤ :=
  #[24, 24, 81, -41, -9, 58, 6, 82, -16, 69, -47, -7, -36, -82, -55, -78,
  -36, -49, -111, 45, 91, 42, 29, 113, 0, -34, 155, 4, 76, 19, -53, 50, -13,
  82, 39, 38, -147, -58, -9, 40, 99, -12, -29, 32, -12, -30, 11, -34, 64,
  108, -17, -108, 87, 58, -134, -15, -17, -86, -8, -98, -203, -157, -87,
  -46, -54, -61, 0, -147, -236, -98, 68, 83, 0, -52, -5, 107, 92, -73, 26,
  15, 18, -83, -4, 0, 3, 17, -122, -40, 106, 109, -76, 76, 35, -89, -82, 49,
  106, 49, 18, 16, 91, -15, 140, 21, 28, -88, -31, -30, 70, 50, 79, -19, 54,
  7, -156, 44, 0, -31, 48, 15, -27, -21, 139, 86, -26, 156, -142, -94, -178,
  149, -15, 69, -30, 73, -74, -27, 15, 16, -9, -94, 102, 18, 66, 144, 81,
  -115, 39, -62, -100, 49, 49, -74, 10, -116, 63, 150, 89, -4, -122, 46, -4,
  -25, 30, 38, 187, -64, -43, 74]

theorem fractionalNearFrameSubtreeG3R0200_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0200Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0200Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0200Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0200_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0200LowerBoundTable : List ℤ :=
  [-118, 141, -39, 2, 3, 71, -21, 77, -15, 309, -180, 204, 299, -52, -5,
  213, -450, 27, 86, -216, 143, 234, -117, -169, 113]

def fractionalNearFrameSubtreeG3R0200LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0200Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0200LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
