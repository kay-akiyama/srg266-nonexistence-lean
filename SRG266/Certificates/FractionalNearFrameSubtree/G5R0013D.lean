import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0013Mask : ℕ := 944054518653187

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0013Witness : Array ℤ :=
  #[47, -38, -34, -40, -54, -11, 117, -28, 0, -35, -62, 53, -30, 13, -106,
  -12, 29, 38, -31, -32, -33, -31, -29, -23, -57, -142, -113, -47, -28, -51,
  -38, 247, -61, -67, -78, -77, 29, -38, 21, 113, 100, -16, -40, 3, 11, -3,
  3, -41, 77, 27, 42, -172, -140, 163, -26, -56, -9, 8, -53, -40, 42, -138,
  11, 32, 106, -70, -12, -59, -47, 27, 77, -56, 58, 151, -105, -27, -68,
  -38, -93, -9, 92, 131, -92, 55, 177, -26, -51, 21, 53, 54, -29, 134, -63,
  -13, -22, 22, -10, 27, 146, -5, -44, 34, -65, -30, -81, -45, -101, -32,
  -100, 92, -2, -12, 161, 106, 93, 60, 21, -5, -93, -65, 90, 39, -192, -107,
  109, 91, -74, -136, -2, 3, -122, 162, 44, -36, -20, 18, 12, 84, 52, -22,
  -62, 50, 244, 17, -19, 61, 68, 203, 136, -6, -74, -7, -126, 62, 6, 48,
  -152, -15, 72, 94, -164, -90, -54, 117, 11, 61, -71, 79]

theorem fractionalNearFrameSubtreeG5R0013_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0013Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0013Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0013Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0013_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0013LowerBoundTable : List ℤ :=
  [-137, 77, -31, 1, -48, 2, -17, 12, -75, 311, -123, 120, 9, 182, 43, 418,
  -216, -80, -320, 20, 187, 11, -83, 10, 6]

def fractionalNearFrameSubtreeG5R0013LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0013Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0013LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
