import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0466`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0466Mask : ℕ := 5807454685172882

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0466Witness : Array ℤ :=
  #[-47, 4, 81, -8, -65, 0, 30, -145, -12, -66, 0, 8, 61, 3, 113, -52, -48,
  24, 26, -80, -8, 67, -10, 22, -18, -54, 85, 58, 0, -12, -16, -30, -12, 16,
  -25, 135, 17, -82, -80, -36, 112, 129, 38, 59, 54, 23, -75, -130, -79,
  -73, -15, 36, 120, -53, 68, 34, -239, 13, -48, 4, -2, -29, -14, 48, -17,
  72, 135, 3, -102, -65, -44, 37, -77, -19, -80, -25, 25, -59, -83, 25, 6,
  -30, 27, 69, 60, -158, 113, 27, -51, 24, 50, 23, 103, -7, 50, -169, 32,
  -93, -92, -23, -18, 6, 35, 44, 16, 97, 192, 168, 147, -40, 18, 62, -157,
  -114, -62, -93, 33, -32, 63, -135, 36, 137, 139, -36, 6, -22, 16, -10, 51,
  27, 14, 11, 30, 37, -47, 31, -26, 75, 142, -47, -46, 27, -44, -24, 36,
  114, 22, 14, 34, -83, 63, -65, -11, -34, 34, -35, -67, 19, 64, -58, 55,
  -37, -10, -112, 13, 24, -59, -18]

theorem fractionalNearFrameSubtreeG2R0466_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0466Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0466Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0466Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0466_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0466LowerBoundTable : List ℤ :=
  [-84, 52, 18, -38, 63, -89, -190, -83, 120, 78, -68, 289, 308, 329, 126,
  48, 10, -278, 198, 9, 222, -254, 168, 150, -63]

def fractionalNearFrameSubtreeG2R0466LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0466Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0466LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
