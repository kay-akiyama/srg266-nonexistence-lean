import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0345`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0345Mask : ℕ := 5668769310684169

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0345Witness : Array ℤ :=
  #[77, 32, 60, 24, -36, -79, -176, -82, -14, -19, -53, 60, 161, 136, 40,
  44, -39, -55, 34, -162, -43, -72, 57, -26, -102, -14, -118, -11, 70, 16,
  151, 174, 73, -78, 28, -203, -88, 12, -117, 21, 148, 191, 48, -239, 222,
  68, 0, 79, -125, -191, -26, -27, 106, -168, -33, 49, 131, -59, 19, -122,
  88, 150, -158, 66, 13, 207, 33, 28, -54, -89, 107, 43, 14, 15, -50, -67,
  -9, 29, 19, -52, 7, -7, -19, 66, -120, 119, 13, 22, -57, 0, -66, -78, 172,
  84, -20, 55, -18, -131, -98, -48, -121, -11, -90, -30, -19, 94, 94, 88,
  -26, 15, 33, 237, 68, 47, 0, -41, -3, -42, -3, 209, 152, 117, -33, -11,
  118, 152, 135, -164, 58, 68, 109, -99, -23, 1, 179, 92, -77, 110, 21, 21,
  109, 64, -131, -12, -34, -84, -93, 83, -1, 35, 48, 27, -146, -97, 16, 188,
  -125, -226, -64, 96, -15, -72, 41, -19, -40, -1, 61, 75]

theorem fractionalNearFrameSubtreeG2R0345_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0345Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0345Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0345Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0345_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0345LowerBoundTable : List ℤ :=
  [-98, 121, 135, 1, -123, 6, 2, 249, 1, 103, 674, 303, 9, 319, 237, 368,
  218, 21, -63, -129, -155, -281, 124, 25, 776]

def fractionalNearFrameSubtreeG2R0345LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0345Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0345LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
