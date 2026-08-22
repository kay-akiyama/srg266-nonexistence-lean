import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0049`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0049Mask : ℕ := 963570715705746

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0049Witness : Array ℤ :=
  #[-32, 66, 0, 25, -126, -88, -92, 12, 0, -134, -1, 81, 100, 34, 129, 11,
  23, 142, 0, 45, 14, 51, 50, 38, 63, -14, -98, -134, -95, -120, -41, -9,
  -45, 52, -41, 18, 34, -93, 78, -68, 53, 59, 67, 108, 28, 21, -62, -115,
  -89, -101, 73, 10, -65, 20, -56, 92, -56, -13, -74, 68, -89, 29, 73, -5,
  45, 97, 76, -64, -110, 39, -72, 29, 17, -50, -4, 41, -27, 59, 64, -9, 52,
  -52, -46, 4, -58, 26, -52, -22, -74, -6, -44, -37, 7, 77, 68, 69, -2,
  -116, 93, 45, 74, 59, 12, -6, 0, -82, 9, 34, 6, -51, 6, -26, 180, -26,
  -69, -39, -115, 43, -63, -29, 60, -10, 39, -6, 50, 31, 16, 92, -30, 24,
  47, -51, -68, -9, 45, 130, 6, -77, -33, -37, -114, 11, -38, 58, -10, 39,
  -12, 56, 32, -5, 110, -45, 9, -93, -18, -35, 76, -49, -97, -72, 40, 43,
  10, 32, -5, -23, 47, -32]

theorem fractionalNearFrameSubtreeG3R0049_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0049Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0049Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0049Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0049_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0049LowerBoundTable : List ℤ :=
  [-101, -35, 1, -25, 2, 2, 2, -183, 48, 338, -151, 222, -80, 297, -57, 154,
  -18, 157, -143, 10, 10, 25, 68, 44, -21]

def fractionalNearFrameSubtreeG3R0049LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0049Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0049LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
