import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0263`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0263Mask : ℕ := 5368625121957386

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0263Witness : Array ℤ :=
  #[-58, 31, -41, -121, 112, 105, 26, -52, 51, 192, -15, -57, -55, 48, 52,
  -28, 24, -19, -93, 62, 128, 43, 66, 54, 137, 0, -90, 157, -78, -4, -57,
  77, -73, 89, -92, 37, 117, 27, -55, -12, -6, 20, -41, 9, -167, 172, 16,
  90, 99, 114, 48, 6, 31, -14, -82, 52, 63, -39, 28, -50, 5, -3, 33, 49, 49,
  4, 129, -91, -143, 48, -57, 12, 85, 7, -23, -50, 109, 6, 100, 118, -5, 28,
  56, -49, 119, 93, 8, 38, -18, -1, -98, 5, -67, 55, -59, 7, -37, -21, -70,
  49, -147, -78, -88, -33, 116, 83, -111, 172, 96, 25, 15, -110, 61, -2, 80,
  -30, 74, -81, -60, 91, 54, 105, 218, -85, 14, 51, -13, -2, 36, 79, 22,
  -14, 88, -35, -32, 29, -101, 19, -50, 192, -93, 12, 130, 6, -29, -30, 84,
  -26, 91, 8, 112, 6, 10, -13, 46, 121, -38, 168, -34, 7, -38, -1, 116, 20,
  -3, 27, 0, -20]

theorem fractionalNearFrameSubtreeG2R0263_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0263Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0263Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0263Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0263_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0263LowerBoundTable : List ℤ :=
  [114, 268, 2, 177, 197, 302, 60, 440, 9, 404, 34, 504, 307, 146, -83, 260,
  221, 38, 284, 761, 10, 190, 168, 9, 331]

def fractionalNearFrameSubtreeG2R0263LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0263Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0263LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
