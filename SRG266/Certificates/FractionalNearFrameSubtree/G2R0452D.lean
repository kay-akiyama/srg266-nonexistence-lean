import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0452`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0452Mask : ℕ := 5794189672848040

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0452Witness : Array ℤ :=
  #[-108, 109, -56, -35, -8, 52, 123, -31, 63, 119, -32, -60, 61, -18, -47,
  126, 6, 3, 11, 75, 76, 1, 41, 37, -115, 23, -173, -35, -19, -131, -107,
  52, -3, 50, 42, 26, 76, 142, 16, 33, 8, 79, 65, 92, -36, -45, 22, -110,
  -48, 147, -125, -92, -107, -64, -33, 44, 31, -30, 26, -46, 123, 115, 48,
  26, -73, 77, 53, -58, -31, -34, -31, 21, 9, 82, -44, 0, -55, 64, -25, -77,
  -48, 9, 27, -63, -81, 24, -21, 171, 26, -41, 117, 109, 84, -63, -18, 36,
  52, 70, 66, 58, 43, -65, 17, -75, 8, 22, -12, 70, -32, 29, -69, -55, 154,
  -69, -143, -4, -57, 43, -33, -154, -135, 62, 20, 30, -58, 15, 10, 4, -20,
  -22, 61, -1, 23, -114, -14, 56, -70, 11, 54, -30, -116, -33, -40, -25,
  104, -18, 29, -123, -24, -126, 20, -34, 20, -92, -78, 205, -94, 81, 61,
  89, 69, 120, -5, 126, 23, -9, -32, 27]

theorem fractionalNearFrameSubtreeG2R0452_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0452Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0452Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0452Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0452_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0452LowerBoundTable : List ℤ :=
  [-36, -41, 108, 2, 2, 299, -20, -27, 2, 41, -188, 58, -137, -143, 8, 405,
  -152, 26, 238, 12, 152, 10, 129, 388, -19]

def fractionalNearFrameSubtreeG2R0452LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0452Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0452LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
