import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0131`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0131Mask : ℕ := 5893749858550162

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0131Witness : Array ℤ :=
  #[112, 118, -101, -91, -50, -135, 169, 54, 80, 0, -30, -20, 104, -89,
  -117, -107, -82, -1, -198, -60, -133, -28, 29, -24, 11, 37, 65, 31, 72,
  163, -86, 43, -93, 100, 301, 48, -190, -151, 6, 116, 241, -91, -118, -78,
  13, 146, 52, 2, 93, 225, -2, -207, -50, 113, 84, 29, -230, -161, 159, 233,
  -6, 0, -41, 61, 123, 136, 9, -41, -5, -21, 99, 120, 57, -9, 91, 305, 22,
  164, 111, -64, -60, -119, 110, -29, 5, 21, 116, -189, 90, 64, -189, 120,
  98, -93, 166, 46, 47, 78, 71, 59, 18, 58, 66, -68, 9, 40, 51, -36, 166,
  39, -36, 134, 86, 39, 98, -96, -128, -29, -164, -75, 3, -22, 110, 40, 83,
  -132, 3, -133, -40, -24, 60, 102, 135, 98, -62, 41, 112, 19, -82, -5, 173,
  -112, 141, -8, -161, 0, 13, 152, 0, 24, -48, -12, 55, -70, 115, 35, -37,
  -59, 135, 62, 42, 65, 63, 8, 77, 24, 215, 99]

theorem fractionalNearFrameSubtreeG5R0131_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0131Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0131Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0131Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0131_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0131LowerBoundTable : List ℤ :=
  [93, 202, 452, 1, 138, 201, 21, 255, 274, 418, 368, 109, 350, 425, 763,
  522, -111, 337, 111, -27, 317, 256, 373, 800, 243]

def fractionalNearFrameSubtreeG5R0131LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0131Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0131LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
