import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0051`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0051Mask : ℕ := 963845576827298

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0051Witness : Array ℤ :=
  #[-107, 84, -117, -13, 15, 18, 53, -35, -92, -61, 26, 18, 81, -47, -54,
  29, -71, 117, 103, -74, 17, 19, 52, -7, -32, -82, 70, -12, -29, -146, -62,
  13, -77, -8, 38, 114, 75, -114, 0, 56, 46, 27, 39, 82, 30, 56, 106, -58,
  -66, -24, 20, -71, -34, -59, 36, -146, -29, 60, -28, 66, -18, 69, 34, -85,
  -42, 15, -15, -146, -65, -34, 3, 25, 38, 9, 35, 113, 26, 70, 88, 33, -21,
  -23, -55, -38, 84, -35, -64, -30, 42, -25, -65, -26, -11, 8, 20, -10, -3,
  -45, -31, 47, 51, 11, 9, -1, 40, -45, 19, 20, -75, -30, -5, -30, -64, 65,
  -85, -21, 15, -90, -29, -109, 45, -3, -3, -105, -67, -8, 18, 45, -40, 69,
  30, 20, 43, 7, 66, -64, -85, 4, 5, 90, 29, -35, 18, 83, 76, 65, -1, 37,
  68, 36, -29, 23, 19, -22, -20, 2, -52, 3, 0, -154, 51, -11, -59, 100, 106,
  58, -12, 134]

theorem fractionalNearFrameSubtreeG3R0051_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0051Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0051Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0051Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0051_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0051LowerBoundTable : List ℤ :=
  [-68, 51, 2, 1, 91, 2, -85, -58, -2, -201, 56, 267, -21, 206, -222, -72,
  -21, -21, 19, -346, -61, 247, 12, 293, 8]

def fractionalNearFrameSubtreeG3R0051LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0051Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0051LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
