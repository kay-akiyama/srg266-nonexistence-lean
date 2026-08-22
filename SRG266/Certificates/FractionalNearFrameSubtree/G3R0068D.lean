import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0068`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0068Mask : ℕ := 1039705436689058

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0068Witness : Array ℤ :=
  #[47, 19, 73, -67, 93, 16, -6, 22, -60, -16, -30, -53, -58, -28, 0, -78,
  -17, 4, 80, 1, -31, -16, -10, 88, -39, -11, -26, 32, 57, 9, 8, -2, 36, 40,
  65, 20, 40, 67, -70, 0, -112, -89, -21, -10, 42, 8, 14, 26, -13, 101, 1,
  -18, 20, -113, 6, 20, 68, 54, 36, -121, -180, 18, 20, 40, -12, 13, 36, 31,
  14, 10, 9, -90, -94, 109, -50, -10, 29, 52, 27, 24, 48, 69, 77, -36, -50,
  14, 36, 0, 40, -7, 8, -71, -51, -19, 169, -48, 8, -15, 10, 19, 44, 88,
  -85, -60, -83, -84, -47, 14, -58, 2, 87, 67, -42, -2, 43, 19, 17, 116, 31,
  3, -41, -171, -39, 13, -76, -158, 27, 22, 26, -21, -26, 20, 16, -124,
  -104, 142, -16, 91, 9, 16, -1, 32, -72, -5, 53, -12, 35, 21, 7, 64, 34,
  -94, -71, 15, -36, 3, 25, -90, 64, -51, -89, 120, -4, 159, 136, 68, -115,
  82]

theorem fractionalNearFrameSubtreeG3R0068_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0068Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0068Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0068Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0068_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0068LowerBoundTable : List ℤ :=
  [-53, 16, 43, 68, 77, -30, 77, -66, -26, -175, 215, -187, -52, 251, 190,
  -360, -92, 111, 11, 10, 10, 149, 274, 66, 231]

def fractionalNearFrameSubtreeG3R0068LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0068Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0068LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
