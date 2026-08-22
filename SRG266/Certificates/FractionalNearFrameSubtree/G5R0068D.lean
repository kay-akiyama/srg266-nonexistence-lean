import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0068`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0068Mask : ℕ := 5027294401369172

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0068Witness : Array ℤ :=
  #[-26, -14, 17, -4, 20, -23, -4, -39, -47, 59, -52, 59, 4, -24, -20, 150,
  -4, 12, 20, -42, -38, 26, 85, -59, 39, 48, 8, -11, 32, -50, 52, -53, -19,
  18, 89, 117, -12, -69, 0, -11, 11, 61, -6, -81, 10, 20, -41, 9, 7, 117, 5,
  16, 63, -5, -42, -26, -32, 70, 45, 61, -89, 9, -10, -76, -36, 45, 31, 43,
  33, 14, 44, 64, 72, 9, 73, 102, -78, -18, -41, 58, 0, 38, 14, 13, 75, -30,
  3, -2, 50, 38, 4, -4, -11, 73, 62, 15, -35, -57, -28, -41, 9, -86, 19, 17,
  -31, 14, -12, 4, -49, 12, 51, 13, 0, 28, 0, -6, -76, 113, -2, 37, -61,
  -76, -40, 13, -21, -46, -71, 0, 41, 6, 33, 67, 65, 47, 4, -83, 49, -9, 58,
  42, 43, -26, 17, -2, -25, 11, 31, 29, 56, -3, 20, 42, -76, 27, 24, 61, -4,
  -120, -45, 10, 4, 103, 0, 23, 42, 63, -15, 98]

theorem fractionalNearFrameSubtreeG5R0068_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0068Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0068Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0068Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0068_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0068LowerBoundTable : List ℤ :=
  [42, 103, 11, 93, 119, 53, 2, 154, 97, 280, 154, 73, 9, 415, 69, 226, 242,
  110, -82, 10, 50, 337, 80, 210, 164]

def fractionalNearFrameSubtreeG5R0068LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0068Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0068LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
