import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0339`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0339Mask : ℕ := 5645689297677321

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0339Witness : Array ℤ :=
  #[-116, -129, 58, -70, 61, -32, -55, 79, -36, 47, -71, -48, -1, 34, 35,
  41, 69, 28, 19, -69, -136, -90, -34, 28, 149, 43, 9, 17, -21, -47, 0, -3,
  -101, -145, -6, -103, -13, 81, 138, 63, -39, -12, -78, -45, 73, -20, 67,
  35, 148, 120, -5, -45, 18, 65, -57, 1, 59, -49, -135, -84, 7, 1, 161, 214,
  80, -159, 65, 97, 0, 18, 61, 9, 1, 66, 18, -106, 28, 77, -170, 2, -32,
  -33, 93, 81, 34, 39, 14, 61, 40, -32, 65, -141, 106, 7, 9, 8, -32, -74,
  -10, -74, 47, -17, 89, 41, -8, 20, -23, 35, -64, 62, -36, 106, -54, 4,
  100, -29, 18, -18, -52, -37, -24, 0, 34, 39, 214, 49, -57, -105, -136,
  -26, -11, -171, -120, -107, 9, -43, -175, -82, -15, 26, 59, 84, 15, -59,
  -101, -8, -70, 20, -30, -42, 81, -174, 18, -5, 25, 38, -24, 23, 21, 144,
  69, -8, 12, 128, -28, -9, 22, 42]

theorem fractionalNearFrameSubtreeG2R0339_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0339Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0339Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0339Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0339_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0339LowerBoundTable : List ℤ :=
  [-102, -107, 12, 126, 23, -19, 3, 1, -8, 35, -342, 194, 227, -83, 281,
  121, -463, 72, 9, 205, 133, -44, 102, -44, 72]

def fractionalNearFrameSubtreeG2R0339LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0339Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0339LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
