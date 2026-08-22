import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0003Mask : ℕ := 252783137505411

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0003Witness : Array ℤ :=
  #[-97, -57, -41, -192, -236, -151, 48, 67, 154, 44, 99, 64, -23, 128, -21,
  105, 78, 25, 66, 8, 33, -155, -47, -101, -16, 54, 2, -14, 56, 81, 0, 45,
  11, 43, 32, -119, -16, -90, 22, 55, 73, -35, 86, -12, 8, 74, -61, 52, 88,
  -4, -42, 21, -62, -10, -5, 54, -20, -3, 12, 20, 20, -2, 123, -50, 6, -4,
  8, -34, 36, 108, 59, -1, -114, -63, -41, -36, 49, 79, 66, -14, 58, 28,
  -81, 77, 28, -18, 52, -50, -2, 86, -56, 10, 102, -12, 47, 75, 0, 99, 34,
  -10, 62, 68, -5, -17, 2, 22, 43, -115, -94, -133, -57, -113, -106, -5,
  -25, 161, 30, -69, 7, -36, 87, 36, 10, 72, -29, 8, 49, -21, 3, 32, 35,
  -110, -9, -26, -99, 34, 20, -3, -53, -61, 107, -42, -83, -17, -87, 17,
  -147, 48, -19, -1, -30, -39, -50, -32, -24, 47, 48, 85, 72, 10, 1, 30, 51,
  58, -109, 59, -80, 6]

theorem fractionalNearFrameSubtreeG2R0003_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0003Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0003Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0003Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0003_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0003LowerBoundTable : List ℤ :=
  [-87, -138, 107, 81, -24, -131, 101, 121, 33, -80, -52, -39, 11, 169, 68,
  188, -120, 260, 194, 289, 89, 10, 8, -28, 11]

def fractionalNearFrameSubtreeG2R0003LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0003Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0003LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
