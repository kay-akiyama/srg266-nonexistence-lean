import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0092`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0092Mask : ℕ := 1235694983816195

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0092Witness : Array ℤ :=
  #[22, 54, 101, 38, 38, 39, -62, -74, -120, 0, -9, -96, 38, -27, -23, 65,
  53, -37, 51, 7, 61, -37, -88, 26, 99, -39, 154, 83, 11, -57, -136, -19,
  -13, -15, 42, -7, 88, -37, -43, -56, -33, 3, 60, -4, -30, 31, -22, -5, 6,
  57, 30, 93, 0, 8, 8, 28, 91, -44, 8, -38, 15, 88, 8, -11, 48, -32, -12, 4,
  -18, 59, 30, 51, -21, -55, -61, -60, 60, -4, 4, 44, 114, 89, -20, -6, 26,
  17, 1, 14, -59, 134, 32, 73, 28, 90, 85, 25, 51, -55, 15, 16, -12, -44, 1,
  -81, 44, 47, -22, 66, -68, -15, -19, -25, 0, -53, -17, -145, -40, -114,
  -10, -5, -42, 61, -10, -29, 9, -10, -24, -1, 8, 35, 55, -46, 59, -39, 49,
  22, 29, 84, 40, -25, -55, -115, -79, -88, 42, -20, 60, -83, 9, 16, -34,
  17, 43, 45, -62, 54, -3, -42, 54, -27, 26, -37, 0, -24, -29, -28, 30, 52]

theorem fractionalNearFrameSubtreeG2R0092_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0092Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0092Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0092Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0092_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0092LowerBoundTable : List ℤ :=
  [-21, -93, 47, 178, 3, 77, 86, -2, 20, 37, -34, -325, -23, 224, 110, -4,
  240, 123, 226, 129, 9, 15, 279, 9, 10]

def fractionalNearFrameSubtreeG2R0092LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0092Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0092LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
