import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0315`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0315Mask : ℕ := 5389345256739428

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0315Witness : Array ℤ :=
  #[51, 0, 0, -53, 12, -100, 17, -62, -14, 8, -79, 44, 76, 37, 7, 30, 19,
  -44, 0, 13, 40, -111, 0, -80, 0, -6, 19, 5, -5, 68, 65, -21, 3, -91, 103,
  39, -2, -49, -69, 69, 44, 123, -35, -99, 44, 107, 29, 40, -16, 48, 4, -7,
  -14, 3, 88, 113, 76, 16, 0, 45, -29, -62, 41, 13, -39, 9, -30, 79, -9,
  -40, -22, -62, 0, -16, -55, 33, 57, 19, 51, -5, 41, 8, 8, -59, 76, 10, -4,
  -66, -3, -28, -32, -4, -9, 115, 44, 3, 21, -105, 90, 29, -45, 14, 35, 86,
  122, -85, 63, -105, 4, 61, -25, 29, 64, 3, -12, 101, -18, -29, 28, -21, 3,
  -8, -23, -71, 61, 43, 10, 70, -40, -38, 40, 9, -2, 64, -4, -17, 67, 35,
  -4, -96, -44, 17, 62, 36, 37, 4, 11, 29, -19, -5, 30, 58, 41, -28, -29,
  -51, -10, -19, -48, -6, 19, -11, 22, -2, 16, 8, -62, -34]

theorem fractionalNearFrameSubtreeG2R0315_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0315Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0315Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0315Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0315_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0315LowerBoundTable : List ℤ :=
  [58, 1, 164, 150, 19, 52, 114, 2, 147, 101, 144, 149, -54, 273, -77, 1,
  250, 63, 138, -205, 30, 111, 178, -47, 58]

def fractionalNearFrameSubtreeG2R0315LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0315Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0315LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
