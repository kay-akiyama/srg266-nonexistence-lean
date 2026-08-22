import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0013`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0013Mask : ℕ := 4870615760455941

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0013Witness : Array ℤ :=
  #[82, -17, 66, -48, -4, -132, -92, -155, 53, 42, -23, 0, 147, 89, 119, 78,
  30, -3, 6, -97, -75, 83, 44, -9, 62, -28, 33, 5, 2, -19, -42, -12, -16, 3,
  8, -86, 56, 24, -7, 77, -55, 14, 6, 66, 9, -6, -5, -82, 69, 127, 48, 23,
  47, 89, -17, -15, -12, 0, 26, 101, 26, 136, 74, -42, -52, 40, -62, 7, 0,
  0, -14, 89, -21, -33, 141, -49, -70, -17, 14, -37, 47, -63, -35, 42, 62,
  59, -13, 36, 123, 9, 5, 71, -16, -25, -79, 40, 110, 36, -61, 64, 9, -32,
  66, 17, 66, -66, -50, 1, 1, 83, -136, -5, 76, -47, -68, -5, -74, -24, -54,
  20, -56, 75, 63, 85, -69, -105, 85, -104, -51, -67, -107, 68, 64, 38, 73,
  -4, -46, -11, 26, -42, -23, -8, 16, -123, 90, 16, -110, -54, -38, -63,
  -68, -42, -42, -28, -33, 40, 24, 70, 8, -18, 19, -14, -1, 35, -26, 44, 11,
  24]

theorem fractionalNearFrameSubtreeG4R0013_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0013Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0013Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0013Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0013_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0013LowerBoundTable : List ℤ :=
  [-27, -177, 115, 10, 25, 4, 111, 171, 63, 76, 9, -92, -306, 202, 241, 153,
  266, -243, 10, 118, 9, 168, -92, 338, 328]

def fractionalNearFrameSubtreeG4R0013LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0013Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0013LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
