import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0374`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0374Mask : ℕ := 5737069592134026

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0374Witness : Array ℤ :=
  #[14, -5, 50, -216, 129, -137, -39, -66, 37, -29, 0, -23, 143, -61, -37,
  52, 4, -6, 103, -20, -137, -97, -183, 23, 50, 2, 47, 79, 5, 155, 67, 130,
  -65, -82, 49, 80, 88, -101, 10, -41, 117, -74, 138, 49, 99, -20, -126,
  -125, -46, -108, 64, -86, -10, -30, 34, 14, 93, 100, 238, 49, 6, 35, -138,
  -10, 19, 145, -95, -11, 103, 59, 127, 106, 54, 31, -89, 208, -40, 128,
  -62, 31, 226, 205, 149, 37, 171, 143, 16, 48, 121, 118, 79, -93, -69, 30,
  -28, 72, 147, 246, 197, 91, 103, -69, 111, 93, 44, 148, 306, -79, -50,
  -48, -46, -180, -54, 144, -141, -228, -50, -51, -66, 25, 120, 35, -4,
  -123, 69, 7, 0, 72, 38, -3, -199, -71, 86, -29, 29, 128, 96, -94, -42, 1,
  76, 46, 171, -104, 118, -17, 171, -70, 51, 8, -74, 4, 1, 207, 184, -31,
  -54, -151, -37, 61, -51, 50, 36, 113, -2, -40, 100, 145]

theorem fractionalNearFrameSubtreeG2R0374_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0374Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0374Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0374Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0374_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0374LowerBoundTable : List ℤ :=
  [149, 146, 521, 639, 235, -65, 2, 123, 137, -33, 70, 12, -212, 863, 687,
  819, 395, 856, 592, 250, 739, 544, 107, 565, -311]

def fractionalNearFrameSubtreeG2R0374LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0374Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0374LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
