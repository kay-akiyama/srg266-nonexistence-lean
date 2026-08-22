import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0283`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0283Mask : ℕ := 5373074645553392

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0283Witness : Array ℤ :=
  #[0, 26, 19, 61, -44, 54, 4, -68, -1, -67, 20, 47, 39, 56, 33, 19, 63, 74,
  39, 26, -60, 27, -27, -44, -54, -67, -58, -18, 0, 41, -60, 45, -40, 20,
  -96, 20, -92, 43, 53, 108, -16, -19, 3, -69, 49, -91, 25, -22, -24, 24,
  -57, 28, 62, 51, 13, -15, -31, -60, -36, 0, -1, 84, -3, -47, -26, 26, -36,
  -18, -64, 12, -18, -75, -12, -16, -87, 78, -40, -23, 28, 52, -11, -34, 22,
  -37, 18, 88, 99, -7, -30, -46, 16, 50, 30, 42, 54, 45, -38, 51, -71, -24,
  -33, -7, -12, 128, 71, 73, -31, 30, -75, 31, 10, -44, 12, -77, 41, -90,
  -48, 48, 37, 26, 30, 77, -62, 72, 6, 86, -69, 17, -17, 46, 131, 49, 104,
  -65, 16, -98, 14, -5, -74, -39, -21, 11, 58, 106, 14, 35, -43, 26, -78,
  -83, -39, 58, 38, 27, 72, -17, 3, -67, 61, 3, 36, 15, 0, 0, -19, -96, -96,
  -9]

theorem fractionalNearFrameSubtreeG2R0283_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0283Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0283Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0283Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0283_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0283LowerBoundTable : List ℤ :=
  [-9, 47, 3, 2, -70, 87, 92, 25, 2, 9, 32, 394, -85, 11, 28, -17, 31, 34,
  55, 100, -150, -27, 132, -9, 10]

def fractionalNearFrameSubtreeG2R0283LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0283Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0283LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
