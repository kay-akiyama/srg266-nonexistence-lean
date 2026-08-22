import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0184`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0184Mask : ℕ := 1388171693564144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0184Witness : Array ℤ :=
  #[70, 85, 164, -2, 28, 48, 27, -84, -82, 8, 211, 22, 39, -69, 119, -9, 44,
  177, -53, 200, -48, 98, -6, 36, -75, -91, -114, -52, -10, -52, -77, 12,
  -23, 27, 20, -21, 36, 0, -144, -64, -13, 63, -17, -82, -149, 123, -45, 99,
  251, -80, -47, -158, 25, 264, 170, 63, 16, -185, -46, -74, -120, -22, 93,
  108, 8, 142, -18, 50, 182, -3, 91, -87, -113, 10, 94, -162, 24, 0, -60,
  67, 28, -14, -40, 88, -22, 128, 0, 143, 44, 173, 46, 30, 235, 124, 74,
  -45, -3, 47, 157, 20, 46, 31, -99, -127, 61, 94, 93, 76, 54, 168, 14, 95,
  112, 4, -245, -240, -100, 44, 78, 0, 28, -10, -104, -247, 215, 3, -34,
  233, -54, 85, -176, 9, 1, 41, -50, 78, -69, 161, -56, -62, 101, 15, -12,
  68, -29, -22, -19, -170, 1, -17, -61, -125, -11, 10, -31, 47, 23, -169,
  16, -8, 175, -113, 83, -109, 11, 57, 172, 147]

theorem fractionalNearFrameSubtreeG2R0184_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0184Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0184Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0184Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0184_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0184LowerBoundTable : List ℤ :=
  [42, 3, 186, 161, 151, 78, 166, 43, 277, 613, 31, 288, -178, 126, 480,
  -233, 9, 546, 312, 328, 73, 85, 788, 196, 189]

def fractionalNearFrameSubtreeG2R0184LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0184Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0184LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
