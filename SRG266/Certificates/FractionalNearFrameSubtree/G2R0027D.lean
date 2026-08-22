import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0027`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0027Mask : ℕ := 799942645498444

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0027Witness : Array ℤ :=
  #[47, 60, -38, 64, 16, -63, 81, 30, -166, 57, -80, -73, -19, 51, -44, -57,
  -127, -149, -94, -29, -69, -65, 45, -40, 47, -14, 110, 64, 46, 100, -23,
  -19, 119, 77, 43, -100, -44, 56, 56, 162, 128, -169, -163, -176, 24, -85,
  37, 7, 61, 57, 102, 0, 96, 14, 43, -111, -7, -6, 41, -14, -112, -36, -9,
  91, -77, -80, 52, -18, -94, -21, -80, 38, 54, 20, -55, 0, 41, 23, -108,
  85, 81, -96, -33, -54, -14, -110, -54, -62, -132, -36, 45, 40, 21, -24,
  -35, -42, 13, -84, 7, 84, -50, 20, 93, 7, -41, 4, -81, -84, 54, 38, -33,
  -25, -26, -11, 30, 27, -23, 73, 1, 48, -53, -87, 20, -79, 107, -17, -66,
  -48, -112, 102, -67, -108, 54, -36, -3, 135, 59, -51, -58, -31, 38, 9,
  -63, -56, 21, -152, 71, 222, -7, 26, -115, 9, 65, 96, 40, -1, -93, -102,
  -20, -106, 18, -46, 28, -62, 78, 13, -6, -42]

theorem fractionalNearFrameSubtreeG2R0027_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0027Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0027Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0027Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0027_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0027LowerBoundTable : List ℤ :=
  [-173, -77, 2, -126, -35, -47, -150, -113, -232, -297, -217, 8, 135, -18,
  33, 170, -602, -173, -37, -285, 132, 218, 12, -1, 10]

def fractionalNearFrameSubtreeG2R0027LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0027Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0027LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
