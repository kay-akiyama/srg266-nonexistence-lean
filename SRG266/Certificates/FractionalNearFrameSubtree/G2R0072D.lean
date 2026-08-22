import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0072Mask : ℕ := 958278484738660

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0072Witness : Array ℤ :=
  #[173, 130, -37, 476, -123, -197, -120, 10, -189, -282, -123, 580, 198,
  96, 277, 109, 304, 226, -305, 16, 521, 223, 111, 105, 347, 199, -273, 12,
  -107, -736, -97, 364, 197, 258, -30, 86, 348, -160, -39, -112, -214, 49,
  110, 0, 179, -115, -153, 154, -106, 354, 253, 138, 266, 125, -361, 309,
  -293, 62, 237, -170, -168, 198, 53, 355, 161, 253, -409, -67, 491, 256,
  39, 86, 101, -237, -85, 506, 254, 61, 173, -148, -213, 473, 13, -30, 370,
  90, 247, 91, -101, -217, -164, -326, -440, 137, -62, 181, 223, 197, -180,
  -431, -113, -170, 107, -395, 212, 289, 276, -233, 235, 258, 400, 52, -200,
  544, -486, -306, 82, -224, -154, -181, 130, -185, 340, 291, -21, -42, -63,
  -146, 70, -49, 88, -277, 274, 90, 414, 161, 260, -226, 190, -256, -218,
  237, -58, -310, 214, -3, -281, -71, -95, 183, 96, 67, -108, -4, 188, 349,
  -135, -274, -185, 58, -161, 90, 378, -45, -84, -179, -15, -182]

theorem fractionalNearFrameSubtreeG2R0072_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0072Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0072Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0072Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0072_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0072LowerBoundTable : List ℤ :=
  [8, -27, -175, 1, 41, 572, 912, 71, 774, -487, 1538, 1268, 419, -722,
  1178, -734, 759, 910, 1019, -353, 1014, 412, 1343, 1981, 568]

def fractionalNearFrameSubtreeG2R0072LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0072Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0072LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
