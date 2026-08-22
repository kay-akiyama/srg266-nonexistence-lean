import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0412`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0412Mask : ℕ := 5746690681386136

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0412Witness : Array ℤ :=
  #[-76, 339, 397, 87, -53, -89, -15, 13, -653, -150, 45, -206, -148, -195,
  16, 400, 168, 89, -244, 156, 384, 79, -223, -2, -576, -287, -128, -573,
  -394, -213, -281, 63, -123, 160, 515, 46, -84, -349, 24, 120, -219, 24,
  418, 77, -114, 116, -347, 371, -269, -136, -58, -160, 586, 127, -46, -483,
  457, 468, -415, -135, -261, -687, 244, 404, 705, 0, 377, 256, -233, -516,
  -652, -880, -591, 384, 154, -265, -45, -600, -83, -14, -372, -240, -306,
  1, 100, 534, -795, -407, 103, 74, 4, 23, 172, 158, 41, 142, -44, 316,
  -807, 91, 58, -314, 71, 331, -169, -294, 191, 122, 99, -215, -234, -78,
  -89, 0, 356, -152, 535, -257, -47, 948, 613, -1023, -659, 218, -105, -132,
  210, -59, -565, -406, -326, 332, 131, -513, -884, -93, 368, -19, -122, 56,
  779, 304, 109, 618, -63, 497, -249, 490, -513, 167, 462, 445, 541, -460,
  -415, -160, -464, 15, 37, 144, -52, 6, -75, -301, -3, 266, 183, 126]

theorem fractionalNearFrameSubtreeG2R0412_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0412Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0412Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0412Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0412_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0412LowerBoundTable : List ℤ :=
  [-1026, 32, -666, -93, -102, -276, -571, -261, -911, 100, -109, 261, -813,
  608, -627, 434, -2888, -2274, 898, 1975, 925, 99, 100, 644, 168]

def fractionalNearFrameSubtreeG2R0412LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0412Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0412LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
