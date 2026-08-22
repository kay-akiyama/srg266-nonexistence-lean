import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0219`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0219Mask : ℕ := 2471318463087174

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0219Witness : Array ℤ :=
  #[15, 236, 489, 22, 141, 161, 96, 4, 337, -145, 0, -243, -372, 204, -311,
  -596, 16, -197, -310, -559, -396, 280, -96, 366, -1, 58, -156, 366, 651,
  398, 730, 165, 558, 874, 344, 138, 513, 68, -58, -784, -444, -285, -12,
  -278, -178, -382, -630, -191, -396, -452, -398, 909, 601, -519, -508, -40,
  -379, 953, 825, -141, 423, -197, 597, 558, 223, -175, -148, -494, -120,
  155, 452, -325, 478, 256, -313, -142, 133, -316, 409, -82, 260, 152, -314,
  33, 178, 88, -185, 486, -41, 37, 371, 415, -220, 26, 158, 296, 206, 46,
  303, -432, -47, 149, 28, -91, 92, 255, -46, 55, 492, 168, -186, -274, 113,
  -27, 387, 169, 317, -276, 191, 208, -227, -17, 302, 172, 60, 208, -600,
  359, -553, -553, -194, -581, -136, 323, 351, -91, -116, 55, 15, -61, -58,
  184, 153, 148, -622, 570, 389, 72, 418, 135, 246, -598, 614, -89, -331,
  -131, 0, -229, 67, 72, -113, -444, 146, -249, 355, -151, 294, -9]

theorem fractionalNearFrameSubtreeG2R0219_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0219Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0219Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0219Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0219_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0219LowerBoundTable : List ℤ :=
  [-52, 32, 32, 414, 342, -484, 584, 900, 920, 1213, 49, 1881, 479, 777,
  823, 929, 447, 883, -355, 2303, 569, 99, 2014, -1137, 100]

def fractionalNearFrameSubtreeG2R0219LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0219Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0219LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
