import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0007`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0007Mask : ℕ := 262402909786257

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0007Witness : Array ℤ :=
  #[326, 419, 468, 315, 345, 261, -426, -358, -240, -324, -393, -519, 90,
  -49, -35, -281, 0, -266, -210, -249, -42, -40, 20, 366, -67, 103, 241, 71,
  50, -218, 134, -128, -65, -89, -191, -371, 48, 210, 78, 124, -69, -52,
  -396, 456, 405, -175, -102, -111, 165, -1, 205, 52, 22, 4, 158, -26, 12,
  -59, -55, 213, -77, -32, 1, 61, -6, -135, 129, 93, -6, 5, -59, -114, -7,
  -111, 56, 64, 7, 55, 52, 65, 173, 12, -69, 131, 7, 70, 79, -90, 67, -132,
  -148, 100, 140, 36, 94, 305, 46, -82, 368, 63, -135, 146, 48, -77, 30, 42,
  154, -14, 107, -121, -262, -63, -205, -83, -160, -190, 0, -83, 54, 161,
  -33, -215, 266, -153, -45, -50, 59, 219, 134, -133, 103, -75, -140, -139,
  136, -15, 73, -109, -14, -16, -14, 217, -225, 84, 191, -68, -129, -94, 33,
  211, 182, 238, 113, 57, 31, 10, 81, 2, 92, 113, 207, 94, 47, 144, 128,
  112, -371, -26]

theorem fractionalNearFrameSubtreeG2R0007_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0007Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0007Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0007Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0007_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0007LowerBoundTable : List ℤ :=
  [-110, 182, 105, 156, 2, 141, 99, -4, 3, 551, 66, 279, -615, 349, 227,
  438, 10, 693, 920, 88, -180, 10, 132, 404, 10]

def fractionalNearFrameSubtreeG2R0007LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0007Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0007LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
