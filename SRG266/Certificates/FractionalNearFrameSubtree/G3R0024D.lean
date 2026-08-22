import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0024`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0024Mask : ℕ := 903089489549857

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0024Witness : Array ℤ :=
  #[179, 252, 308, 102, 460, -36, 107, -231, -21, 135, 22, -103, -49, -210,
  -59, -166, 0, -189, -127, -96, 6, 74, -193, 190, 196, 130, 84, 22, 44, 24,
  -110, -21, 43, 168, 237, 218, 91, -289, 21, -179, 65, 147, -97, 14, -20,
  122, -24, -184, 25, 18, -118, 130, -27, 63, 63, 63, 76, 21, -244, -116,
  88, 80, -79, -16, -74, 69, -100, 226, -207, -27, -66, -141, -21, 61, -70,
  -106, -28, -147, 46, 43, 62, 102, 38, -45, 137, 54, 37, -175, -106, 1,
  -83, -36, -168, 31, 11, -65, -112, 112, -237, -10, 79, -39, -13, -60, 48,
  170, 213, 23, 139, 118, 9, -88, -27, -144, -98, 92, 37, 101, 11, -178,
  -30, 36, -13, 58, -59, 94, 139, 75, -120, -101, 212, -20, -119, -39, 195,
  32, 75, 161, -180, 81, 168, 42, 250, -226, 23, -42, 161, 126, 70, -3, 83,
  116, 14, -165, 11, 72, 46, -33, -130, 57, -12, 19, -83, -163, -40, -73,
  12, 73]

theorem fractionalNearFrameSubtreeG3R0024_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0024Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0024Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0024Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0024_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0024LowerBoundTable : List ℤ :=
  [-109, 138, 2, 1, 8, 1, -29, 60, 210, 1, 549, -22, 115, 437, -38, 41, 363,
  -93, 316, 10, 449, 578, 9, 484, 165]

def fractionalNearFrameSubtreeG3R0024LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0024Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0024LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
