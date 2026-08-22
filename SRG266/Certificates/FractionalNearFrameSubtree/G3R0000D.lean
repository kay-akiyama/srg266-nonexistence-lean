import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0000`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0000Mask : ℕ := 260296109105283

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0000Witness : Array ℤ :=
  #[121, 136, 0, -32, 10, 31, -188, -213, -242, 0, -145, 5, 51, 27, 90, 42,
  82, 13, -76, -113, -127, -157, -35, -149, 254, 15, 0, 229, 139, -42, 92,
  3, -1, -76, 162, -187, -153, -84, 0, 127, 266, -120, -57, -43, -12, 206,
  260, -22, 85, 49, -267, 136, 302, -284, -195, -9, 184, 254, -317, -114,
  229, -86, 55, -2, 74, -48, 90, -42, 72, 76, -52, 85, -57, 29, 104, 63, -8,
  25, 40, 22, 128, -16, 70, 45, -47, -57, 30, -32, 168, 30, 81, 156, 122,
  232, 11, -61, -87, -85, -9, -91, 98, -42, 143, 53, 124, 71, 33, -147, 138,
  -75, -151, -63, 44, 105, -93, -34, 162, 0, -27, 14, -69, -72, 54, -146,
  -98, 11, 2, 80, -25, -110, 47, -85, -48, 62, -19, -66, 155, -4, 19, 179,
  75, -138, -20, -116, -155, -80, -17, -115, -79, -36, -11, 14, -191, -72,
  220, 15, -27, 46, 78, 113, 35, 25, 255, -106, 60, -26, -155, 45]

theorem fractionalNearFrameSubtreeG3R0000_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0000Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0000Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0000Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0000_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0000LowerBoundTable : List ℤ :=
  [-111, -149, 183, 247, 2, 1, 174, -98, 0, -107, 10, -263, 84, 441, 841,
  -92, 265, 160, 695, 284, -286, -185, 383, 305, 9]

def fractionalNearFrameSubtreeG3R0000LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0000Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0000LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
