import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0012`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0012Mask : ℕ := 658456756863235

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0012Witness : Array ℤ :=
  #[147, -146, -272, -62, -59, 0, 202, 287, 75, -47, 337, 0, -127, 0, 121,
  -76, -226, 208, 211, -63, -169, 141, -40, 36, 213, -116, -87, 0, -56, 5,
  86, 84, -99, -102, 166, -27, 193, 133, 130, 34, 0, 99, -112, -164, -54,
  -96, -230, 107, -23, 19, 24, 61, -67, -111, -43, 73, 19, 6, -84, -66,
  -129, 20, -64, -48, 113, -26, 91, 291, 81, 67, 99, 42, 83, 37, -31, 87,
  49, 15, -1, -48, 47, -57, -75, 41, 5, 47, -41, -13, 164, 85, -69, 119, 98,
  46, 23, -32, 6, 33, -110, 85, 44, -9, -142, -42, -40, -170, -23, 100,
  -132, 184, -44, -75, 63, -184, -167, -146, 0, 28, 83, -87, 246, 66, 13,
  -152, -26, 57, 21, 18, 105, 87, -252, -127, -110, 109, 255, 314, -6, -22,
  -4, -28, 33, 104, 55, 79, -68, 102, -20, 45, 92, 232, -110, 16, 81, 0, 18,
  22, -266, -3, -6, -69, -82, -66, 115, 137, 32, 329, 35, -57]

theorem fractionalNearFrameSubtreeG2R0012_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0012Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0012Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0012Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0012_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0012LowerBoundTable : List ℤ :=
  [-80, 250, 39, -208, 405, 333, 44, 516, 81, 9, 103, 716, 561, 544, -156,
  486, -289, 6, -372, -139, -289, -381, 275, 513, 819]

def fractionalNearFrameSubtreeG2R0012LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0012Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0012LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
