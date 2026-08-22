import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0049`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0049Mask : ℕ := 931890483274828

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0049Witness : Array ℤ :=
  #[314, 293, 0, -5, 104, 164, 315, 85, 86, 1, -12, -156, -171, -117, -318,
  -112, 164, 121, -110, -28, -75, -19, -75, -124, -157, -239, 147, 86, 439,
  459, 101, 113, -26, -60, -200, 231, 263, -130, -247, -283, -187, 154, 237,
  0, -55, 13, 250, 155, 183, -328, -181, -218, 242, 95, 225, -251, -133,
  -284, -88, 255, -146, 74, 130, 292, -59, 395, 225, -169, 0, -107, 35, 128,
  -51, -62, 104, 96, 92, 142, 89, -114, 150, 164, 370, -174, -2, 96, -328,
  -7, -18, 198, 73, -51, 193, 175, 144, -48, 235, 123, -91, -115, -4, 107,
  270, 311, 95, 0, 97, 184, 190, -82, 121, 91, -140, 55, 15, 6, -126, 105,
  157, 145, 62, 118, -69, -109, 29, 120, -115, 44, 96, 135, 100, -170, 192,
  123, 202, 145, 237, -250, 24, 214, -260, -15, -217, -38, 89, 116, -112,
  390, 6, 190, 234, 165, -137, 145, 56, 158, 262, -129, -36, 74, -89, -178,
  161, -37, -73, -5, -55, -55]

theorem fractionalNearFrameSubtreeG2R0049_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0049Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0049Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0049Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0049_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0049LowerBoundTable : List ℤ :=
  [333, 513, 330, 296, 470, 653, 716, 249, 360, 1043, 791, 63, 11, 1002,
  784, 326, -61, 716, 739, 236, 10, 1265, 189, 385, 205]

def fractionalNearFrameSubtreeG2R0049LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0049Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0049LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
