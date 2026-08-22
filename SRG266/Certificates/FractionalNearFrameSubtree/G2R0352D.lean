import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0352`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0352Mask : ℕ := 5670687080827913

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0352Witness : Array ℤ :=
  #[0, 158, 60, 32, -44, 125, 32, 87, 114, 55, 59, -4, -241, -116, -175,
  -215, -201, -181, -120, -74, -268, 226, -82, -210, -44, 49, -201, -76,
  181, 222, 186, 231, -125, -148, -144, -254, 62, 90, -58, 47, 50, 127, 38,
  -43, 173, -90, -70, 84, 74, -87, 64, -36, -32, 94, 10, 0, 56, 108, -66, 2,
  -120, 196, 21, -238, -54, 123, 139, 188, -123, -33, -76, 16, 131, 68, 62,
  -5, -61, -45, -11, -58, 119, 91, -38, 51, -23, -108, -42, -11, 90, 184,
  220, 101, -10, -34, -16, 5, 14, -21, 148, 85, 37, -76, -12, 49, -115, -39,
  -38, -95, 29, 103, -22, 0, 123, -36, 128, 12, -63, -74, 42, 53, -1, -33,
  -6, -95, -25, -226, 65, -42, 20, -77, -1, -93, 26, 79, 134, -54, 21, -34,
  37, -12, 94, 54, 194, 42, -115, 141, 65, 73, 99, -26, -5, 52, 99, 127,
  217, 161, -67, -53, 101, 82, -53, -42, 62, 85, 56, 66, -30, -144]

theorem fractionalNearFrameSubtreeG2R0352_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0352Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0352Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0352Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0352_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0352LowerBoundTable : List ℤ :=
  [-71, 247, 104, 2, 1, 76, 57, 1, -20, 58, 311, 291, 11, -416, 130, 234,
  -103, 400, 459, -42, 710, -52, 181, 578, 590]

def fractionalNearFrameSubtreeG2R0352LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0352Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0352LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
