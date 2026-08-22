import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0071`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0071Mask : ℕ := 958003875267668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0071Witness : Array ℤ :=
  #[27, 0, 61, -42, 65, -5, -81, 18, -52, -141, -79, 85, 62, 39, 165, 98, 2,
  -8, 39, -24, 44, 31, -23, 40, 13, -87, -13, 18, -33, -13, -116, -14, -100,
  122, 94, 8, -13, 99, -105, -12, -23, 41, -31, 27, -122, -53, -81, 24, -39,
  18, -4, 1, 66, -2, -21, 0, -96, -46, -56, 25, 28, -46, -75, -63, -13, 14,
  22, 24, -2, -29, 107, 28, 148, 12, 72, -51, 55, 31, 4, 30, 16, -4, -24,
  16, -4, -22, -25, 36, 21, 15, 38, -65, 147, 85, -14, 3, 11, -106, -128,
  -13, -52, -58, 20, -81, -52, 8, -72, 68, 26, -44, -46, -38, -9, -13, 59,
  -42, 0, 28, 112, -2, -29, -34, 66, 30, 29, 75, -55, 23, 15, 47, -55, -35,
  -14, 13, 78, -4, -45, 8, 17, -38, -1, 28, -40, 27, 32, 55, 57, 3, 37, 65,
  -33, -2, -77, 16, 31, 36, -56, -96, -13, 42, -61, -38, 9, 2, -17, 1, 11,
  19]

theorem fractionalNearFrameSubtreeG2R0071_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0071Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0071Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0071Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0071_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0071LowerBoundTable : List ℤ :=
  [-83, 8, -108, -4, -113, 10, -44, 212, 61, 178, -57, -28, 10, -19, -184,
  197, -55, 89, 9, 11, 182, -23, 77, 10, 41]

def fractionalNearFrameSubtreeG2R0071LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0071Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0071LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
