import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0091`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0091Mask : ℕ := 1213641528908809

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0091Witness : Array ℤ :=
  #[-231, -198, -238, -213, -268, -227, 87, 224, 163, 211, 198, 139, 77, 57,
  52, -33, 66, 0, 153, -18, 3, 51, 51, 38, -96, -40, 4, -84, 57, -25, 70, 0,
  15, -112, -39, -194, 101, 154, 17, 45, 83, -91, -49, -106, 0, -12, -15,
  148, 115, 30, -50, 72, 24, 104, -13, 78, 26, 60, 65, 10, 88, 260, 94, -12,
  100, -29, -50, 48, 5, -24, 76, -17, -15, 0, -3, -47, 64, 97, -27, 58, 2,
  8, 97, -44, -9, 43, 20, 17, 3, 38, 156, 2, -24, 33, -17, 93, 4, 137, 0,
  77, 70, -120, 31, -48, -34, -112, -46, -14, 35, -106, -154, -14, -169,
  -113, -174, -156, -54, 187, 244, -158, -89, 87, -17, 21, -17, 53, -66, 27,
  -66, 69, -113, -27, 59, -3, 121, 23, 46, -64, 8, 6, -22, 60, -28, 8, 39,
  -91, 9, 6, -15, 1, -30, 7, 28, 73, 48, -42, -27, 0, -30, -63, -18, -36,
  94, 3, -38, 39, 99, -81]

theorem fractionalNearFrameSubtreeG2R0091_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0091Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0091Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0091Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0091_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0091LowerBoundTable : List ℤ :=
  [-23, -33, 0, 141, 1, -72, 69, 233, 127, -151, 142, -128, 15, 52, -22,
  -107, 141, 134, 188, 53, 355, 85, 97, 431, 434]

def fractionalNearFrameSubtreeG2R0091LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0091Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0091LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
