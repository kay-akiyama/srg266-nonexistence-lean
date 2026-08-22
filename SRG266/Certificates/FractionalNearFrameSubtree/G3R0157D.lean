import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0157`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0157Mask : ℕ := 6850636267303716

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0157Witness : Array ℤ :=
  #[189, -7, 93, 0, 34, -21, -122, -10, -137, 26, -211, 3, -120, 44, 39,
  -67, 83, -111, -75, 63, -19, 32, 9, 100, 39, -4, 26, 24, -247, -54, 317,
  129, 115, -54, 22, -91, -20, -206, -45, 52, 80, -137, -82, 0, 21, -107,
  -79, -17, 1, 53, -18, 59, 73, 113, 119, 48, -69, 113, -156, 1, 183, 184,
  -179, -246, 83, 130, 113, 8, 67, -54, -87, -151, -71, -88, -55, -75, 67,
  -102, -72, -96, -12, 75, 4, 0, 58, 25, 8, -4, 85, 38, 88, 4, -7, 28, -28,
  -223, 52, -59, 32, -55, -56, 109, 64, -77, 75, -166, -57, -33, -61, -14,
  15, 51, 117, -14, 37, -66, 0, -108, 6, 95, 9, 164, -33, 20, -68, 75, -132,
  -132, -85, 54, -13, -80, -21, 11, -71, 94, 85, -32, 12, 195, 11, -51, -88,
  124, 89, 27, 23, 117, 9, 52, -53, 33, 124, 46, 34, 126, -77, 230, -15,
  -67, -3, -3, 17, 83, -176, 168, 36, -69]

theorem fractionalNearFrameSubtreeG3R0157_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0157Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0157Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0157Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0157_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0157LowerBoundTable : List ℤ :=
  [-46, 139, 149, -57, 54, 62, -172, 2, -150, 302, -96, 482, -26, 203, 63,
  -379, 11, -64, 259, 483, -297, 10, -194, 160, 11]

def fractionalNearFrameSubtreeG3R0157LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0157Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0157LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
