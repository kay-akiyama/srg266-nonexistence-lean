import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0103`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0103Mask : ℕ := 5542795728816728

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0103Witness : Array ℤ :=
  #[91, 40, 20, -5, 65, 70, -45, -37, 45, 40, -23, -26, -101, 40, 50, -75,
  145, -14, -4, -61, 79, 105, 15, -35, 64, 75, 64, 98, -81, 22, 7, -9, 9,
  -41, -38, -59, 130, 156, -61, -56, -172, 104, 47, 57, 39, 29, 0, -88, 115,
  140, -45, 102, 43, -28, 32, -102, 72, -148, 41, 9, 130, -66, 88, -17, -18,
  169, -42, 49, 59, 50, 162, 29, 18, 20, 27, 75, -47, -13, 166, 53, 23, -70,
  80, -73, 176, 60, 89, 26, 151, -5, 86, 23, 66, 27, 102, 24, 40, -76, 77,
  -25, 202, -104, -91, 64, 21, 36, 133, 3, 38, -80, -2, -18, 8, -72, -38,
  -12, -86, -61, 46, -69, 0, 45, -56, 12, 20, -18, 90, -2, 73, 32, -69, 64,
  -61, 13, -37, 60, -7, -40, 40, 125, -40, 83, 17, -20, -46, 23, -23, 117,
  29, 92, -31, -83, -25, 64, -47, -39, -8, 13, 7, 49, -5, 78, 88, 109, -124,
  82, 170, -38]

theorem fractionalNearFrameSubtreeG5R0103_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0103Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0103Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0103Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0103_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0103LowerBoundTable : List ℤ :=
  [176, 132, 257, 289, 249, 119, 305, 38, 275, 156, 170, 9, -98, 685, 478,
  227, 125, 242, 472, 441, 234, 123, 238, 427, 644]

def fractionalNearFrameSubtreeG5R0103LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0103Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0103LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
