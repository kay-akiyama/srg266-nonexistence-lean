import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0019Mask : ℕ := 437523387828741

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0019Witness : Array ℤ :=
  #[151, 154, 0, 36, 0, 8, -203, -86, -71, -163, -136, -105, 60, 63, 143,
  22, 174, 3, 40, -40, -81, -52, -35, 105, -116, 10, -47, -18, 28, 144, -21,
  64, 128, -12, -85, -109, 0, -47, 76, 18, -45, -30, -54, -10, 275, 55, 5,
  100, -37, 75, -136, 17, 45, 28, -7, -53, -23, -2, 73, 47, -11, 88, 27, 0,
  -19, 0, -15, -8, -30, 113, 114, -50, 26, -6, 8, 108, -31, 51, -111, -41,
  -40, -26, -55, 13, 28, 58, 153, -47, 205, 60, -53, 80, -3, 96, -76, 19,
  15, -53, 9, 146, -55, 60, 24, -86, 59, 48, 102, 6, 37, 120, 40, -21, -39,
  -1, -88, 35, -164, -42, 5, -7, 83, 70, -97, 28, 100, -28, -13, 58, -154,
  92, 101, 9, -18, -9, -134, -111, -96, 9, 8, 134, -41, 11, 41, 66, 44, -20,
  54, 75, -73, 109, -20, 30, 34, 49, 0, -42, -37, 18, 64, 59, -47, 42, -59,
  -55, -80, -14, 63, 73]

theorem fractionalNearFrameSubtreeG1R0019_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0019Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0019Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0019Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0019_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0019LowerBoundTable : List ℤ :=
  [-18, 3, 160, 43, 1, 2, 394, 156, -29, 205, 273, 11, 131, 159, 422, 40,
  478, 338, 447, 10, 9, -279, 136, -170, 288]

def fractionalNearFrameSubtreeG1R0019LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0019Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0019LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
