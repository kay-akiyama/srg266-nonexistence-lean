import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0018`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0018Mask : ℕ := 4884697187988485

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0018Witness : Array ℤ :=
  #[170, 166, 55, 52, 5, -73, -121, -42, -171, -81, -96, 103, -44, 90, 55,
  -85, -90, -45, 0, 1, -44, 16, 80, -118, 0, -9, 52, 19, 58, 15, 17, 63, 42,
  113, 0, 14, -73, -108, 80, 114, -52, 56, 66, -24, 20, -15, -96, 93, 80,
  36, -33, 11, 60, -6, 92, 24, -28, -84, -11, 53, 40, -66, 5, -5, 2, -24,
  -34, 24, -83, 23, -109, -146, 20, 149, 55, 153, 71, 63, 48, -27, 42, 1,
  71, 61, 39, 10, 46, -94, -44, -28, -30, 65, 10, -76, 20, 34, 32, -54, 47,
  52, 18, 102, -1, 70, 24, -9, 6, 84, 101, -187, -56, -31, -22, -22, -54,
  92, 126, -55, -3, -129, 27, -30, -79, 49, 143, 64, -169, 95, 106, 7, 20,
  114, 63, -8, -12, -30, -3, 27, -48, 50, 101, 20, 78, -40, 81, 3, 43, 52,
  6, -33, -29, -73, -5, 80, -12, -28, -75, 16, -9, 14, 62, -69, -51, -8,
  108, -46, 105, 61]

theorem fractionalNearFrameSubtreeG4R0018_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0018Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0018Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0018Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0018_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0018LowerBoundTable : List ℤ :=
  [26, 46, 42, 0, 200, 10, 135, 91, 247, 145, 199, 91, 309, 155, 336, 274,
  408, 368, 10, 9, -254, 360, 9, 10, 133]

def fractionalNearFrameSubtreeG4R0018LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0018Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0018LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
