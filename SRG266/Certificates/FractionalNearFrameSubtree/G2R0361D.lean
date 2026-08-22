import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0361`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0361Mask : ℕ := 5713994201109130

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0361Witness : Array ℤ :=
  #[9, 109, 67, 104, 77, 120, 41, 35, 0, 49, 35, -112, -64, -84, -93, -87,
  35, 43, 39, 27, 97, -63, -10, -104, -3, 0, 87, 4, 0, 93, -81, -17, -40,
  72, 42, 102, 47, -3, -34, 75, 18, -19, 56, -18, 25, 20, 6, 84, 26, 14,
  -34, -18, -124, 63, 56, 13, 114, -72, 89, 8, -45, 9, 72, 0, 8, 48, -16,
  30, 75, -45, 10, 9, -42, -18, 56, 44, -16, 77, -22, 8, 9, -15, 0, -15,
  -88, -32, 38, 4, 0, 2, 13, 80, 12, 59, 33, 17, 41, 15, -70, 3, 42, -21,
  -76, 92, -70, -52, 38, 15, 0, 35, 25, 35, 29, -54, -84, 6, -94, -54, -18,
  -7, 21, -33, 20, -104, -21, 9, -33, 24, 81, 70, -33, -20, 29, 5, 105, 35,
  -94, 52, 98, -30, -71, -5, 1, -44, 32, -20, 4, 67, 12, -37, 64, -1, 56,
  21, -58, -68, -20, 21, 80, 58, 6, -48, 49, 81, -81, 33, -18, 11]

theorem fractionalNearFrameSubtreeG2R0361_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0361Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0361Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0361Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0361_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0361LowerBoundTable : List ℤ :=
  [32, 9, 50, 118, 2, 168, 22, 47, 171, 18, 18, 300, 10, -172, 58, 93, 205,
  49, 568, 214, 265, 129, 381, 267, 51]

def fractionalNearFrameSubtreeG2R0361LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0361Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0361LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
