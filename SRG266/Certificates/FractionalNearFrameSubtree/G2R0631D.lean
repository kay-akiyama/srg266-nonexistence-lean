import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0631`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0631Mask : ℕ := 11336955565804834

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0631Witness : Array ℤ :=
  #[-10, -16, 64, 80, 50, 61, -92, 3, 38, 0, 19, 34, -54, -25, 37, 0, -58,
  -27, -28, -20, -102, 74, 47, 13, 52, -51, 0, -2, 25, -39, -38, -45, 15, 7,
  15, 79, 72, 1, 14, -34, 9, 0, 86, 38, -35, 8, 8, -79, 123, 35, -50, -51,
  28, 67, 27, 0, -27, 45, 41, -89, 109, 108, -10, 99, -7, 40, -70, -194, 70,
  -18, 21, 34, 14, 41, -16, -104, -50, 15, -143, -23, -42, 53, 43, -33, -36,
  -7, 5, 31, 51, 78, -100, 15, 57, 100, 97, 26, -174, -35, -57, -54, -86,
  -108, 17, -23, 11, 68, -87, -80, 24, -15, 94, -10, -21, 92, -45, 141, -5,
  -5, 63, 14, 19, 200, -65, -20, -24, -9, -27, -29, -13, -18, 62, 44, -81,
  45, -69, 4, -38, -6, -39, -68, 0, 7, 81, 51, 35, -51, -49, 4, 65, 27, 29,
  -6, -12, 35, -2, -11, 73, -44, 1, -3, 23, -56, -24, 30, -183, 97, -28,
  -52]

theorem fractionalNearFrameSubtreeG2R0631_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0631Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0631Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0631Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0631_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0631LowerBoundTable : List ℤ :=
  [-53, 1, -64, -99, 3, 3, 47, 192, 113, 48, 11, -18, -118, 10, 10, 32, 192,
  -296, -34, 0, 331, 233, 40, 10, -4]

def fractionalNearFrameSubtreeG2R0631LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0631Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0631LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
