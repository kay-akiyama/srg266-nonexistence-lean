import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0100`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0100Mask : ℕ := 2520335281668770

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0100Witness : Array ℤ :=
  #[-2, 26, 16, -133, 6, 192, -66, -62, -24, -119, -58, 60, 69, -4, -21, -7,
  -56, 57, -98, -100, -48, 128, 142, 123, -10, 72, -55, 72, -25, -44, -134,
  25, 52, 44, 30, 23, -35, 96, -72, -23, 25, -2, -82, 28, 109, -19, 42, 24,
  -89, -81, -68, -104, -90, 61, -176, -116, -153, 120, 98, 68, 74, -2, -90,
  83, 140, 109, -39, 67, 60, -73, 45, 54, 93, 21, -38, 62, 0, -70, -1, -58,
  -20, 0, 31, 112, 73, 42, 104, -18, 32, 20, -15, 26, -44, -8, 45, -11, 46,
  -43, -101, 17, -44, 55, 17, -94, -96, -86, 34, -8, 6, -125, -65, 32, -11,
  17, -20, -38, -124, -56, 42, 56, -12, 53, -2, 11, -183, -42, -3, -74, -22,
  12, 21, -89, 11, 23, 151, 34, -5, -2, 8, -39, 98, 12, -9, -38, 3, 69, 24,
  46, -4, -63, 41, -49, 70, -46, -84, -14, -65, -117, -136, -67, -167, 75,
  163, 0, -12, 26, 41, -32]

theorem fractionalNearFrameSubtreeG3R0100_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0100Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0100Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0100Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0100_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0100LowerBoundTable : List ℤ :=
  [-158, -70, -97, -109, -7, 2, -148, 104, -35, -262, -167, 168, 11, 116,
  -37, -212, -75, -72, 78, -49, -152, 381, -54, 70, 420]

def fractionalNearFrameSubtreeG3R0100LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0100Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0100LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
