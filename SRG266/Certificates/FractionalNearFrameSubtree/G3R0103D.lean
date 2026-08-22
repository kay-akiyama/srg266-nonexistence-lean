import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0103`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0103Mask : ℕ := 5247678646227602

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0103Witness : Array ℤ :=
  #[165, 174, 182, 15, 53, 24, 145, 18, 241, -66, -145, 88, -3, -67, -65,
  -122, 17, 15, 64, 33, 72, -22, -144, -138, -111, -86, 18, -68, 59, 42,
  119, 127, -81, 136, -79, 383, 272, 68, -116, -124, 48, 125, 69, 164, 94,
  235, 212, -149, 90, 40, 83, 68, -315, -282, -303, 58, 118, 0, -61, -1,
  245, 54, 60, 71, -51, -53, 80, 75, 102, -86, 113, 57, 76, -19, -51, 20,
  -68, 3, 87, 24, 86, 84, -66, 44, 95, -116, -183, 84, 20, 40, 5, -4, 29,
  74, 13, 15, -78, 201, 16, -91, -122, -64, -159, 199, -61, -208, 135, 0, 2,
  -15, -137, -114, -119, -27, -194, -162, -47, -95, -53, 0, 90, 111, -95,
  -87, -195, 92, 112, 139, -116, 169, -79, 58, 62, 99, 124, 69, 83, -236,
  -5, 70, -136, 93, 0, 28, -119, -2, 58, 2, -70, 12, 40, -4, 96, -30, -30,
  -114, 59, 81, 87, -91, -36, 168, 120, 18, 0, -140, -93, -215]

theorem fractionalNearFrameSubtreeG3R0103_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0103Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0103Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0103Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0103_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0103LowerBoundTable : List ℤ :=
  [-130, -173, 2, -110, -103, 2, 3, 661, 345, -62, 208, 176, -69, 63, 228,
  321, -381, 9, 97, 18, 185, 385, 35, 105, 1601]

def fractionalNearFrameSubtreeG3R0103LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0103Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0103LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
