import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0063Mask : ℕ := 4980152527208529

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0063Witness : Array ℤ :=
  #[3, 221, 86, 226, -44, 4, -8, 0, -19, 212, 32, -67, -76, 88, 36, 105, 0,
  -108, 99, 153, -26, -87, 25, 38, -68, 61, -2, 73, 0, -83, 106, 44, -10,
  -42, -69, 140, 12, 0, -32, -10, 5, 75, 14, 74, -180, -61, -154, -108, 39,
  -10, 60, 85, 76, 96, 61, -12, 6, 0, 125, 95, 94, 159, -74, 94, -138, -9,
  113, -149, 155, 181, -23, -40, -111, 27, -227, 143, -9, 51, 33, 31, 248,
  73, -186, -39, -62, -212, -112, 93, 3, -108, -47, 51, 18, 158, -9, -64,
  88, -2, 224, -56, 197, 139, -140, 14, 90, -73, -13, -51, -140, 31, 117,
  108, 128, -122, 142, 63, 85, 30, 146, -32, 147, -41, -27, 118, -5, -105,
  -163, 73, 115, -101, -130, 193, 79, 13, -168, 150, -42, -98, -68, -92,
  -40, -53, 63, 147, 14, -188, 19, 72, -32, 34, -167, 66, 69, -96, 159, -66,
  66, -120, -22, -83, -61, 12, -98, -91, -80, -34, -233, 324]

theorem fractionalNearFrameSubtreeG5R0063_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0063Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0063Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0063Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0063_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0063LowerBoundTable : List ℤ :=
  [-4, 64, -250, 58, 1, 51, 145, 484, 279, -52, -22, 10, 179, 533, -494,
  -174, 270, 10, 149, 507, 409, 790, 208, 515, 312]

def fractionalNearFrameSubtreeG5R0063LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0063Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0063LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
