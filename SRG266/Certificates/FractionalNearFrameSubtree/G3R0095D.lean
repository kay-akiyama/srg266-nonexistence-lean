import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0095`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0095Mask : ℕ := 2512506093245524

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0095Witness : Array ℤ :=
  #[-51, -29, -79, 49, 44, 36, -8, 33, 43, -29, 21, -151, 73, -23, 6, 10, 0,
  -5, -55, 32, 47, -15, -28, 55, 69, -74, -70, -26, 25, 86, -14, 42, 46, 66,
  -100, 40, 22, 0, -152, -11, -53, 13, 6, 145, 58, -43, -5, 59, -39, -113,
  -38, -59, 77, 8, 89, 28, -117, -147, 47, -69, -23, 75, -4, 76, 125, 0, 26,
  -7, -33, 128, 101, -118, 72, 38, -73, -10, 13, -42, 75, -67, 45, 63, 29,
  -83, 15, 22, -6, -53, -88, -53, -11, 38, -22, -29, -32, -33, -25, -32,
  -13, 4, -117, -81, -47, -26, 62, 72, 44, -53, -32, 125, 10, 10, 66, -105,
  51, -22, 14, 0, 10, 61, 167, 60, -65, 131, -51, 25, 72, 13, -10, 40, 20,
  104, 3, 18, -8, 97, 6, 44, -7, 80, 83, -183, -43, 25, 23, 33, 120, -2, 49,
  75, 1, 60, -57, 60, 85, 99, 109, -19, -79, -55, 91, 70, -27, 15, -52, -1,
  -46, -47]

theorem fractionalNearFrameSubtreeG3R0095_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0095Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0095Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0095Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0095_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0095LowerBoundTable : List ℤ :=
  [-39, 148, 1, 2, 65, 5, 7, 3, -7, 218, 768, 303, 333, 89, 9, 231, -69,
  511, 9, -142, 25, -85, 11, 259, 270]

def fractionalNearFrameSubtreeG3R0095LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0095Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0095LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
