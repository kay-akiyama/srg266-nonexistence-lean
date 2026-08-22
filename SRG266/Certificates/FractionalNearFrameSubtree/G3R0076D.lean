import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0076`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0076Mask : ℕ := 2355552939580433

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0076Witness : Array ℤ :=
  #[-5, -23, -95, 40, -195, 14, 34, 181, 25, 141, 0, 35, 98, -5, -110, 18,
  0, 95, 133, 68, -252, -216, -98, 133, 25, 109, -102, -99, 267, 226, -89,
  36, 12, -169, 9, -173, 78, 65, 198, 103, -43, -147, -103, 39, 9, 183, 5,
  59, 39, -117, -149, -36, 149, 55, 62, 55, 3, -133, 235, -79, 245, -1, 115,
  257, 220, 29, 22, 31, 53, -73, 46, 122, 72, 151, 123, 76, 37, -212, 46, 8,
  201, 121, -14, 43, 152, 57, -67, 92, -40, 0, -29, -3, 157, 165, -210, 103,
  86, 72, -45, 129, -83, 124, -5, -215, 26, -10, 60, -146, -75, -251, -145,
  65, 2, 115, 135, 121, -13, -57, 118, 170, 45, 67, 73, 128, -28, 29, -62,
  128, -39, -39, 51, -151, 163, 64, 231, 84, 35, -128, 138, -244, 188, -191,
  31, -69, -69, 144, -92, 52, 3, -113, 60, 129, -57, -109, -347, -172, 94,
  -213, -19, 20, -20, 130, -155, 45, -184, -55, 0, 86]

theorem fractionalNearFrameSubtreeG3R0076_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0076Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0076Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0076Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0076_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0076LowerBoundTable : List ℤ :=
  [-19, -113, 1, 49, 138, 191, 104, 444, 362, 159, -324, 487, 249, 217, 25,
  9, 863, 391, -64, 10, 783, -208, 330, 656, 763]

def fractionalNearFrameSubtreeG3R0076LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0076Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0076LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
