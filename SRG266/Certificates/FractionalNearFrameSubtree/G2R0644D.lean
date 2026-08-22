import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0644`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0644Mask : ℕ := 36107840424364553

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0644Witness : Array ℤ :=
  #[-600, -185, -196, -166, -626, 0, -119, 21, 29, -130, -283, 167, 112,
  508, 333, -118, 222, 198, 48, -104, 315, 418, 712, -362, 138, 196, 338,
  260, -624, -418, 129, -912, -25, 52, 450, -322, 19, -101, -163, 514, 227,
  -98, 193, 0, 541, -616, -511, -132, -236, 229, 146, 261, 133, -204, 166,
  321, -78, 248, 308, -49, -68, -252, -52, 231, 46, -71, 89, -71, -149, 35,
  392, -173, -257, 251, 104, -295, -260, -237, -369, -47, -89, 379, -48,
  129, 22, 42, -78, 315, 179, 257, 514, 284, 47, 443, 129, 429, 560, -255,
  470, -300, 190, -47, 794, 287, -53, 388, -30, 380, 52, 100, -46, 271, 205,
  118, 15, 916, 345, 157, -448, -332, 315, 271, -69, 60, 52, 112, -62, 500,
  69, -503, 199, 213, -128, 179, 0, -147, 100, -29, -115, 673, -417, 147, 7,
  -80, -15, 478, -133, 240, 10, 424, -51, -35, 94, 62, -131, 23, -170, 496,
  -150, -66, -36, 239, 376, -288, 785, -219, 420, -307]

theorem fractionalNearFrameSubtreeG2R0644_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0644Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0644Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0644Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0644_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0644LowerBoundTable : List ℤ :=
  [683, 2394, 633, 611, 1368, 978, 32, -5, 32, 1920, -23, 591, 897, 1470,
  -100, 788, 605, 1060, 1041, 984, 606, -295, 905, 353, 100]

def fractionalNearFrameSubtreeG2R0644LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0644Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0644LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
