import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0470`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0470Mask : ℕ := 5809369160791316

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0470Witness : Array ℤ :=
  #[-233, -37, -91, -2, 19, -134, 146, 28, -37, 94, -185, 17, 228, 50, 225,
  216, -69, 32, 13, 254, -44, 1, 101, -134, -8, -201, 75, 83, 0, 156, -117,
  -244, -36, -1, 13, 116, 365, 412, -142, 23, -50, -76, 184, 236, 14, -70,
  32, 123, 171, 72, -141, 66, -162, -73, 29, -230, -5, -8, 20, 94, 231, 76,
  41, -251, 94, 232, 210, 176, 51, -1, -185, 52, -36, 72, 91, -235, 120,
  -118, 102, 272, 296, -7, -76, 192, -3, -23, -149, 212, 133, 20, 7, 1, -74,
  303, -41, -15, 308, -10, 104, -139, -97, -12, 100, 22, -176, 29, -8, -66,
  168, 64, -216, -75, -112, 29, -63, -46, 164, 160, 136, 126, -19, -152,
  222, -129, -131, -83, 101, 133, -22, -24, -19, -129, -154, 51, 93, -115,
  -159, 48, 123, 135, -77, 152, 0, 104, -51, 15, 52, 58, -80, 110, 166, 117,
  143, -72, -170, 364, 10, -80, 92, -322, -159, 392, -124, -28, -80, 22,
  -44, -153]

theorem fractionalNearFrameSubtreeG2R0470_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0470Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0470Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0470Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0470_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0470LowerBoundTable : List ℤ :=
  [103, 81, 118, 647, 335, 256, -111, 2, 446, 448, 9, 685, -121, 286, -142,
  212, 671, 473, 10, 127, 942, 122, 480, -27, 801]

def fractionalNearFrameSubtreeG2R0470LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0470Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0470LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
