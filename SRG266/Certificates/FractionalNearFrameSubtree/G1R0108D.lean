import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0108`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0108Mask : ℕ := 960723286575512

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0108Witness : Array ℤ :=
  #[30, 65, 10, -15, -112, -14, 36, -51, -24, 2, 80, -28, 42, 14, 13, 53,
  34, 48, -24, 1, 34, -72, -38, -18, 15, -35, -41, 30, -30, 4, -88, -95, 4,
  95, 31, 90, -63, -104, 14, 3, 11, 4, 48, 33, -9, -27, -124, -40, 30, -30,
  21, -70, 5, 16, -38, 6, -92, 79, -27, 62, -11, 41, -7, -12, -34, 5, -55,
  87, -57, -27, 25, 16, 40, 69, 10, -19, 0, 82, 51, 23, -19, -15, -11, -76,
  24, 3, 59, 0, 55, 26, 15, 20, -21, 2, 1, -7, -26, -16, 109, 25, 14, 45,
  56, 22, 11, 47, 51, -28, 41, -10, 16, -96, -61, -13, 71, 113, 57, 104, 32,
  47, -20, -9, 68, -84, -75, -48, -40, 55, 58, 15, -2, -3, -71, 48, -1, 36,
  23, -29, -52, -61, -5, 37, 19, -2, 14, 70, 11, 47, 53, -38, -34, 20, 21,
  -43, -45, -28, 65, -56, 41, 38, 54, 74, -2, -33, -53, -1, -28, -1]

theorem fractionalNearFrameSubtreeG1R0108_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0108Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0108Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0108Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0108_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0108LowerBoundTable : List ℤ :=
  [-13, 35, -47, 57, 29, 24, 47, 115, 0, 306, 264, 103, -163, 58, -77, -92,
  -67, 212, 9, 222, 169, -9, 296, 0, 188]

def fractionalNearFrameSubtreeG1R0108LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0108Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0108LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
