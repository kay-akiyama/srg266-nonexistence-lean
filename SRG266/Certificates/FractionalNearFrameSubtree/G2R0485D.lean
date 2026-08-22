import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0485`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0485Mask : ℕ := 5810615512580770

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0485Witness : Array ℤ :=
  #[-97, -6, -122, -137, -85, -108, 0, 96, 54, 58, -153, 6, 153, 69, -43,
  164, -28, 151, -122, -71, 81, 28, 165, -50, -26, -120, 104, -46, 20, -46,
  104, 69, -157, 28, 30, -33, -155, 86, 103, 194, -131, -86, 81, 133, 42,
  127, -122, 29, -21, -68, -45, -85, 0, 2, -5, -39, 3, -86, -106, -11, 0,
  25, 83, 100, -46, -92, 108, -17, -67, 209, 42, 88, 18, -68, -178, 130, 4,
  120, -79, 61, -63, 236, 132, 220, 100, 83, 15, 39, 159, -116, 7, -36, -91,
  249, 91, 42, -34, 90, 51, 128, -21, 70, 107, -45, -13, -102, -74, -93,
  -171, 40, -45, 119, 15, 186, 130, -217, -53, -94, -65, -22, -25, 111, 4,
  18, -95, 51, 186, 207, 131, -106, 20, -98, -15, 164, 170, -46, 0, -65, 32,
  37, -37, 71, 90, -123, 24, 44, -47, 41, -60, 163, 99, 168, -13, 200, 55,
  26, 115, -21, -65, 68, 90, -41, 0, 4, -86, 11, 197, -1]

theorem fractionalNearFrameSubtreeG2R0485_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0485Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0485Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0485Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0485_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0485LowerBoundTable : List ℤ :=
  [122, 329, 226, 217, 365, 277, -80, 2, 148, 94, 254, 99, 106, 194, 297,
  415, 140, 172, 253, 10, 83, 345, 804, 10, 581]

def fractionalNearFrameSubtreeG2R0485LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0485Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0485LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
