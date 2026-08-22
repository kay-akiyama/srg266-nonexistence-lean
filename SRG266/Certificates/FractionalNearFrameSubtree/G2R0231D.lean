import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0231`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0231Mask : ℕ := 2906643463111242

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0231Witness : Array ℤ :=
  #[97, 8, 105, 92, 13, 78, 171, 104, 128, 0, 65, -106, -136, -196, -90,
  -173, -128, -104, -64, -27, -96, 15, 31, 2, 88, -31, 88, 101, 40, 1, -80,
  77, 234, -111, 68, 19, 17, 67, 13, -145, -33, -102, 8, 0, 133, -42, 223,
  -57, 85, -114, 39, 11, 64, -84, -50, -95, 24, -33, -71, 112, 149, -55, 6,
  -15, 7, -58, -20, -40, 22, -24, 51, -20, 70, -8, -64, 148, -66, -166, -50,
  -10, 0, -65, -17, 44, 89, 44, -39, 50, 81, -47, 13, 35, -2, -42, 56, -57,
  21, 92, -81, -38, 13, 95, 19, 24, -21, -4, -8, -148, 30, 75, 57, 17, -23,
  -114, 65, -134, 15, -61, -59, -91, 107, 45, -3, 10, -14, -96, -96, 123,
  71, -30, -8, 29, -137, 122, 59, 121, 79, 64, -210, -91, 49, 16, 130, 1,
  30, 107, -26, -62, 52, -65, 49, 109, -13, 31, -28, 11, 4, -104, -10, -108,
  39, 37, 18, -56, -17, -66, 32, 82]

theorem fractionalNearFrameSubtreeG2R0231_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0231Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0231Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0231Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0231_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0231LowerBoundTable : List ℤ :=
  [-73, 1, 2, 9, -16, 0, 121, 24, -16, 41, -351, 32, 174, 77, 309, -37,
  -305, 10, 198, 73, 217, 290, 137, 374, -55]

def fractionalNearFrameSubtreeG2R0231LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0231Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0231LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
