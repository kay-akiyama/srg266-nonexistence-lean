import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0004`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0004Mask : ℕ := 254705403805765

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0004Witness : Array ℤ :=
  #[-124, -72, -58, -148, -301, -237, 120, 139, 13, 99, 122, -5, -6, -20,
  26, 11, 0, 10, 150, -73, -42, -245, -188, -16, -60, -14, -55, -60, 9, 0,
  259, 22, 209, 116, 51, 6, -107, 36, -136, -151, 17, 48, 156, -115, -204,
  0, -60, 61, 25, 5, -40, -21, -106, -39, 114, 93, 24, 104, -105, 33, 11,
  -36, 25, -2, 3, -97, -35, 22, -22, 43, -75, 196, -15, -43, 140, -120, -21,
  -10, -56, 93, 20, -34, 70, -22, 51, -13, 116, -75, -100, 56, 18, -1, 62,
  -12, 65, 122, 161, 31, 134, 56, -26, -18, 48, 111, 165, 33, 18, 53, -97,
  -29, -120, -87, -53, -173, -162, -4, -50, 161, 59, -87, 169, 7, -11, 76,
  135, -17, -48, -79, 25, -20, 118, -48, -206, 147, 152, -61, 30, -41, 46,
  -111, 88, 37, -57, -20, 26, 119, -105, -60, -9, 141, -62, -58, 93, -63,
  -138, -93, 110, 83, -65, -115, 51, 68, 137, -106, 0, 27, 42, -137]

theorem fractionalNearFrameSubtreeG2R0004_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0004Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0004Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0004Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0004_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0004LowerBoundTable : List ℤ :=
  [-210, -63, -105, 100, 3, -131, -128, 89, 77, 512, 10, 164, 113, 294,
  -185, 563, -548, 228, -34, 208, -42, -45, 212, -397, 8]

def fractionalNearFrameSubtreeG2R0004LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0004Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0004LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
