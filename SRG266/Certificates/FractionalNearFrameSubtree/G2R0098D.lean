import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0098`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0098Mask : ℕ := 1247107913081865

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0098Witness : Array ℤ :=
  #[20, 117, 0, -68, 27, 25, -97, 72, -39, -3, 167, 0, -148, 2, -58, -100,
  -153, -79, 210, -30, 77, -124, -5, 9, -136, -18, -178, -180, 158, 128,
  138, 60, -90, -34, -179, -33, 82, 206, 95, 72, -238, -26, -113, -139, 181,
  53, 90, 62, -24, 31, 5, 43, -73, 32, 49, 18, 26, -43, -16, 44, 69, 189,
  91, -115, -67, 95, 65, -109, -88, 62, 53, -67, 35, 19, 82, 76, 84, -43,
  43, 90, -16, 119, 51, 25, -35, 69, 113, 38, 4, -67, -57, 102, -24, -47,
  67, -112, 49, -44, -86, -23, -30, 45, -1, -56, 44, 29, 65, -92, -70, 41,
  -74, -96, -91, -185, -67, 3, 80, -42, -5, 117, -44, 69, 55, 36, 47, -43,
  -22, -13, 56, -2, -19, -26, -3, -17, 144, -3, 113, 122, 47, -64, 80, 79,
  57, 6, -71, 6, 58, -5, 98, -55, -21, -87, 12, -41, 131, -200, -49, 61,
  -11, -45, 15, 86, -59, -11, 89, 155, 36, 127]

theorem fractionalNearFrameSubtreeG2R0098_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0098Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0098Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0098Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0098_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0098LowerBoundTable : List ℤ :=
  [-54, 42, 159, 22, 2, 131, 2, 118, -32, 118, 148, 284, 159, 325, 89, -20,
  123, 148, 11, 159, 10, -174, -39, 36, 843]

def fractionalNearFrameSubtreeG2R0098LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0098Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0098LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
