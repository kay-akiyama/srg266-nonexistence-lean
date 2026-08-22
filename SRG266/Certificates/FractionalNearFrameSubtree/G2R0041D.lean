import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0041`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0041Mask : ℕ := 888048244869665

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0041Witness : Array ℤ :=
  #[0, 59, -28, 21, 119, 29, 16, 0, -18, -11, -22, 0, -65, -1, -76, -55, -2,
  -11, -48, -48, -46, -23, 14, 61, 43, 31, 3, -6, 15, -22, 23, 107, -24, 25,
  -48, -23, -21, 37, 7, 27, -29, 41, 7, 9, 33, 53, -18, -44, -65, -65, 47,
  21, -7, 29, 13, 41, 106, -125, -11, 11, 84, -7, -45, -29, -22, -7, 2, 30,
  -4, -126, -7, 6, 20, 17, 5, 10, 17, 37, 27, 38, -34, 23, -53, -33, -5,
  -32, 32, 57, 48, 24, 16, 26, -3, -58, -49, -106, -149, -21, -22, 23, -16,
  -10, 1, -2, 12, 47, 22, -9, -23, 2, -12, 6, -8, -13, 43, 0, -88, 30, 8,
  -19, 6, -39, -12, -14, 13, -32, -4, -18, -29, 8, -21, 23, 31, -1, 72, 1,
  -8, -19, -11, -45, 84, 12, -35, 25, 3, 32, 28, 100, -28, 13, -24, 16, 90,
  -19, -23, 16, 26, 4, 13, -63, 30, 12, 43, 10, 8, 50, -16, -155]

theorem fractionalNearFrameSubtreeG2R0041_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0041Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0041Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0041Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0041_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0041LowerBoundTable : List ℤ :=
  [-43, 89, -121, 68, -45, 19, 31, 2, -69, 179, -65, 30, 18, -230, 59, 86,
  -111, 100, 112, 10, 91, -102, 11, 92, -29]

def fractionalNearFrameSubtreeG2R0041LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0041Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0041LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
