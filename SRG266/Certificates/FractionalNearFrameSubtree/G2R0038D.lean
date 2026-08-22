import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0038`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0038Mask : ℕ := 887773635398673

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0038Witness : Array ℤ :=
  #[-70, 14, -47, -63, 72, -16, 3, 59, -8, -34, 16, -19, 12, -7, 36, -41,
  -12, 0, -28, -52, 25, -34, -17, 7, 27, 36, -2, 14, 14, -25, -25, 36, -37,
  -2, 19, 54, 16, -35, -14, -6, 7, 13, 30, -15, 40, 31, -45, -32, -32, 12,
  54, 37, -7, -31, 39, 53, 53, -80, 18, 38, 97, -2, -27, -26, -19, 1, -30,
  -35, -11, -73, -4, -6, 12, -7, 23, 49, -13, 28, 26, -30, 29, 48, -81, 56,
  3, -17, 47, -9, -58, -105, -57, -98, 44, 17, 23, -19, -25, -18, -16, -20,
  25, -14, 15, 55, 37, 49, 1, -27, 9, -7, 9, 10, -12, -29, 12, 8, -19, 39,
  26, 1, -20, -3, 21, 30, 10, -35, -49, -4, -68, -8, -11, 32, 48, -16, 40,
  13, 23, -45, 65, -19, 8, 48, 11, 31, 15, 10, 33, 25, 11, -12, 64, 80, 25,
  -16, -70, -3, -24, -10, -23, -22, 19, -59, 41, -6, 45, 50, 14, -84]

theorem fractionalNearFrameSubtreeG2R0038_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0038Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0038Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0038Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0038_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0038LowerBoundTable : List ℤ :=
  [-18, 49, 54, -17, -56, 38, -15, -16, -42, 56, 76, -69, 68, 120, 66, -9,
  73, 99, 9, 91, 7, 99, 10, 10, -11]

def fractionalNearFrameSubtreeG2R0038LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0038Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0038LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
