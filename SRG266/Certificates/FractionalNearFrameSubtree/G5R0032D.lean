import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0032`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0032Mask : ℕ := 1382737109557507

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0032Witness : Array ℤ :=
  #[205, 2, 37, -62, -22, 75, 70, -5, -62, 17, -69, 29, -43, 34, 65, 6, 15,
  -66, 59, -114, -32, 112, 108, 101, 33, 156, 0, -136, -2, -92, 4, -107, -8,
  21, -59, 23, 0, 21, 101, 53, 61, -52, -115, -30, 66, 42, -6, -22, 97, -16,
  -63, -101, -63, 21, 18, -59, -123, 40, -1, 59, -27, 56, 48, 11, -62, 114,
  31, 17, 7, -70, 93, -40, -20, -39, 114, -33, 14, 84, 86, 53, 112, 67, 165,
  -23, 65, -45, 49, -8, 4, 145, -19, 0, 45, 1, 5, -57, -1, -57, -11, 35,
  -50, 21, -87, -4, -21, 0, -55, 7, -1, -13, -32, 40, -10, 58, 72, 123, 17,
  -22, -31, -81, 31, -71, -132, -30, 110, 86, -117, -120, -10, 75, -61, 10,
  -8, 37, 36, 21, 20, 64, 42, 97, -58, 11, -76, -58, -123, -22, 13, 16, 106,
  -25, 45, -18, 1, -10, -57, -26, -111, 31, 70, 0, -146, 155, -83, 29, 0,
  57, -22, -21]

theorem fractionalNearFrameSubtreeG5R0032_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0032Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0032Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0032Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0032_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0032LowerBoundTable : List ℤ :=
  [33, -24, 16, 23, 93, 14, 112, 125, 47, -76, 95, 168, -134, 103, 180, 304,
  10, 31, 10, -149, 10, 201, 313, -123, 410]

def fractionalNearFrameSubtreeG5R0032LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0032Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0032LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
