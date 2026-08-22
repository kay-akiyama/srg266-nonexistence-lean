import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0118`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0118Mask : ℕ := 969511041313192

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0118Witness : Array ℤ :=
  #[96, 107, 25, 89, -113, 23, -105, 113, 47, 120, 1, 69, 36, 3, 30, -22,
  88, 69, 53, 176, 24, 31, 182, 214, -37, -52, -116, -145, -74, 3, -82, 182,
  99, -9, -134, -63, 6, 23, 125, 211, -121, 35, 83, -45, 89, -137, 52, -100,
  118, 189, -52, -43, 40, 176, 198, 110, 4, -166, 159, 33, 10, -52, 39, -61,
  98, -111, -96, -125, 254, 162, 142, -82, 201, -61, 97, 3, 84, 145, 29,
  -88, -78, 64, 40, -51, -110, 61, 25, 10, 114, 194, 73, 67, -43, 36, -3,
  35, -21, 207, -70, 117, 171, 68, -56, 151, -29, 116, 230, -22, 7, 12, 48,
  89, 235, 251, -112, -184, -215, -168, -200, -110, 136, -40, -53, 219, 29,
  0, 95, 117, -77, -146, 223, 1, 116, 72, 68, -109, 33, -141, -37, 115, 102,
  109, -5, -18, 115, -15, -120, -55, -88, -77, -153, 81, 33, -43, 152, 67,
  -42, 112, -28, 168, 74, 42, 21, 20, -21, 59, 70, -142]

theorem fractionalNearFrameSubtreeG1R0118_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0118Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0118Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0118Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0118_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0118LowerBoundTable : List ℤ :=
  [250, 105, 296, 509, 271, 206, 193, 433, 244, 11, 62, 352, 28, 309, 385,
  276, 427, 676, 642, 782, 426, 185, 389, 159, 1056]

def fractionalNearFrameSubtreeG1R0118LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0118Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0118LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
