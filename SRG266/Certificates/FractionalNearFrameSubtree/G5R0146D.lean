import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0146`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0146Mask : ℕ := 7972872726187096

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0146Witness : Array ℤ :=
  #[-17, 39, -52, 49, -61, 55, 40, -57, 61, 81, 65, -136, 2, -109, 0, 39,
  116, 90, 53, 35, 61, -19, -22, -86, -136, 22, -16, 154, 131, 43, 72, -22,
  46, 139, -244, -11, 215, 102, -115, -66, -207, 16, 177, 150, -2, 75, 138,
  -15, 149, -134, -55, 116, 99, 103, -272, -109, 83, 31, -53, -14, 4, 85,
  52, -54, 41, -28, -51, 106, -18, -108, 45, -126, -22, 95, 127, -39, 85,
  -10, -57, 46, 66, -48, 49, 91, -120, 22, -61, -44, -11, -63, -116, -47,
  54, 55, -11, 74, 71, -151, 59, -85, 37, -199, -107, 95, -30, 89, 71, 67,
  -44, -84, -75, 117, -71, -3, 100, 77, 124, -17, 75, -53, -42, 149, -82,
  -76, 78, 126, 61, -105, -59, -89, 142, 3, -53, 96, 0, -129, -9, 81, -42,
  79, 29, 77, 32, -25, 59, -266, -165, -98, -29, 51, 68, -80, -23, 27, -30,
  0, 105, 65, -59, -60, 0, 56, -47, 29, 133, -62, 63, 64]

theorem fractionalNearFrameSubtreeG5R0146_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0146Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0146Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0146Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0146_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0146LowerBoundTable : List ℤ :=
  [-58, 36, 199, -129, 228, 150, 37, -269, 42, 278, 10, 15, 220, 238, 327,
  -139, 29, 10, -23, -119, 440, 257, 248, 454, 221]

def fractionalNearFrameSubtreeG5R0146LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0146Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0146LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
