import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0332`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0332Mask : ℕ := 5638204058937865

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0332Witness : Array ℤ :=
  #[46, 0, 38, -53, -98, -130, 0, 17, 17, 11, 23, -64, 69, 81, 51, 38, 98,
  -27, 25, 73, 17, 50, 18, -15, 80, 43, -37, -39, 33, 45, -64, 62, 133, 95,
  1, -24, -80, 11, -43, -149, 54, -5, 64, -54, 193, -107, 72, -51, -64, 107,
  -108, 23, -74, -41, 50, 32, -186, -54, 74, 1, -72, 67, 48, -3, 0, -67,
  -122, -17, -19, -7, -19, 19, 82, 3, -41, 85, 14, -66, 68, 30, -120, -71,
  45, 32, 152, 70, -12, -3, 20, -21, 36, 7, 52, 34, 23, 70, 70, 36, 92, 18,
  166, -152, -14, 93, 25, -52, -14, 104, -24, 35, 184, 44, 67, -53, 65, 57,
  57, 92, -10, 167, 0, 23, -73, 4, -52, -53, -11, 48, -15, -154, -118, 16,
  18, 0, -13, -55, -74, -7, -5, -49, 58, -96, -15, 25, 46, -55, 64, -88, 56,
  -71, 49, -73, 87, 129, 29, -53, -64, -14, -9, -7, 59, -80, -45, 17, 16,
  32, 0, -90]

theorem fractionalNearFrameSubtreeG2R0332_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0332Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0332Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0332Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0332_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0332LowerBoundTable : List ℤ :=
  [-41, -76, 54, 103, 117, -25, 28, 2, 116, 510, 9, 385, -187, 615, 134,
  -233, 176, 414, 19, 33, 11, 9, 385, -245, 250]

def fractionalNearFrameSubtreeG2R0332LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0332Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0332LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
