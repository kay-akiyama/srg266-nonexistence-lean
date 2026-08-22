import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0091`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0091Mask : ℕ := 2511522412205202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0091Witness : Array ℤ :=
  #[47, 128, 38, 94, 89, 138, -130, -123, -107, 3, -43, 37, 55, -13, -59,
  116, 27, 42, 43, -15, 21, 76, 102, -132, -30, -40, 24, 18, 19, 0, 37, -45,
  109, 59, -13, 10, -40, 56, -57, -5, -79, 77, 30, -40, -15, 120, 32, -55,
  -68, -19, 41, 19, -27, -23, 39, 102, -63, 7, 46, -10, 90, -24, 85, -97,
  35, 54, 19, -12, 52, -39, 25, 4, 74, 81, 18, 33, 17, -27, 28, -50, -3, 19,
  104, -96, -44, 77, -11, 85, -102, -61, 50, 23, 35, 41, 7, 14, -8, -17,
  -69, -80, -95, -112, -30, 57, 3, 82, 81, 26, -57, -56, -20, -132, -23, 5,
  -82, -28, -86, 15, -5, 83, 58, 31, 6, 48, 39, -12, -47, -118, 6, -84, -30,
  128, 73, 103, 106, 88, -17, -42, 21, 33, -14, 16, -18, 2, 10, -43, 109,
  -40, 39, -50, 100, -53, -50, -19, 69, 2, -40, -138, -59, 90, -53, 0, -131,
  56, -10, -132, 64, 101]

theorem fractionalNearFrameSubtreeG3R0091_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0091Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0091Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0091Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0091_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0091LowerBoundTable : List ℤ :=
  [-43, -5, -70, 111, -81, 72, 40, 164, -3, -163, -94, 228, 78, 414, 243,
  85, 11, 10, 185, 256, 54, 9, 10, 398, 352]

def fractionalNearFrameSubtreeG3R0091LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0091Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0091LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
