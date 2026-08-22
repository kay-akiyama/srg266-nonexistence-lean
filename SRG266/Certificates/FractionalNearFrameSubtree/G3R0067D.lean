import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0067Mask : ℕ := 1034762466202708

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0067Witness : Array ℤ :=
  #[22, -16, -5, -15, 14, -9, 25, -22, -124, -74, -41, 26, 231, -35, -5,
  -16, -32, -18, -76, 85, -12, 35, -5, -15, 164, 26, -139, 44, -55, -14, 31,
  -65, 61, 46, 37, 10, -7, -92, 79, 87, 45, 24, 0, -152, 15, -66, -82, 35,
  57, 84, -57, 49, 22, -174, 74, 33, -81, 6, -11, -54, 1, 10, 80, -20, 19,
  111, -12, 24, -18, 15, -56, -148, 58, -52, -36, 152, -58, 44, 65, 72, -5,
  143, -46, -84, 61, 1, 60, -57, -5, -54, 7, -57, -53, 37, -56, -39, 92, 79,
  -56, -44, -80, -90, 16, -111, 38, 5, -21, -40, -89, 111, 98, 32, 38, 21,
  -152, -59, -83, -40, -56, 14, -17, 93, -34, -96, -10, 62, -45, -45, 133,
  43, 12, 35, 109, 104, 34, -77, -6, -68, -141, 13, -59, 0, 148, -35, -61,
  40, -59, -15, 133, 11, -166, -1, -7, -4, 76, 9, -93, -197, 124, 153, 12,
  126, -63, -157, -36, 44, 68, -45]

theorem fractionalNearFrameSubtreeG3R0067_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0067Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0067Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0067Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0067_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0067LowerBoundTable : List ℤ :=
  [-81, -57, -22, -41, -122, -67, 87, -57, 34, 166, 115, 62, -164, -163, 25,
  1, 9, 126, -158, -311, 198, -48, 131, 196, 19]

def fractionalNearFrameSubtreeG3R0067LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0067Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0067LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
