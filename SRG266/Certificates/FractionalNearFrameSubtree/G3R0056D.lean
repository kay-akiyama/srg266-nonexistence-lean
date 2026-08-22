import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0056`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0056Mask : ℕ := 964875362345192

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0056Witness : Array ℤ :=
  #[475, -23, -634, -712, 10, 221, 158, 292, 213, 562, 18, -252, -39, 127,
  199, -343, -678, -251, -1022, 206, 396, 33, 25, -152, 306, 340, 816, 112,
  612, 54, -227, 233, -395, 505, 23, -575, -13, -449, -654, 344, 223, -430,
  -599, -460, 192, 326, 6, 793, 375, -176, -134, -650, 204, 671, 24, -368,
  268, 15, 90, -360, 169, 521, 709, 0, 1027, 450, 326, 166, 273, -180, 52,
  -287, -560, -97, 487, 102, -324, -19, 64, 597, 248, 152, -171, 371, 472,
  778, 481, 11, 208, -109, -352, 374, 57, 497, -275, -23, 525, -627, -277,
  -72, -30, 282, -744, -87, 644, 338, 220, -223, -21, 186, 323, -1399, 189,
  -563, -268, 416, 227, 93, -364, -143, 179, -205, -257, -621, -164, 748,
  -478, -598, 391, 613, -27, 413, -2, -387, 668, 293, -846, -422, -382, 159,
  100, -2, -126, -48, -238, -57, 144, -254, -699, 542, -784, -762, 210,
  -1335, 493, -635, 196, 18, 0, -1018, 417, 10, 823, -254, -272, 948, 241,
  -480]

theorem fractionalNearFrameSubtreeG3R0056_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0056Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0056Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0056Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0056_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0056LowerBoundTable : List ℤ :=
  [-764, -960, 710, 33, -721, 32, -27, 31, 469, 525, 554, -812, 350, 345,
  3212, -182, 99, 914, 101, 100, 108, 1672, -476, -75, 2548]

def fractionalNearFrameSubtreeG3R0056LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0056Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0056LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
