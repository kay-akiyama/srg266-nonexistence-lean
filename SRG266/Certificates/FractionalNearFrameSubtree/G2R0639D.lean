import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0639`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0639Mask : ℕ := 11349685864744458

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0639Witness : Array ℤ :=
  #[619, 503, 111, 308, 271, 287, -384, 207, 747, 338, 49, -587, 0, -38,
  -471, -220, 0, 521, 240, -729, -278, -782, -6, -311, 166, -430, 511, 1217,
  405, 881, 357, 467, 55, 186, -305, -567, 620, 618, -701, -387, 40, 381,
  249, 138, 26, 368, 24, -19, -432, -80, -168, -479, -264, 214, 456, -458,
  -234, 682, -120, -148, 164, 206, -99, -637, -192, -88, -840, -228, -194,
  -16, 39, -160, -225, 394, -517, -230, 174, 653, 136, 792, 679, -163, -1,
  -788, 209, 502, -222, 266, -295, -217, -141, -53, 226, 187, -773, -190,
  137, 159, 329, 295, 733, 68, 704, 50, 123, 225, 310, 633, 1081, 1340,
  -401, -622, 286, 51, -62, -296, -75, -277, -224, 178, 329, 598, -78, 251,
  101, -31, -79, 218, 386, -429, 191, 458, 76, -679, -73, 249, 795, -137,
  232, -23, -502, -272, 216, 790, 85, 128, -120, 129, 219, 430, -553, -151,
  122, 947, -552, -190, 45, -7, 0, 267, 366, -474, 703, -696, 47, -1176,
  -505, -616]

theorem fractionalNearFrameSubtreeG2R0639_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0639Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0639Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0639Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0639_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0639LowerBoundTable : List ℤ :=
  [11, -51, 2, 2, 412, 694, 951, 310, 589, -879, 2704, 614, 1972, 734, 1620,
  9, 964, -531, -786, 1122, 2640, 207, 425, 1883, 2164]

def fractionalNearFrameSubtreeG2R0639LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0639Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0639LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
