import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0437`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0437Mask : ℕ := 5785411363394712

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0437Witness : Array ℤ :=
  #[48, -62, -105, -40, -103, 56, 173, 41, -61, -59, 110, 158, -2, 189, -9,
  35, 92, -41, -12, 88, 213, 116, -24, -11, -49, -91, -25, 126, -93, 111,
  -59, -63, -30, -22, 6, 40, 11, -64, 49, 68, 48, 65, 162, -64, -127, 2, 12,
  -142, 77, 9, -116, -24, -9, -35, 70, -49, 1, -53, 115, -55, 23, 47, -1,
  67, 135, -58, -60, -88, 56, -100, -212, 12, 67, 204, -17, -65, 3, -33, -5,
  -45, 163, -103, 46, -105, 125, 39, 50, -18, -99, -74, -94, -54, 224, -1,
  73, -50, -4, -145, 108, 121, 50, -24, 121, 72, 35, 33, -72, 57, 0, 128,
  116, -35, 87, -66, 104, 73, 38, 142, 102, 201, -141, 8, -62, 43, -115,
  111, -66, 231, -109, 0, 95, 189, -110, 20, 27, -11, -14, 140, -17, 97, -8,
  -55, 198, -110, 101, -25, -175, 159, 112, 71, 45, 65, 168, 35, -78, -72,
  10, -9, -106, -35, -49, 56, 81, -73, 0, 65, -52, -191]

theorem fractionalNearFrameSubtreeG2R0437_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0437Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0437Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0437Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0437_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0437LowerBoundTable : List ℤ :=
  [4, 206, 49, 183, 3, 34, 247, -13, 113, 750, 384, 140, 391, -171, 789, 76,
  9, 170, 596, -91, 744, -180, 921, -181, 394]

def fractionalNearFrameSubtreeG2R0437LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0437Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0437LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
