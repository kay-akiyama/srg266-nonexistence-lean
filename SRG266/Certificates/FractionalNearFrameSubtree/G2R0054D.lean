import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0054`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0054Mask : ℕ := 936563409650762

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0054Witness : Array ℤ :=
  #[78, 14, 16, -57, 93, 17, -166, -79, -84, -40, -97, 6, 45, 86, 107, 122,
  12, -13, -7, -99, -117, 94, 71, 25, 55, 24, -25, -52, -18, -40, -27, -10,
  -81, 44, 0, -16, 28, 29, -20, -79, 3, 144, 17, 24, 44, -4, 11, 33, -107,
  -79, 45, 48, -3, -30, -127, -75, 53, -98, 130, -22, 43, -23, 35, -14, 0,
  -62, 32, -23, 83, 35, 54, -29, -31, -59, -20, 66, -20, 81, -26, 39, 36,
  -44, 103, -55, 25, 3, -58, -14, -77, -16, 14, 68, 19, -84, -60, 33, 11,
  94, -99, 19, 72, 107, -121, 51, 26, 30, -64, 29, -11, -13, -35, 101, 64,
  -29, 28, 18, 11, -3, 49, 45, -7, -7, 20, -5, 12, -23, 0, 17, -3, -1, -96,
  38, 50, 29, -38, 87, -49, -10, -56, -20, 37, 6, -49, -34, 3, 20, 23, -51,
  9, -8, 29, 97, -13, 55, -119, -30, 29, 25, -80, 86, 35, -22, -21, -33, 21,
  -102, -32, 54]

theorem fractionalNearFrameSubtreeG2R0054_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0054Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0054Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0054Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0054_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0054LowerBoundTable : List ℤ :=
  [-43, 0, -32, 1, 1, 0, 1, 82, 77, 49, -49, -246, 58, 8, 165, 95, 10, 16,
  69, -99, -106, 8, 316, 36, 68]

def fractionalNearFrameSubtreeG2R0054LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0054Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0054LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
