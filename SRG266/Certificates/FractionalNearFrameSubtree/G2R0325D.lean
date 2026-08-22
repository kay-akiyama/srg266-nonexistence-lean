import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0325`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0325Mask : ℕ := 5390514412624560

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0325Witness : Array ℤ :=
  #[13, 111, -60, 24, 4, 6, -11, -18, 5, -42, 5, 44, 17, 11, -1, 4, 67, -37,
  17, 9, -3, 15, -14, 51, -27, 56, 12, -121, -115, 3, -76, -90, -79, 39,
  125, -65, -63, -15, 64, 112, 147, -31, 42, 2, 3, 33, -26, -69, 71, 76,
  -35, -31, -7, 133, 48, -64, -49, -64, -101, -75, 36, -54, -31, -81, 48,
  11, -64, -44, 104, -63, -3, 154, 184, -42, 152, 75, -51, 12, -27, -2, 42,
  -33, 23, 1, 6, 8, 18, -28, -20, 46, 123, -2, 0, -23, -9, 68, 60, 29, 91,
  33, 52, 104, -87, 76, 55, 16, 59, -4, 33, -123, 57, 102, 38, 17, 9, -36,
  74, -40, -131, 72, 0, -37, 38, 36, -33, -6, 29, 68, 101, 7, -28, 2, -29,
  52, 53, 45, 44, 17, -49, -111, 34, -37, 91, 35, -32, -16, -10, 81, 40, -1,
  -142, 25, -33, 66, -90, 21, 167, 43, 56, 20, 18, 0, 66, -103, 15, -2, 187,
  19]

theorem fractionalNearFrameSubtreeG2R0325_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0325Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0325Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0325Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0325_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0325LowerBoundTable : List ℤ :=
  [133, 137, 180, 157, 40, 177, 82, -87, 68, 401, 224, -166, 260, 201, 258,
  158, 363, 84, 311, 10, 117, 411, 54, 149, 88]

def fractionalNearFrameSubtreeG2R0325LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0325Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0325LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
