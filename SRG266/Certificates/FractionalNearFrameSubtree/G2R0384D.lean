import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0384`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0384Mask : ℕ := 5739200258645144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0384Witness : Array ℤ :=
  #[137, 108, 116, 71, -17, -11, 14, 26, -12, -51, -7, -82, -80, -88, 68,
  99, 68, -53, 32, -63, -25, -41, -50, -84, 41, 13, 108, 45, 51, 60, -20,
  -56, 98, 52, 45, -99, -81, 8, -11, 9, -6, 15, 89, -53, 102, -40, 85, 90,
  -72, -48, -12, -5, 97, 20, 10, -16, -92, 59, -25, -63, -192, 91, 28, -3,
  83, 35, 0, 68, -45, 44, 57, -30, 37, 20, 9, -23, 101, -20, 2, 65, -3, 85,
  13, -43, -31, -30, 85, -13, -73, -53, -1, -20, -14, -33, 85, 11, 21, 48,
  -29, 40, 32, 29, 96, 55, 68, 46, 74, -64, -99, -37, -58, -37, 27, 101,
  117, -62, -2, -18, 0, -28, 72, 27, 102, -84, -38, -69, -25, -36, -50, -44,
  -10, 62, 55, -14, 31, 53, -79, 87, -76, 16, 60, 16, 29, 93, 57, 41, -18,
  34, 36, -19, 122, 59, 9, -15, -30, -122, 27, 50, 9, -17, 36, -43, 4, -46,
  -12, -33, 57, -6]

theorem fractionalNearFrameSubtreeG2R0384_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0384Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0384Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0384Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0384_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0384LowerBoundTable : List ℤ :=
  [36, 25, 95, 112, 280, 169, -79, 126, 25, 9, 270, 197, -132, 401, 58, 22,
  10, 143, 9, 125, 152, 413, 215, -9, 292]

def fractionalNearFrameSubtreeG2R0384LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0384Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0384LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
