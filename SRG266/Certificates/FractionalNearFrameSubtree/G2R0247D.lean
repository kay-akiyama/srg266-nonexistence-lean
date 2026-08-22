import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0247`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0247Mask : ℕ := 5177418417029522

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0247Witness : Array ℤ :=
  #[10, 27, 66, 73, 22, -86, -40, -103, -61, -20, -32, 47, -60, 94, 86, 37,
  51, 48, -34, 8, 11, 64, -5, -44, -10, 17, -41, -53, -57, 27, -50, -48,
  -39, 25, 48, 80, 122, -15, -51, -20, 35, 42, 8, 52, 31, 68, -11, -47, 0,
  -34, 40, 100, 80, -107, -147, -70, -47, -8, -23, 52, 102, -26, -68, 110,
  57, -17, 0, -56, 22, 49, 8, 76, 8, -31, -75, -26, 17, 2, -40, -6, 80, -75,
  -75, 29, 31, 11, 44, -28, -22, -83, 40, 70, -27, -26, 18, 74, -71, 18,
  -88, 14, 100, -60, 64, 59, 103, 67, -8, 29, 15, -31, 22, 35, 49, -116,
  -118, -115, -55, -49, -1, -44, 6, 57, 23, 5, -13, -43, -56, -17, -67, 20,
  16, -19, 71, -5, 41, 19, 34, 56, -65, 73, 103, -79, -25, 15, 11, 99, -36,
  -58, 72, -66, -23, 87, 67, -86, -115, -56, 12, 27, -12, 47, -4, 85, 69,
  133, 5, -73, 20, 5]

theorem fractionalNearFrameSubtreeG2R0247_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0247Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0247Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0247Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0247_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0247LowerBoundTable : List ℤ :=
  [-65, -48, 62, -66, 77, -18, 9, 152, 2, 9, 270, 44, -90, 89, 218, 86, -80,
  -104, -61, 259, 87, 244, 144, 18, 132]

def fractionalNearFrameSubtreeG2R0247LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0247Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0247LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
