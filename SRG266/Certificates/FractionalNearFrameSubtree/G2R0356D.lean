import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0356`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0356Mask : ℕ := 5671120662147617

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0356Witness : Array ℤ :=
  #[-4, 149, 107, 43, -25, 0, -287, -65, -112, -74, 0, -69, 63, 42, -44,
  108, 42, 135, -90, -89, 82, 18, -9, -29, -151, -50, 37, 24, 17, -7, 16,
  175, -86, -70, -83, -159, -29, 108, 162, 277, 72, -49, -104, -43, 314,
  -90, -50, 129, 56, -33, 114, -4, -15, 15, 40, 102, 131, 134, 86, 28, -18,
  7, -314, -192, -88, 17, 142, -30, 79, -191, 74, 59, 48, 122, 121, -98,
  -63, -53, -48, 1, -53, 74, -56, 135, 59, 36, 235, 24, -8, 139, 86, -29,
  67, 34, -5, 34, 37, 9, 27, 91, 51, 35, 93, -56, 0, -8, 102, 0, 20, 4,
  -132, 128, -130, -133, -4, -29, -25, 165, -115, -157, 83, 57, 176, 49,
  141, 11, -52, -133, 1, 14, -19, 71, -7, -8, -7, -43, -20, -3, -28, 59,
  -120, 177, 151, -81, -81, 57, -24, -35, -18, 30, 26, -4, 25, 67, -38, -43,
  -84, 35, 7, -55, -167, 29, -133, -83, 2, -111, -64, -81]

theorem fractionalNearFrameSubtreeG2R0356_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0356Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0356Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0356Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0356_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0356LowerBoundTable : List ℤ :=
  [-41, -149, 31, 1, 305, -61, 13, -6, 183, -561, -25, 138, -37, 11, 542,
  -57, 117, 311, 64, 241, 10, 524, 714, 241, 12]

def fractionalNearFrameSubtreeG2R0356LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0356Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0356LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
