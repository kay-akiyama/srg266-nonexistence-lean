import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0053`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0053Mask : ℕ := 4949367592918021

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0053Witness : Array ℤ :=
  #[38, 83, 88, 38, 35, 37, 112, 58, 83, 9, 101, -217, -97, -59, -34, -89,
  -94, -136, -217, -172, -163, -19, 41, -40, -75, -78, -33, 209, 267, 196,
  228, 189, 73, 128, 80, 79, -11, 3, -38, 24, -40, -30, 31, 45, -13, -41,
  -40, -27, -5, -51, 19, -123, 17, 56, 62, 67, -15, 7, 104, 14, 32, 23, 0,
  -102, 24, -130, -77, 72, -14, -71, -13, 97, -13, -161, 53, 117, 31, 28,
  -23, 17, -6, 112, -34, -8, 110, 67, 19, 39, 8, 20, 58, 32, 65, -11, -2,
  28, 24, 24, -10, 7, 56, 28, 24, 45, 49, 56, 22, -11, -2, -19, -2, 32, 19,
  17, 0, -55, 23, 13, -63, 37, 32, 6, 41, 73, 68, 15, 32, -53, 14, -13, 32,
  -14, -15, 7, -18, 2, 156, -102, 96, -79, -88, 123, -39, 24, 42, -42, 7,
  22, 8, -13, 26, 45, -99, -17, -92, 17, 43, -3, -14, -69, 30, -64, -46,
  -33, -62, 21, -31, -23]

theorem fractionalNearFrameSubtreeG5R0053_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0053Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0053Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0053Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0053_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0053LowerBoundTable : List ℤ :=
  [48, -52, 100, -84, 232, 156, 213, 2, 103, 171, 105, -17, 134, 247, 127,
  49, 481, 4, -86, 10, 161, 140, 114, 93, 275]

def fractionalNearFrameSubtreeG5R0053LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0053Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0053LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
