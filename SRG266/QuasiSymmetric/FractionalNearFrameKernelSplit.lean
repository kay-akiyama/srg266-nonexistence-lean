/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.FractionalNearFrameSplitAudit

/-!
# Discharging the residual Farkas stratum semantically

The Farkas stratum is stated as the proposition that every listed entry carrying
a Farkas certificate is impossible. The bridge from entries to masks inspects
only the certificate constructor and mask.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.QuasiSymmetric

/-- The residual Farkas stratum, stated semantically. -/
def FractionalNearFrameKernelFarkasRuleOn
    (entries : List FractionalNearFrameCertificateEntry) : Prop :=
  ∀ entry ∈ entries, ∀ witness, entry.certificate = .farkas witness →
    NoCompactFractionalNearFrame entry.nearMask

/-- Boolean bridge: every Farkas entry's mask occurs in a listed family. -/
def fractionalNearFrameFarkasMasksCovered
    (entries : List FractionalNearFrameCertificateEntry) (masks : List ℕ) : Bool :=
  entries.all fun entry =>
    match entry.certificate with
    | .emptyShell => true
    | .farkas _ => masks.contains entry.nearMask

/-- A family of per-representative obstructions covering every Farkas mask
discharges the whole stratum. -/
theorem fractionalNearFrameKernelFarkasRuleOn_of_masks
    (entries : List FractionalNearFrameCertificateEntry) (masks : List ℕ)
    (hcover : fractionalNearFrameFarkasMasksCovered entries masks = true)
    (hmasks : ∀ mask ∈ masks, NoCompactFractionalNearFrame mask) :
    FractionalNearFrameKernelFarkasRuleOn entries := by
  intro entry hentry witness hcertificate
  rw [fractionalNearFrameFarkasMasksCovered, List.all_eq_true] at hcover
  have hentryCover := hcover entry hentry
  rw [hcertificate] at hentryCover
  exact hmasks entry.nearMask (List.mem_of_elem_eq_true hentryCover)

/-- Dispatch the empty stratum through the Hall rule and the Farkas stratum
through per-representative proofs. -/
theorem noCompactFractionalNearFrame_of_mem_kernel_split
    (entries : List FractionalNearFrameCertificateEntry)
    (hempty : FractionalNearFrameMinedEmptyRuleOn entries)
    (hfarkas : FractionalNearFrameKernelFarkasRuleOn entries)
    {entry : FractionalNearFrameCertificateEntry} (hentry : entry ∈ entries) :
    NoCompactFractionalNearFrame entry.nearMask := by
  cases hcertificate : entry.certificate with
  | emptyShell =>
      have hcheck := hempty entry hentry
      rw [checkFractionalNearFrameMinedEmptyRuleEntry, hcertificate,
        Bool.or_eq_true] at hcheck
      rcases hcheck with hprimary | hexceptional
      · exact noCompactFractionalNearFrame_of_hasHallDeficientEndpointShell
          entry.nearMask hprimary
      · exact
          noCompactFractionalNearFrame_of_hasExceptionalHallDeficientEndpointShell
            entry.nearMask hexceptional
  | farkas witness => exact hfarkas entry hentry witness hcertificate

end SRG266.QuasiSymmetric
