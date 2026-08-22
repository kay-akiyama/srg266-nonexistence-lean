/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.FractionalNearFrameAudit

/-!
# Split audits for mined empty-shell rules

The certificate corpus has two proof strata. Payload-free `emptyShell` entries
use two Hall cut orbits, while Farkas entries use their exact indexed
right-hand-side check. This module separates those obligations.
-/

namespace SRG266.QuasiSymmetric

/-- Check only the theorem-mined empty-shell stratum.  Farkas entries are
accepted without inspecting their payload. -/
def checkFractionalNearFrameMinedEmptyRuleEntry
    (entry : FractionalNearFrameCertificateEntry) : Bool :=
  match entry.certificate with
  | .emptyShell =>
      compactHasHallDeficientEndpointShell entry.nearMask ||
        compactHasExceptionalHallDeficientEndpointShell entry.nearMask
  | .farkas _ => true

/-- Check only the residual Farkas stratum.  Empty-shell entries are accepted
without running any shell search. -/
def checkFractionalNearFrameFarkasOnlyEntry
    (entry : FractionalNearFrameCertificateEntry) : Bool :=
  match entry.certificate with
  | .emptyShell => true
  | .farkas witness =>
      decide (compactKernelIndexedCanonicalFarkasRhsDot
        entry.nearMask witness < 0)

/-- The two branch checks jointly imply the semantic obstruction for one
entry. -/
theorem noCompactFractionalNearFrame_of_split_entry_checks
    (entry : FractionalNearFrameCertificateEntry)
    (hempty : checkFractionalNearFrameMinedEmptyRuleEntry entry = true)
    (hfarkas : checkFractionalNearFrameFarkasOnlyEntry entry = true) :
    NoCompactFractionalNearFrame entry.nearMask := by
  cases hcertificate : entry.certificate with
  | emptyShell =>
      rw [checkFractionalNearFrameMinedEmptyRuleEntry, hcertificate,
        Bool.or_eq_true] at hempty
      rcases hempty with hprimary | hexceptional
      · exact noCompactFractionalNearFrame_of_hasHallDeficientEndpointShell
          entry.nearMask hprimary
      · exact
          noCompactFractionalNearFrame_of_hasExceptionalHallDeficientEndpointShell
            entry.nearMask hexceptional
  | farkas witness =>
      rw [checkFractionalNearFrameFarkasOnlyEntry, hcertificate,
        decide_eq_true_eq] at hfarkas
      exact noCompactFractionalNearFrame_of_indexedCanonicalPairFarkas
        entry.nearMask witness hfarkas

/-- Every entry in a bounded list satisfies the theorem-mined empty branch
check. -/
def FractionalNearFrameMinedEmptyRuleOn
    (entries : List FractionalNearFrameCertificateEntry) : Prop :=
  ∀ entry ∈ entries,
    checkFractionalNearFrameMinedEmptyRuleEntry entry = true

/-- Kernel reduction of a bounded Boolean range yields its pointwise rule. -/
theorem fractionalNearFrameMinedEmptyRuleOn_of_audit
    (entries : List FractionalNearFrameCertificateEntry)
    (haudit : entries.all checkFractionalNearFrameMinedEmptyRuleEntry = true) :
    FractionalNearFrameMinedEmptyRuleOn entries := by
  rw [List.all_eq_true] at haudit
  exact haudit

/-- Mined-empty range proofs compose across concatenation. -/
theorem fractionalNearFrameMinedEmptyRuleOn_append
    (left right : List FractionalNearFrameCertificateEntry) :
    FractionalNearFrameMinedEmptyRuleOn (left ++ right) ↔
      FractionalNearFrameMinedEmptyRuleOn left ∧
        FractionalNearFrameMinedEmptyRuleOn right := by
  constructor
  · intro hbound
    constructor
    · intro entry hentry
      exact hbound entry (List.mem_append_left right hentry)
    · intro entry hentry
      exact hbound entry (List.mem_append_right left hentry)
  · rintro ⟨hleft, hright⟩ entry hentry
    rcases List.mem_append.mp hentry with hentry | hentry
    · exact hleft entry hentry
    · exact hright entry hentry

/-- Join independently checked prefix and suffix ranges. -/
theorem fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    (entries : List FractionalNearFrameCertificateEntry) (cut : ℕ)
    (hleft : FractionalNearFrameMinedEmptyRuleOn (entries.take cut))
    (hright : FractionalNearFrameMinedEmptyRuleOn (entries.drop cut)) :
    FractionalNearFrameMinedEmptyRuleOn entries := by
  rw [← List.take_append_drop cut entries]
  exact (fractionalNearFrameMinedEmptyRuleOn_append _ _).mpr
    ⟨hleft, hright⟩

/-- Join two independently checked adjacent bounded ranges. -/
theorem fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    (entries : List FractionalNearFrameCertificateEntry)
    (start leftLength rightLength : ℕ)
    (hleft : FractionalNearFrameMinedEmptyRuleOn
      ((entries.drop start).take leftLength))
    (hright : FractionalNearFrameMinedEmptyRuleOn
      ((entries.drop (start + leftLength)).take rightLength)) :
    FractionalNearFrameMinedEmptyRuleOn
      ((entries.drop start).take (leftLength + rightLength)) := by
  rw [List.take_add]
  apply (fractionalNearFrameMinedEmptyRuleOn_append _ _).mpr
  exact ⟨hleft, by simpa [List.drop_drop] using hright⟩

/-- A mined-empty range audit and a Farkas-only aggregate audit prove every
listed entry directly. -/
theorem noCompactFractionalNearFrame_of_mem_split_audits
    (entries : List FractionalNearFrameCertificateEntry)
    (hempty : FractionalNearFrameMinedEmptyRuleOn entries)
    (hfarkas : entries.all checkFractionalNearFrameFarkasOnlyEntry = true)
    {entry : FractionalNearFrameCertificateEntry} (hentry : entry ∈ entries) :
    NoCompactFractionalNearFrame entry.nearMask := by
  apply noCompactFractionalNearFrame_of_split_entry_checks entry
  · exact hempty entry hentry
  · rw [List.all_eq_true] at hfarkas
    exact hfarkas entry hentry

end SRG266.QuasiSymmetric
