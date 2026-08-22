/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentEnumerationCore
import SRG266.Hosts.E7CentroidRealization

/-!
# Lightweight data for the mined E7 branch payload

This module contains only the payload predicates and structure.  Keeping the
data separate lets the lattice construction avoid importing the downstream
Weyl and residual-elimination proofs that consume the payload.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Data from which the signed-magnitude completeness theorem reconstructs
enumerator membership. -/
structure E7ComponentEnumerationWitness (profile : Array ℤ) where
  parity : ℕ
  source : List ℤ
  canonical : List ℤ
  parity_cases : parity = 0 ∨ parity = 1
  source_length : source.length = 8
  source_bounds : ∀ z ∈ source, -17 ≤ z ∧ z ≤ 17
  source_sum : source.sum = e7ComponentTargetSum parity
  source_sq :
    (source.map (fun z : ℤ => z * z)).sum ≤ e7ComponentTargetSq parity
  source_special : parity = 1 → source.count 17 = 0
  canonical_perm : canonical.Perm source
  canonical_sorted : canonical.Pairwise (· ≤ ·)
  profile_eq : profile = e7ScaleReducedProfile parity canonical

/-- The divisibility and component-norm information retained by the mined
profile reduction. -/
def IsE7MinedComponentProfile (profile : Array ℤ) : Prop :=
  (∀ i, (5 : ℤ) ∣ e7ComponentEnumerationProfile profile i) ∧
  ∃ n : ℤ,
    (n = 50 ∨ n = 100 ∨ n = 150 ∨ n = 200 ∨ n = 250) ∧
    ∑ i, (e7ComponentEnumerationProfile profile i) ^ 2 = 4 * n

/-- The structural data needed by the mined direct contradiction. Enumeration
witnesses let the aggregate Kneser boundary reconstruct the audited-host case. -/
structure E7BranchPayload (x : V) where
  /-- The enumerated component profile of the first `E₇` factor. -/
  left : Array ℤ
  /-- The enumerated component profile of the second `E₇` factor. -/
  right : Array ℤ
  /-- Data reconstructing first-profile enumerator membership when needed. -/
  left_enumeration : E7ComponentEnumerationWitness left
  /-- Data reconstructing second-profile enumerator membership when needed. -/
  right_enumeration : E7ComponentEnumerationWitness right
  /-- The first profile satisfies the mined divisibility and small-norm cases. -/
  left_mined : IsE7MinedComponentProfile left
  /-- The second profile satisfies the mined divisibility and small-norm cases. -/
  right_mined : IsE7MinedComponentProfile right
  /-- The first component has zero coordinate sum. -/
  left_sum : ∑ i, e7ComponentEnumerationProfile left i = 0
  /-- The second component has zero coordinate sum. -/
  right_sum : ∑ i, e7ComponentEnumerationProfile right i = 0
  /-- The first component has common coordinate parity. -/
  left_parity : ∀ i j,
    e7ComponentEnumerationProfile left i % 2 =
      e7ComponentEnumerationProfile left j % 2
  /-- The second component has common coordinate parity. -/
  right_parity : ∀ i j,
    e7ComponentEnumerationProfile right i % 2 =
      e7ComponentEnumerationProfile right j % 2
  /-- The first enumerated profile is stored in canonical nondecreasing order. -/
  left_sorted :
    (List.ofFn (e7ComponentEnumerationProfile left)).Pairwise (· ≤ ·)
  /-- The second enumerated profile is stored in canonical nondecreasing order. -/
  right_sorted :
    (List.ofFn (e7ComponentEnumerationProfile right)).Pairwise (· ≤ ·)
  /-- The realization in the paired minuscule shell. -/
  realization :
    E7CentroidShellGramRealization G x
      (e7ComponentEnumerationProfile left) (e7ComponentEnumerationProfile right)

end Lattice
end SRG266
