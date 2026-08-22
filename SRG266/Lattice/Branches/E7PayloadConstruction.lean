/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.E7PayloadProfiles
import SRG266.Lattice.Branches.E7Weight
import SRG266.Lattice.Hosts.E7E7PlusTrace

/-!
# The `(E₇ ⊕ E₇)⁺` branch

If the norm-one-free core of the host is `(E₇ ⊕ E₇)⁺` — so the host is
`(E₇ ⊕ E₇)⁺ ⊕ ℤ` and `k = 1` — a
pure embedding produces a structural payload that the mined profile chain
refutes directly.

The derivation is entirely arithmetic in the scaled coordinate model.

* **Glue parity.**  The centroid has even norm `300`, and a vector of the glue
  coset has odd norm, so `c ∈ E₇ ⊕ E₇`: both blocks of `4 c` have even residue
  (`SRG266.Lattice.e7e7Plus_even_block_of_even_norm`).  Halving gives the
  doubled coordinates `y = 2 c₁` the repository's enumerators use, with all
  eight coordinates of one parity `p` and sum zero.
* **Reduction.**  Writing `y = 2 a + p` turns `∑ y = 0` and `∑ y² = 4 ‖c₁‖²`
  into `∑ a = -4 p` and `∑ a² = ‖c₁‖² + 2 p²`, matching
  `SRG266.e7ComponentTargetSum` and `SRG266.e7ComponentTargetSq` on the nose;
  `|y_i| ≤ 34` gives `a_i ∈ [-17, 17]`, and at `p = 1` the value `17` is
  unreachable — the enumerator's special rule.
* **Trace bound.**  The projector bound at the eight lattice vectors
  `8 e_i - 1 ∈ A₇ ⊂ E₇` of one factor reads `20 ∑_B (w_B)_i² ≤ 12600 + 8 (2 c₁)_i²`;
  summing over `i` and using `‖w_B‖² = 3/2` gives `105600 ≤ 100800 + 128 ‖c₁‖²`,
  that is `‖c₁‖² ≥ 37.5`, that is **38** — and by symmetry `‖c₁‖² ≤ 262`.
The main results are `SRG266.Lattice.not_isHostCoreModel_e7e7Plus` and
`SRG266.Lattice.no_pure_e7e7PlusCore`, which close the branch through the
mined 25-profile/Weyl/residual route.  The constructor for
`SRG266.AuditedRank15HostCase` is isolated in
`SRG266.Lattice.KneserBoundary`, where the trace-filter membership is
reconstructed, so this branch imports neither histogram/DP machinery nor a
whole-search audit.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

set_option maxRecDepth 40000

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

/-- A pure embedding whose
core is presented by the Gram matrix of `(E₇ ⊕ E₇)⁺` produces the intrinsic
E7 branch payload consumed by the mined profile chain. -/
theorem e7BranchPayload_of_pureCoreModel {x : V} (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c e7e7PlusGram) :
    Nonempty (E7BranchPayload G x) := by
  classical
  obtain ⟨C⟩ := e7BranchConstructionData_of_pureCoreModel hG hc M
  obtain ⟨P⟩ := preparedProfiles_of_constructionData C
  rcases C with ⟨Y, D, par, a, n, σ, p, hY, hD, hDfive, hcard,
    hYmin, hYsq, hDsum, hpar01, hDa, hn, hneven, htotal, hn300,
    hasum, hasq, habound, haspecial, hσ, hp⟩
  rcases P with ⟨hprofileD', hprofileFive', henumeration', hprofSum',
    hprofSq', hprofPar', hprofSorted'⟩
  have hprofileD : ∀ side i,
      2 * e7ComponentEnumerationProfile (p side) i = D side (σ side i) := by
    simpa using hprofileD'
  have hprofileFive : ∀ side i,
      (5 : ℤ) ∣ e7ComponentEnumerationProfile (p side) i := by
    simpa using hprofileFive'
  have henumeration : ∀ side, E7ComponentEnumerationWitness (p side) := by
    simpa using henumeration'
  have hprofSum : ∀ side,
      ∑ i, e7ComponentEnumerationProfile (p side) i = 0 := by
    simpa using hprofSum'
  have hprofSq : ∀ side,
      ∑ i, (e7ComponentEnumerationProfile (p side) i) ^ 2 = 4 * n side := by
    simpa using hprofSq'
  have hprofPar : ∀ side (i j : Fin 8),
      e7ComponentEnumerationProfile (p side) i % 2 =
        e7ComponentEnumerationProfile (p side) j % 2 := by
    simpa using hprofPar'
  have hprofSorted : ∀ side,
      (List.ofFn (e7ComponentEnumerationProfile (p side))).Pairwise
        (· ≤ ·) := by
    simpa using hprofSorted'
  -- the shell weights, after sorting
  have hweight : ∀ (B : SecondSubconstituent G x) (side : Bool),
      ∃ w : E7WeightIndex, ∀ i, Y B side (σ side i) = e7Weight4 w i := fun B side =>
    exists_e7Weight4_of_isE7Minimal ((hYmin B side).comp_perm (σ side))
  choose wt hwt using hweight
  -- the three pairing identities
  have hgram : ∀ B C : SecondSubconstituent G x,
      (∑ i, Y B false i * Y C false i) + ∑ i, Y B true i * Y C true i =
        16 * localGramMatrix G x B C := by
    intro B C
    have h := e7e7PlusBlock_dot (M.generator B) (M.generator C)
    rw [M.gram B C] at h
    have hleft : ∑ i, Y B false i * Y C false i =
        ∑ i, e7e7PlusBlock false (M.generator B) i * e7e7PlusBlock false (M.generator C) i :=
      Finset.sum_congr rfl fun i _ => by rw [hY B false i, hY C false i]
    have hright : ∑ i, Y B true i * Y C true i =
        ∑ i, e7e7PlusBlock true (M.generator B) i * e7e7PlusBlock true (M.generator C) i :=
      Finset.sum_congr rfl fun i _ => by rw [hY B true i, hY C true i]
    rw [hleft, hright]
    omega
  have hpair : ∀ B : SecondSubconstituent G x,
      (∑ i, D false i * Y B false i) + ∑ i, D true i * Y B true i = 240 := by
    intro B
    have h := e7e7PlusBlock_dot M.centroid (M.generator B)
    rw [M.centroid_generator hG hc] at h
    have hleft : ∑ i, D false i * Y B false i =
        ∑ i, e7e7PlusBlock false M.centroid i * e7e7PlusBlock false (M.generator B) i :=
      Finset.sum_congr rfl fun i _ => by rw [hD false i, hY B false i]
    have hright : ∑ i, D true i * Y B true i =
        ∑ i, e7e7PlusBlock true M.centroid i * e7e7PlusBlock true (M.generator B) i :=
      Finset.sum_congr rfl fun i _ => by rw [hD true i, hY B true i]
    rw [hleft, hright]
    omega
  have hgensum : ∀ (side : Bool) (j : Fin 8), ∑ B, Y B side j = 11 * D side j := by
    intro side j
    have hcoeff := M.generator_sum e7e7PlusGram_posDef hc
    have hexpY : ∀ B, Y B side j =
        ∑ k, M.generator B k * e7e7PlusCoords k (if side then Sum.inr j else Sum.inl j) :=
      fun B => by rw [hY B side j, e7e7PlusBlock, Matrix.vecMul, dotProduct]
    have hexpD : D side j =
        ∑ k, M.centroid k * e7e7PlusCoords k (if side then Sum.inr j else Sum.inl j) := by
      rw [hD side j, e7e7PlusBlock, Matrix.vecMul, dotProduct]
    have hgen : ∀ k, ∑ B, M.generator B k = 11 * M.centroid k := by
      intro k
      have h := congrFun hcoeff k
      rw [Finset.sum_apply] at h
      simpa using h
    rw [Finset.sum_congr rfl fun B _ => hexpY B, Finset.sum_comm, hexpD, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul, hgen k]; ring
  -- the trace bound at the eight vectors `8 e_i - 1`
  have htrace : ∀ side, 38 ≤ n side := by
    intro side
    have hstep : ∀ i : Fin 8,
        20 * ∑ B, (Y B side i) ^ 2 ≤ 12600 + 8 * (D side i) ^ 2 := by
      intro i
      have hb := M.projector_bound hG hc (e7e7PlusTraceCoeff side i)
      have hgenval : ∀ B : SecondSubconstituent G x,
          Matrix.toBilin' e7e7PlusGram (e7e7PlusTraceCoeff side i) (M.generator B) =
            2 * Y B side i := by
        intro B
        rw [e7e7PlusTrace_toBilin' side i (M.generator B), hY B side i]
      have hcenval :
          Matrix.toBilin' e7e7PlusGram (e7e7PlusTraceCoeff side i) M.centroid =
            2 * D side i := by
        rw [e7e7PlusTrace_toBilin' side i M.centroid, hD side i]
      rw [Finset.sum_congr rfl fun B _ => by rw [hgenval B], hcenval,
        e7e7PlusTrace_norm side i] at hb
      have hexp : ∑ B : SecondSubconstituent G x, (2 * Y B side i) ^ 2 =
          4 * ∑ B, (Y B side i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun B _ => by ring
      rw [hexp] at hb
      nlinarith [hb]
    have hsumstep : ∑ i, 20 * ∑ B, (Y B side i) ^ 2 ≤
        ∑ i : Fin 8, (12600 + 8 * (D side i) ^ 2) :=
      Finset.sum_le_sum fun i _ => hstep i
    have hleft : ∑ i, 20 * ∑ B : SecondSubconstituent G x, (Y B side i) ^ 2 = 105600 := by
      rw [← Finset.mul_sum, Finset.sum_comm,
        Finset.sum_congr rfl fun B _ => hYsq B side, Finset.sum_const, hcard]
      norm_num
    have hright : ∑ i : Fin 8, (12600 + 8 * (D side i) ^ 2) =
        100800 + 8 * ∑ i, (D side i) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
      norm_num
    rw [hleft, hright, hn side] at hsumstep
    omega
  have hnCases : ∀ side,
      n side = 50 ∨ n side = 100 ∨ n side = 150 ∨
        n side = 200 ∨ n side = 250 := by
    intro side
    have hhigh : n side ≤ 262 := by
      cases side
      · have hother := htrace true
        omega
      · have hother := htrace false
        omega
    exact e7e7Plus_componentNorm_cases (D side) (n side)
      (hDfive side) (hn side) (hneven side) (htrace side) hhigh
  have hmined : ∀ side, IsE7MinedComponentProfile (p side) := by
    intro side
    exact ⟨hprofileFive side, n side, hnCases side, hprofSq side⟩
  -- the realization
  have heligible : ∀ B : SecondSubconstituent G x,
      e7Eligible (e7ComponentEnumerationProfile (p false))
        (e7ComponentEnumerationProfile (p true)) (wt B false, wt B true) := by
    intro B
    have hside : ∀ side, 2 * integerDot (e7ComponentEnumerationProfile (p side))
        (e7Weight4 (wt B side)) = ∑ j, D side j * Y B side j := by
      intro side
      rw [integerDot, Finset.mul_sum]
      rw [← Equiv.sum_comp (σ side) (fun j => D side j * Y B side j)]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hwt B side i, ← hprofileD side i]
        ring
    have h := hpair B
    have hf := hside false
    have ht := hside true
    show integerDot (e7ComponentEnumerationProfile (p false)) (e7Weight4 (wt B false)) +
      integerDot (e7ComponentEnumerationProfile (p true)) (e7Weight4 (wt B true)) = 120
    omega
  obtain ⟨realization⟩ : Nonempty (E7CentroidShellGramRealization G x
      (e7ComponentEnumerationProfile (p false)) (e7ComponentEnumerationProfile (p true))) := by
    refine ⟨{ shell := fun B => ⟨(wt B false, wt B true), heligible B⟩
              gram := ?_
              leftCentroid := ?_
              rightCentroid := ?_ }⟩
    · intro B C
      refine e7ShellInner_of_dot _ _ (localGramMatrix G x B C) ?_
      have hside : ∀ side, ∑ i, e7Weight4 (wt B side) i * e7Weight4 (wt C side) i =
          ∑ j, Y B side j * Y C side j := by
        intro side
        rw [← Equiv.sum_comp (σ side) (fun j => Y B side j * Y C side j)]
        exact Finset.sum_congr rfl fun i _ => by rw [hwt B side i, hwt C side i]
      rw [hside false, hside true]
      exact hgram B C
    · intro i
      have h : ∑ B, e7Weight4 (wt B false) i = 11 * D false (σ false i) := by
        rw [Finset.sum_congr rfl fun B _ => (hwt B false i).symm]
        exact hgensum false (σ false i)
      rw [h, ← hprofileD false i]
      ring
    · intro i
      have h : ∑ B, e7Weight4 (wt B true) i = 11 * D true (σ true i) := by
        rw [Finset.sum_congr rfl fun B _ => (hwt B true i).symm]
        exact hgensum true (σ true i)
      rw [h, ← hprofileD true i]
      ring
  exact ⟨{ left := p false
           right := p true
           left_enumeration := henumeration false
           right_enumeration := henumeration true
           left_mined := hmined false
           right_mined := hmined true
           left_sum := hprofSum false
           right_sum := hprofSum true
           left_parity := hprofPar false
           right_parity := hprofPar true
           left_sorted := hprofSorted false
           right_sorted := hprofSorted true
           realization := realization }⟩

end Lattice
end SRG266
