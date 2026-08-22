/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.A15Shell
import SRG266.Lattice.Branches.PureCore
import SRG266.Lattice.Hosts.A15Plus
import SRG266.Lattice.Branches.A15MinedCentroid
import SRG266.Hosts.A15ReducedProfile

/-!
# The `A₁₅⁺` branch

If the norm-one-free core of the host is `A₁₅⁺` — the only rank-15 host with no
orthogonal `ℤ` summand, so `k = 0` — then a pure embedding produces the direct
shell payload together with all eight elementary side conditions.

Write `d := 4c ∈ ℤ¹⁶` for the scaled centroid and `d_i = r + 4 a_i` with `r` the
glue residue.  Everything is arithmetic in `∑ d = 0` and `∑ d² = 16 · 300`:

* `∑ a = -4r` and `∑ a² = 300 + r²`;
* `∑ a² ≡ ∑ a (mod 2)` forces `r` even, which is
  `SRG266.Lattice.a15Plus_residue_of_even_norm` — the `residue_cases`
  condition;
* `a_i² ≤ ∑ a² ≤ 304` gives `|a_i| ≤ 17`, the `coordinate_bounds` condition;
* if `r = 2` and some `a_i = 17`, the remaining fifteen coordinates would have
  `∑ a_j = -25` and `∑ a_j² = 15`, contradicting `-z² ≤ z`.  That is
  `special_residue_bound`, and it needs no Cauchy--Schwarz inequality;
* `⟨c, v_B⟩ = 15` reads `∑_{i ∈ S_B} d_i = ∓60`, which is exactly
  `SRG266.a15DataEligible` *and* fixes the orientation convention of
  `SRG266.a15ShellCoordinate4`;
* `⟨v_B, v_C⟩ = L_BC` reads `|S_B ∩ S_C| - 1 = L_BC`, and `∑_B v_B = 11 c`
  reads the `centroid` field.

The realization the constructor demands sits at the *canonically reordered*
profile `SRG266.a15CanonicalReducedCoordinates`.  Since that reordering is
defined by coordinate counts it is a permutation of `Fin 16`
(`SRG266.Lattice.exists_perm_comp_of_ofFn_perm`), and the whole data package
above is simply reindexed along it before
`SRG266.Lattice.a15ShellGramRealization_of_data` is called; the four-subset
table index never enters.

The main result is `SRG266.Lattice.a15BranchPayload_of_pureCoreModel`, the
branch construction.  Its finite mined transport and final contradiction are
assembled in `SRG266.Lattice.Branches.A15`.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The only inequality the residue-two argument needs: on `ℤ`, `z (z + 1) ≥ 0`. -/
private theorem neg_sq_le_self (z : ℤ) : -(z ^ 2) ≤ z := by
  rcases le_or_gt 0 z with hz | hz
  · nlinarith [sq_nonneg z]
  · have hz1 : z ≤ -1 := by omega
    nlinarith

/-! ## The branch payload -/

/-- The eight elementary `A₁₅⁺` side conditions and both downstream
realizations. -/
structure A15BranchPayload (x : V) where
  /-- The glue residue of the embedded centroid. -/
  residue : ℤ
  /-- The reduced centroid coordinates, in the order the model supplies them. -/
  coordinates : List ℤ
  /-- The residue is even. -/
  residue_cases : residue = 0 ∨ residue = 2
  /-- There are sixteen coordinates. -/
  coordinate_count : coordinates.length = 16
  /-- Every reduced coordinate lies in `[-17, 17]`. -/
  coordinate_bounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17
  /-- The reduced coordinate sum. -/
  coordinate_sum : coordinates.sum = a15ReducedTargetSum residue
  /-- The reduced squared norm. -/
  coordinate_sq_sum :
    (coordinates.map (fun z : ℤ => z * z)).sum = a15ReducedTargetSq residue
  /-- At residue two the value `17` does not occur. -/
  special_residue_bound : residue = 2 → coordinates.count 17 = 0
  /-- The shell realization, at the canonically reordered profile. -/
  realization :
    A15ShellGramRealization G x
      (a15EnumerationProfile
        (a15ScaleReducedProfile residue
          (a15CanonicalReducedCoordinates coordinates)))
  /-- The canonically reordered centroid after the mined division by ten. -/
  minedCoordinates : List ℤ
  /-- The divided centroid is one of the 17 computed norm profiles. -/
  minedProfile : minedCoordinates ∈ a15MinedNormProfiles
  /-- The same shell, reindexed at the divided-and-rescaled profile. -/
  minedRealization :
    A15ShellGramRealization G x (a15SmallProfile minedCoordinates)

/-! ## The branch construction -/

variable {G}

/-- A pure embedding whose core is
presented by the Gram matrix of `A₁₅⁺` produces the full `a15Plus` payload. -/
theorem a15BranchPayload_of_pureCoreModel {x : V} (hG : IsHypothetical G)
    {E : Rank15EmbeddingWitness G x} {c : IntegralGramLattice G x}
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (M : PureCoreModel E c a15PlusGram) :
    Nonempty (A15BranchPayload G x) := by
  classical
  set y : SecondSubconstituent G x → Fin 16 → ℤ :=
    fun B => Matrix.vecMul (M.generator B) a15PlusCoords with hyDef
  set d : Fin 16 → ℤ := Matrix.vecMul M.centroid a15PlusCoords with hdDef
  -- The scaled centroid: sum zero, squared norm `16 · 300`, one glue residue.
  have hmem := a15Plus_vecMul_mem M.centroid
  have hsum : ∑ i, d i = 0 := hmem.1
  have hsq : ∑ i, d i ^ 2 = 4800 := by
    have h := sum_sq_vecMul_coords a15PlusGram a15PlusCoords 4 a15PlusCoords_gram M.centroid
    rw [M.centroid_norm hG hc] at h
    have h' : ∑ i, d i ^ 2 = 4 ^ 2 * 300 := h
    linarith
  obtain ⟨z, hzRaw, hzMined⟩ :=
    a15Plus_centroid_minedNormProfile hG hc M
  have hz : ∀ i, d i = 10 * z i := by
    intro i
    simpa only [hdDef] using hzRaw i
  obtain ⟨r, hr, hcong⟩ := hmem.residue_normalised
  have hr02 : r = 0 ∨ r = 2 :=
    a15Plus_residue_of_even_norm M.centroid 300 ⟨150, by norm_num⟩
      (M.centroid_norm hG hc) hr hcong
  obtain ⟨a, ha⟩ := exists_shift hcong
  have ha' : ∀ i, d i = r + 4 * a i := ha
  -- The two reduced invariants.
  have hconst : ∑ _i : Fin 16, r = 16 * r := by simp
  have hconstSq : ∑ _i : Fin 16, r ^ 2 = 16 * r ^ 2 := by simp
  have hasum : ∑ i, a i = -4 * r := by
    have h : ∑ i, d i = 16 * r + 4 * ∑ i, a i := by
      rw [Finset.sum_congr rfl fun i _ => ha' i, Finset.sum_add_distrib, hconst,
        ← Finset.mul_sum]
    rw [hsum] at h
    linarith
  have hasq : ∑ i, a i ^ 2 = 300 + r ^ 2 := by
    have hstep : ∀ i : Fin 16, d i ^ 2 = r ^ 2 + 8 * r * a i + 16 * a i ^ 2 := fun i => by
      rw [ha' i]; ring
    have h : ∑ i, d i ^ 2 = 16 * r ^ 2 + 8 * r * (∑ i, a i) + 16 * ∑ i, a i ^ 2 := by
      rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
        Finset.sum_add_distrib, hconstSq, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsq, hasum] at h
    have hrw : 8 * r * (-4 * r) = -32 * r ^ 2 := by ring
    rw [hrw] at h
    linarith
  have hsqBound : ∑ i, a i ^ 2 ≤ 304 := by
    rcases hr02 with h | h <;> rw [hasq, h] <;> norm_num
  have habound : ∀ i, -17 ≤ a i ∧ a i ≤ 17 := by
    intro i
    have hle : a i ^ 2 ≤ 304 :=
      le_trans (Finset.single_le_sum (f := fun j => a j ^ 2)
        (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)) hsqBound
    constructor <;> nlinarith [hle]
  -- At residue two the extreme value `17` is unreachable.
  have h17 : r = 2 → ∀ i, a i ≠ 17 := by
    intro hr2 i hai
    have hasum2 : ∑ j, a j = -8 := by rw [hasum, hr2]; ring
    have hasq2 : ∑ j, a j ^ 2 = 304 := by rw [hasq, hr2]; ring
    have hsplit : a i + ∑ j ∈ Finset.univ.erase i, a j = ∑ j, a j :=
      Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
    have hsplitSq : a i ^ 2 + ∑ j ∈ Finset.univ.erase i, a j ^ 2 = ∑ j, a j ^ 2 :=
      Finset.add_sum_erase Finset.univ (fun j => a j ^ 2) (Finset.mem_univ i)
    rw [hasum2, hai] at hsplit
    rw [hasq2, hai] at hsplitSq
    have hge : -(∑ j ∈ Finset.univ.erase i, a j ^ 2) ≤ ∑ j ∈ Finset.univ.erase i, a j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => neg_sq_le_self (a j)
    linarith
  -- Every generator sits in the norm-three shell.
  have hnorm3 : ∀ B, ∃ S : Finset (Fin 16), S.card = 4 ∧
      ((∀ j, y B j = if j ∈ S then -3 else 1) ∨
        (∀ j, y B j = if j ∈ S then 3 else -1)) := fun B =>
    (a15Plus_norm_three_iff (M.generator B)).mp (M.generator_norm hG B)
  choose S hScard hSshell using hnorm3
  have hshell : ∀ B, (∀ i, y B i = a15RawVector (S B) i) ∨
      (∀ i, y B i = -a15RawVector (S B) i) := by
    intro B
    rcases hSshell B with h | h
    · exact Or.inl h
    · refine Or.inr fun i => ?_
      rw [h i, a15RawVector]
      by_cases hi : i ∈ S B <;> simp [hi]
  -- The three pairing identities.
  have hpair : ∀ B, ∑ i, d i * y B i = 240 := by
    intro B
    have h := dotProduct_vecMul_coords a15PlusGram a15PlusCoords 4 a15PlusCoords_gram
      M.centroid (M.generator B)
    rw [M.centroid_generator hG hc, dotProduct] at h
    have h' : ∑ i, d i * y B i = 4 ^ 2 * 15 := h
    linarith
  have hgram : ∀ B C, ∑ i, y B i * y C i = 16 * localGramMatrix G x B C := by
    intro B C
    have h := dotProduct_vecMul_coords a15PlusGram a15PlusCoords 4 a15PlusCoords_gram
      (M.generator B) (M.generator C)
    rw [M.gram B C, dotProduct] at h
    have h' : ∑ i, y B i * y C i = 4 ^ 2 * localGramMatrix G x B C := h
    rw [h']
    ring
  have hgensum : ∀ k, ∑ B, M.generator B k = 11 * M.centroid k := by
    intro k
    have h := congrFun (M.generator_sum a15PlusGram_posDef hc) k
    rw [Finset.sum_apply] at h
    simpa using h
  have hcent : ∀ i, ∑ B, y B i = 11 * d i := by
    intro i
    have hexpY : ∀ B, y B i = ∑ k, M.generator B k * a15PlusCoords k i := fun B => by
      simp [hyDef, Matrix.vecMul, dotProduct]
    have hexpD : d i = ∑ k, M.centroid k * a15PlusCoords k i := by
      simp [hdDef, Matrix.vecMul, dotProduct]
    rw [Finset.sum_congr rfl fun B _ => hexpY B, Finset.sum_comm, hexpD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, hgensum k]
    ring
  -- Independently reorder the divided centroid.  This is the small profile
  -- consumed by the mined 17-profile classification.
  have hzsq : ∑ i, (z i) ^ 2 = 48 := by
    have hscaled : ∑ i, d i ^ 2 = 100 * ∑ i, (z i) ^ 2 := by
      calc
        ∑ i, d i ^ 2 = ∑ i, (10 * z i) ^ 2 := by
          exact Finset.sum_congr rfl fun i _ => by rw [hz i]
        _ = 100 * ∑ i, (z i) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsq] at hscaled
    omega
  have hzbound : ∀ i, -6 ≤ z i ∧ z i ≤ 6 := by
    intro i
    have hle : z i ^ 2 ≤ ∑ j, (z j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (z j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hzsq] at hle
    constructor <;> nlinarith
  have hzListBounds :
      ∀ q ∈ List.ofFn z, -6 ≤ q ∧ q ≤ 6 :=
    List.forall_mem_ofFn_iff.mpr hzbound
  set smallCoordinates : List ℤ :=
    a15SmallCanonicalCoordinates (List.ofFn z) with hsmallDef
  have hsmallPerm : smallCoordinates.Perm (List.ofFn z) := by
    rw [hsmallDef]
    exact a15SmallCanonicalCoordinates_perm (List.ofFn z) hzListBounds
  have hsmallLen : smallCoordinates.length = 16 := by
    exact hsmallPerm.length_eq.trans (by simp)
  have hofFnSmall :
      List.ofFn (fun i : Fin 16 => smallCoordinates.getD i.1 0) =
        smallCoordinates := by
    refine List.ext_getElem (by rw [List.length_ofFn, hsmallLen])
      fun i h1 h2 => ?_
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem smallCoordinates 0 h2
  obtain ⟨τ, hτ⟩ :=
    exists_perm_comp_of_ofFn_perm
      (f := fun i : Fin 16 => smallCoordinates.getD i.1 0) (g := z)
      (by rw [hofFnSmall]; exact hsmallPerm)
  have hsmallProfile :
      a15SmallProfile smallCoordinates = fun i => d (τ i) := by
    funext i
    change 10 * smallCoordinates.getD i.1 0 = d (τ i)
    rw [← hτ i]
    exact (hz (τ i)).symm
  -- The canonical reordering is a permutation of the sixteen coordinates.
  set coordinates : List ℤ := List.ofFn a with hcoordDef
  have hlen : coordinates.length = 16 := by rw [hcoordDef, List.length_ofFn]
  have hbounds : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17 := by
    rw [hcoordDef]
    exact List.forall_mem_ofFn_iff.mpr habound
  set canonical : List ℤ := a15CanonicalReducedCoordinates coordinates with hcanonDef
  have hcanonPerm : canonical.Perm coordinates :=
    a15CanonicalReducedCoordinates_perm coordinates hbounds
  have hcanonLen : canonical.length = 16 := hcanonPerm.length_eq.trans hlen
  have hofFn : List.ofFn (fun i : Fin 16 => canonical.getD i.1 0) = canonical := by
    refine List.ext_getElem (by rw [List.length_ofFn, hcanonLen]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem canonical 0 h2
  obtain ⟨σ, hσ⟩ :=
    exists_perm_comp_of_ofFn_perm (f := fun i : Fin 16 => canonical.getD i.1 0) (g := a)
      (by rw [hofFn, ← hcoordDef]; exact hcanonPerm)
  -- The target profile is the centroid profile, reindexed.
  have hprofile :
      a15EnumerationProfile (a15ScaleReducedProfile r canonical) = fun i => d (σ i) := by
    funext i
    rw [a15EnumerationProfile_scale_apply r canonical hcanonLen i, ha' (σ i), hσ i]
    ring
  refine ⟨{ residue := r
            coordinates := coordinates
            residue_cases := hr02
            coordinate_count := hlen
            coordinate_bounds := hbounds
            coordinate_sum := ?_
            coordinate_sq_sum := ?_
            special_residue_bound := ?_
            realization := ?_
            minedCoordinates := smallCoordinates
            minedProfile := ?_
            minedRealization := ?_ }⟩
  · rw [hcoordDef, List.sum_ofFn, hasum]
    rcases hr02 with h | h <;> rw [h] <;> norm_num [a15ReducedTargetSum]
  · have hmapsum : ((List.ofFn a).map (fun z : ℤ => z * z)).sum = ∑ i, a i ^ 2 := by
      rw [List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Function.comp_apply]
        ring
    rw [hcoordDef, hmapsum, hasq]
    rcases hr02 with h | h <;> rw [h] <;> norm_num [a15ReducedTargetSq]
  · intro hr2
    have hne : ∀ z ∈ coordinates, z ≠ 17 := by
      rw [hcoordDef]
      exact List.forall_mem_ofFn_iff.mpr (h17 hr2)
    exact List.count_eq_zero.mpr fun hcontra => hne 17 hcontra rfl
  · rw [← hcanonDef, hprofile]
    refine Nonempty.some (a15ShellGramRealization_of_data (G := G) (x := x)
        (fun i => d (σ i))
        ((Equiv.sum_comp σ d).trans hsum)
        (fun B i => y B (σ i)) (fun B => (S B).map σ.symm.toEmbedding)
        (fun B => by rw [Finset.card_map]; exact hScard B)
        (fun B => by
          rcases hshell B with h | h
          · exact Or.inl fun i => by rw [a15RawVector_map]; exact h (σ i)
          · exact Or.inr fun i => by rw [a15RawVector_map]; exact h (σ i))
        (fun B => (Equiv.sum_comp σ (fun i => d i * y B i)).trans (hpair B))
        (fun B C => (Equiv.sum_comp σ (fun i => y B i * y C i)).trans (hgram B C))
        (fun i => hcent (σ i)))
  · simpa only [hsmallDef] using hzMined
  · rw [hsmallProfile]
    refine Nonempty.some (a15ShellGramRealization_of_data (G := G) (x := x)
        (fun i => d (τ i))
        ((Equiv.sum_comp τ d).trans hsum)
        (fun B i => y B (τ i)) (fun B => (S B).map τ.symm.toEmbedding)
        (fun B => by rw [Finset.card_map]; exact hScard B)
        (fun B => by
          rcases hshell B with h | h
          · exact Or.inl fun i => by rw [a15RawVector_map]; exact h (τ i)
          · exact Or.inr fun i => by rw [a15RawVector_map]; exact h (τ i))
        (fun B => (Equiv.sum_comp τ (fun i => d i * y B i)).trans (hpair B))
        (fun B C => (Equiv.sum_comp τ (fun i => y B i * y C i)).trans (hgram B C))
        (fun i => hcent (τ i)))

end Lattice
end SRG266
