/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Mod11
import Mathlib.Algebra.Field.ZMod

/-!
# Rank consequences of the mod-11 Gram algebra

This file isolates the remaining rank-reduction input.  It proves that an
upper bound `rank L ≤ 12` over `ZMod 11` forces the exact rank to be 12.

The proof is internal to the finite-field algebra: `L²` is idempotent, its
trace forces its rank to be divisible by 11, and the nonzero coupling
`L(L-I) = 2J` supplies the twelfth rank direction. The upper bound is an
explicit hypothesis of the result.
-/

open scoped Matrix

namespace SRG266

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem trace_eq_rank_cast_of_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 11))
    (hA : A * A = A) :
    A.trace = (A.rank : ZMod 11) := by
  let f : (ι → ZMod 11) →ₗ[ZMod 11] (ι → ZMod 11) := A.toLin'
  have hf : IsIdempotentElem f := by
    change f * f = f
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin' hA
  have hproj : LinearMap.IsProj f.range f :=
    LinearMap.IsIdempotentElem.isProj_range f hf
  have htraceRange := hproj.trace
  rw [Matrix.trace_toLin'_eq] at htraceRange
  have hrank :
      A.rank = Module.finrank (ZMod 11) f.range := by
    rw [Matrix.rank_eq_finrank_range_toLin A
      (Pi.basisFun (ZMod 11) ι) (Pi.basisFun (ZMod 11) ι),
      Matrix.toLin_eq_toLin']
  rw [hrank]
  exact htraceRange

theorem localGramMatrixMod11_sq_trace
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixMod11 G x *
      localGramMatrixMod11 G x).trace = 0 := by
  rw [Matrix.trace]
  have hdiag :
      ∀ B : SecondSubconstituent G x,
        (localGramMatrixMod11 G x *
          localGramMatrixMod11 G x) B B = 5 := by
    intro B
    rw [localGramMatrixMod11_sq_apply G hG x B B]
    change (localGramMatrix G x B B : ZMod 11) + 2 = 5
    rw [localGramMatrix_diagonal G hG x B]
    decide
  change
    (∑ B : SecondSubconstituent G x,
      (localGramMatrixMod11 G x *
        localGramMatrixMod11 G x) B B) = 0
  rw [show (∑ B : SecondSubconstituent G x,
      (localGramMatrixMod11 G x *
        localGramMatrixMod11 G x) B B) =
      ∑ _B : SecondSubconstituent G x, (5 : ZMod 11) by
    apply Finset.sum_congr rfl
    intro B _
    exact hdiag B]
  calc
    (∑ _B : SecondSubconstituent G x, (5 : ZMod 11)) =
        (Fintype.card (SecondSubconstituent G x) : ZMod 11) * 5 := by
      simp
    _ = (220 : ZMod 11) * 5 := by
      congr 1
      exact congrArg (fun n : ℕ => (n : ZMod 11))
        (secondSubconstituent_card G hG x)
    _ = 0 := by decide

private theorem localGramMatrixMod11_sq_rank_pos
    (hG : IsHypothetical G) (x : V) :
    0 < (localGramMatrixMod11 G x *
      localGramMatrixMod11 G x).rank := by
  let P := localGramMatrixMod11 G x * localGramMatrixMod11 G x
  have hcard :
      Fintype.card (SecondSubconstituent G x) = 220 :=
    secondSubconstituent_card G hG x
  haveI : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by omega)
  let B : SecondSubconstituent G x := Classical.choice inferInstance
  rw [Matrix.rank_eq_finrank_span_cols]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let w : SecondSubconstituent G x → ZMod 11 := P.col B
  have hwmem :
      w ∈ Submodule.span (ZMod 11) (Set.range P.col) :=
    Submodule.subset_span ⟨B, rfl⟩
  refine ⟨⟨w, hwmem⟩, ?_⟩
  intro hzero
  have hwzero : w = 0 := congrArg Subtype.val hzero
  have hentry := congrFun hwzero B
  have hdiag :
      P B B = 5 := by
    dsimp [P]
    rw [localGramMatrixMod11_sq_apply G hG x B B]
    change (localGramMatrix G x B B : ZMod 11) + 2 = 5
    rw [localGramMatrix_diagonal G hG x B]
    decide
  rw [show w B = P B B by rfl, hdiag] at hentry
  exact (by decide : (5 : ZMod 11) ≠ 0) hentry

theorem localGramMatrixMod11_sq_rank_eq_eleven_of_rank_le_twelve
    (hG : IsHypothetical G) (x : V)
    (hupper : (localGramMatrixMod11 G x).rank ≤ 12) :
    (localGramMatrixMod11 G x *
      localGramMatrixMod11 G x).rank = 11 := by
  let L := localGramMatrixMod11 G x
  let P := L * L
  have hidempotent : P * P = P := by
    simpa [L, P] using localGramMatrixMod11_sq_idempotent G hG x
  have htrace : P.trace = 0 := by
    simpa [L, P] using localGramMatrixMod11_sq_trace G hG x
  have hrankCast : (P.rank : ZMod 11) = 0 := by
    rw [← trace_eq_rank_cast_of_idempotent P hidempotent]
    exact htrace
  have hdvd : 11 ∣ P.rank :=
    (ZMod.natCast_eq_zero_iff P.rank 11).mp hrankCast
  have hpos : 0 < P.rank := by
    simpa [L, P] using localGramMatrixMod11_sq_rank_pos G hG x
  have hle : P.rank ≤ 12 := by
    exact (Matrix.rank_mul_le_left L L).trans hupper
  have hlower : 11 ≤ P.rank := Nat.le_of_dvd hpos hdvd
  have hneTwelve : P.rank ≠ 12 := by
    intro heq
    rw [heq] at hdvd
    norm_num at hdvd
  have hlt : P.rank < 12 := lt_of_le_of_ne hle hneTwelve
  have hupperEleven : P.rank ≤ 11 := Nat.lt_succ_iff.mp (by
    simpa using hlt)
  exact Nat.le_antisymm hupperEleven hlower

theorem localGramMatrixMod11_rank_eq_twelve_of_rank_le_twelve
    (hG : IsHypothetical G) (x : V)
    (hupper : (localGramMatrixMod11 G x).rank ≤ 12) :
    (localGramMatrixMod11 G x).rank = 12 := by
  let L := localGramMatrixMod11 G x
  let P := L * L
  let f := L.mulVecLin
  let p := P.mulVecLin
  have hPrank : P.rank = 11 := by
    simpa [L, P] using
      localGramMatrixMod11_sq_rank_eq_eleven_of_rank_le_twelve
        G hG x hupper
  have hPle : P.rank ≤ L.rank :=
    Matrix.rank_mul_le_left L L
  have hLlower : 11 ≤ L.rank := by omega
  have hLneEleven : L.rank ≠ 11 := by
    intro hLrank
    have hkerle : LinearMap.ker f ≤ LinearMap.ker p := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      change P *ᵥ v = 0
      change (L * L) *ᵥ v = 0
      change L *ᵥ v = 0 at hv
      rw [← Matrix.mulVec_mulVec, hv]
      exact Matrix.mulVec_zero L
    have hfnull := LinearMap.finrank_range_add_finrank_ker f
    have hpnull := LinearMap.finrank_range_add_finrank_ker p
    have hcard :
        Fintype.card (SecondSubconstituent G x) = 220 :=
      secondSubconstituent_card G hG x
    have hkerfinrank :
        Module.finrank (ZMod 11) (LinearMap.ker f) =
          Module.finrank (ZMod 11) (LinearMap.ker p) := by
      have hfRange :
          Module.finrank (ZMod 11) (LinearMap.range f) = L.rank := by
        rfl
      have hpRange :
          Module.finrank (ZMod 11) (LinearMap.range p) = P.rank := by
        rfl
      rw [hfRange, Module.finrank_pi] at hfnull
      rw [hpRange, Module.finrank_pi] at hpnull
      omega
    have hkerEq :
        LinearMap.ker f = LinearMap.ker p :=
      Submodule.eq_of_le_of_finrank_eq hkerle hkerfinrank
    have hcube : L * L * L = L * L := by
      simpa [L] using localGramMatrixMod11_cube_eq_sq G hG x
    have hPsub : P * (L - 1) = 0 := by
      dsimp [P]
      noncomm_ring [hcube]
    have hproductZero : L * (L - 1) = 0 := by
      ext i j
      let v : SecondSubconstituent G x → ZMod 11 :=
        Pi.single j 1
      let y := (L - 1) *ᵥ v
      have hyP : y ∈ LinearMap.ker p := by
        rw [LinearMap.mem_ker]
        change P *ᵥ y = 0
        dsimp [y]
        have hv := congrArg (fun A => A *ᵥ v) hPsub
        simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hv
      have hyF : y ∈ LinearMap.ker f := by
        rw [hkerEq]
        exact hyP
      rw [LinearMap.mem_ker] at hyF
      change L *ᵥ y = 0 at hyF
      dsimp [y] at hyF
      have hvzero : (L * (L - 1)) *ᵥ v = 0 := by
        simpa only [Matrix.mulVec_mulVec] using hyF
      have hentry := congrFun hvzero i
      simpa [v] using hentry
    exact localGramMatrixMod11_mul_sub_one_ne_zero G hG x hproductZero
  have hupperL : L.rank ≤ 12 := by simpa [L] using hupper
  have hlowerTwelve : 12 ≤ L.rank := by omega
  change L.rank = 12
  exact Nat.le_antisymm hupperL hlowerTwelve

end SRG266
