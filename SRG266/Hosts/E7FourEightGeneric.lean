/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightGeneric

/-!
# Exclusion of the generic residual `4 × 8` E7 shell

The eligible shell splits into left-evaluation classes of sizes 20, 96, and
30.  The centroid equations give equality of the outer class totals.  A
checked bit-vector certificate says that a nonzero class-2 profile has total
at least 60, whereas the 20-element class-0 total is strictly below 60.
Consequently both outer totals vanish and the middle total is 220.

For the middle class, the profile equations give `xᵀCx = 30 * 220`.  The
structured Hadamard/Kronecker certificate proves that `96C - 18J` is
positive semidefinite, contradicting

`96 * (30 * 220) < 18 * 220²`.
-/

open scoped BigOperators Matrix

namespace SRG266
namespace E7FourEightGeneric

open E7FourEightGenericData

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

def class0Total (packing : E7ShellPacking d₄ d₈) : ℕ :=
  ∑ i : Class0Index, packing.multiplicity (class0Vertex i)

def class1Total (packing : E7ShellPacking d₄ d₈) : ℕ :=
  ∑ i : Class1Index, packing.multiplicity (class1Vertex i)

def class2Total (packing : E7ShellPacking d₄ d₈) : ℕ :=
  ∑ i : Class2Index, packing.multiplicity (class2Vertex i)

theorem classTotals_sum (packing : E7ShellPacking d₄ d₈) :
    class0Total packing + class1Total packing + class2Total packing = 220 := by
  have hequiv := shellEquiv.sum_comp packing.multiplicity
  have hall :
      (∑ a : AllIndex, packing.multiplicity (shellEquiv a)) = 220 := by
    rw [hequiv, packing.total]
  simpa only [Fintype.sum_sum_type, shellEquiv_apply, allVertex,
    class0Total, class1Total, class2Total, add_assoc] using hall

theorem class0Total_eq_class2Total
    (packing : E7ShellPacking d₄ d₈) :
    class0Total packing = class2Total packing := by
  have haffine := packing.left_affine_sum 0 d₄
  have hleft :
      (∑ w : Shell, (packing.multiplicity w : ℤ) *
          integerDot d₄ (e7Weight4 w.1.1)) =
        8 * (class1Total packing : ℤ) +
          16 * (class2Total packing : ℤ) := by
    calc
      _ = ∑ a : AllIndex,
          (packing.multiplicity (shellEquiv a) : ℤ) *
            integerDot d₄ (e7Weight4 (shellEquiv a).1.1) := by
        exact (shellEquiv.sum_comp
          (fun w : Shell => (packing.multiplicity w : ℤ) *
            integerDot d₄ (e7Weight4 w.1.1))).symm
      _ = (∑ i : Class0Index,
            (packing.multiplicity (class0Vertex i) : ℤ) *
              integerDot d₄ (e7Weight4 (class0Vertex i).1.1)) +
          ((∑ i : Class1Index,
            (packing.multiplicity (class1Vertex i) : ℤ) *
              integerDot d₄ (e7Weight4 (class1Vertex i).1.1)) +
          ∑ i : Class2Index,
            (packing.multiplicity (class2Vertex i) : ℤ) *
              integerDot d₄ (e7Weight4 (class2Vertex i).1.1)) := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [shellEquiv_apply, allVertex]
      _ = 8 * (class1Total packing : ℤ) +
          16 * (class2Total packing : ℤ) := by
        simp only [class0_pairing, class1_pairing, class2_pairing,
          mul_zero, Finset.sum_const_zero, zero_add]
        simp only [class1Total, class2Total, Nat.cast_sum]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · apply Finset.sum_congr rfl
          intro i hi
          ring
  simp only [zero_add, zero_mul] at haffine
  rw [hleft, d₄_norm] at haffine
  have htotal := classTotals_sum packing
  exact_mod_cast (show class0Total packing = class2Total packing by omega)

def globalNeighbours
    {I : Type*} (vertex : I → Shell) (i : I) : Finset Shell :=
  Finset.univ.filter fun w =>
    e7ShellInner (vertex i).1 w.1 = 2

theorem neighbourSum_eq_global
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Shell → Prop) [DecidablePred P]
    (vertex : I → Shell)
    (equiv : I ≃ {w : Shell // P w})
    (hequiv : ∀ i, (equiv i).1 = vertex i)
    (adjacent : I → I → Bool)
    (hadjacent : ∀ i j,
      adjacent i j = decide (e7ShellInner (vertex i).1 (vertex j).1 = 2))
    (hclosed : ∀ i w,
      e7ShellInner (vertex i).1 w.1 = 2 → P w)
    (m : Shell → ℕ) (i : I) :
    (∑ j ∈ profileNeighbours adjacent i, m (vertex j)) =
      ∑ w ∈ globalNeighbours vertex i, m w := by
  let critical : Finset Shell := Finset.univ.filter P
  have hequivSum :
      (∑ j : I,
          if e7ShellInner (vertex i).1 (vertex j).1 = 2
            then m (vertex j) else 0) =
        ∑ w : {w : Shell // P w},
          if e7ShellInner (vertex i).1 w.1.1 = 2
            then m w.1 else 0 := by
    simpa only [hequiv] using
      equiv.sum_comp
        (fun w : {w : Shell // P w} =>
          if e7ShellInner (vertex i).1 w.1.1 = 2 then m w.1 else 0)
  have hleft :
      (∑ j ∈ profileNeighbours adjacent i, m (vertex j)) =
        ∑ j : I,
          if e7ShellInner (vertex i).1 (vertex j).1 = 2
            then m (vertex j) else 0 := by
    rw [profileNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hadjacent]
    by_cases hinner : e7ShellInner (vertex i).1 (vertex j).1 = 2
    · simp [hinner]
    · simp [hinner]
  have hsubtype :
      (∑ w : {w : Shell // P w},
          if e7ShellInner (vertex i).1 w.1.1 = 2
            then m w.1 else 0) =
        ∑ w ∈ critical,
          if e7ShellInner (vertex i).1 w.1 = 2 then m w else 0 := by
    symm
    apply Finset.sum_subtype
    intro w
    simp [critical]
  have hcritical :
      (∑ w ∈ critical,
          if e7ShellInner (vertex i).1 w.1 = 2 then m w else 0) =
        ∑ w ∈ globalNeighbours vertex i, m w := by
    simp only [critical, globalNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hinner : e7ShellInner (vertex i).1 w.1 = 2
    · have hp := hclosed i w hinner
      simp [hinner, hp]
    · simp [hinner]
  rw [hleft, hequivSum, hsubtype, hcritical]

def class0Profile
    (packing : E7ShellPacking d₄ d₈) (i : Class0Index) : ProfileValue :=
  ⟨packing.multiplicity (class0Vertex i), by
    exact Nat.lt_succ_iff.mpr (packing.le_three (class0Vertex i))⟩

def class1Profile
    (packing : E7ShellPacking d₄ d₈) (i : Class1Index) : ProfileValue :=
  ⟨packing.multiplicity (class1Vertex i), by
    exact Nat.lt_succ_iff.mpr (packing.le_three (class1Vertex i))⟩

def class2Profile
    (packing : E7ShellPacking d₄ d₈) (i : Class2Index) : ProfileValue :=
  ⟨packing.multiplicity (class2Vertex i), by
    exact Nat.lt_succ_iff.mpr (packing.le_three (class2Vertex i))⟩

theorem class0Profile_satisfies
    (packing : E7ShellPacking d₄ d₈) :
    ProfileSatisfies class0Adjacent (class0Profile packing) := by
  intro i hi
  have hpos : 0 < packing.multiplicity (class0Vertex i) := by
    exact Nat.pos_of_ne_zero (by simpa [class0Profile] using hi)
  have hprofile := packing.twoProfile (class0Vertex i) hpos
  have hsum := neighbourSum_eq_global
    (fun w : Shell => e7ResidualEvaluation d₄ w.1.1 = 0)
    class0Vertex class0Equiv class0Equiv_apply
    class0Adjacent class0Adjacent_eq_shell class0_inner_two_closed
    packing.multiplicity i
  change
    (∑ j ∈ profileNeighbours class0Adjacent i,
        packing.multiplicity (class0Vertex j)) +
      3 * packing.multiplicity (class0Vertex i) = 30
  rw [hsum]
  simpa only [class0Profile, globalNeighbours] using hprofile

theorem class1Profile_satisfies
    (packing : E7ShellPacking d₄ d₈) :
    ProfileSatisfies class1Adjacent (class1Profile packing) := by
  intro i hi
  have hpos : 0 < packing.multiplicity (class1Vertex i) := by
    exact Nat.pos_of_ne_zero (by simpa [class1Profile] using hi)
  have hprofile := packing.twoProfile (class1Vertex i) hpos
  have hsum := neighbourSum_eq_global
    (fun w : Shell => e7ResidualEvaluation d₄ w.1.1 = 1)
    class1Vertex class1Equiv class1Equiv_apply
    class1Adjacent class1Adjacent_eq_shell class1_inner_two_closed
    packing.multiplicity i
  change
    (∑ j ∈ profileNeighbours class1Adjacent i,
        packing.multiplicity (class1Vertex j)) +
      3 * packing.multiplicity (class1Vertex i) = 30
  rw [hsum]
  simpa only [class1Profile, globalNeighbours] using hprofile

theorem class2Profile_satisfies
    (packing : E7ShellPacking d₄ d₈) :
    ProfileSatisfies class2Adjacent (class2Profile packing) := by
  intro i hi
  have hpos : 0 < packing.multiplicity (class2Vertex i) := by
    exact Nat.pos_of_ne_zero (by simpa [class2Profile] using hi)
  have hprofile := packing.twoProfile (class2Vertex i) hpos
  have hsum := neighbourSum_eq_global
    (fun w : Shell => e7ResidualEvaluation d₄ w.1.1 = 2)
    class2Vertex class2Equiv class2Equiv_apply
    class2Adjacent class2Adjacent_eq_shell class2_inner_two_closed
    packing.multiplicity i
  change
    (∑ j ∈ profileNeighbours class2Adjacent i,
        packing.multiplicity (class2Vertex j)) +
      3 * packing.multiplicity (class2Vertex i) = 30
  rw [hsum]
  simpa only [class2Profile, globalNeighbours] using hprofile

theorem class0Total_lt_sixty
    (packing : E7ShellPacking d₄ d₈) :
    class0Total packing < 60 := by
  have hle : class0Total packing ≤ 60 := by
    calc
      class0Total packing ≤ ∑ _i : Class0Index, 3 := by
        apply Finset.sum_le_sum
        intro i hi
        exact packing.le_three (class0Vertex i)
      _ = 60 := by norm_num
  have hne : class0Total packing ≠ 60 := by
    intro htotal
    have hall (i : Class0Index) :
        packing.multiplicity (class0Vertex i) = 3 := by
      by_contra hne
      have hi_le : packing.multiplicity (class0Vertex i) ≤ 2 := by
        have := packing.le_three (class0Vertex i)
        omega
      have hsum :
          class0Total packing ≤
            ∑ j : Class0Index, if j = i then 2 else 3 := by
        unfold class0Total
        apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [hi_le]
        · simp [hji, packing.le_three (class0Vertex j)]
      have hrhs :
          (∑ j : Class0Index, if j = i then 2 else 3) = 59 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have herase :
            (∑ j ∈ Finset.univ.erase i, if j = i then 2 else 3) =
              ∑ _j ∈ Finset.univ.erase i, 3 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_erase] at hj
          simp [hj.1]
        rw [herase]
        norm_num
      omega
    have hsatisfies := class0Profile_satisfies packing
    have hrow := hsatisfies 0 (by simp [class0Profile, hall])
    have hcard :
        (profileNeighbours class0Adjacent (0 : Class0Index)).card = 9 := by
      exact class0Neighbours_zero_card
    simp only [profileNeighbourSum] at hrow
    have hvalues :
        (∑ j ∈ profileNeighbours class0Adjacent (0 : Class0Index),
          (class0Profile packing j).1) = 27 := by
      simp only [class0Profile, hall]
      simp [hcard]
    have hself : (class0Profile packing (0 : Class0Index)).1 = 3 := by
      simp [class0Profile, hall]
    rw [hvalues, hself] at hrow
    norm_num at hrow
  omega

theorem outerTotals_zero
    (packing : E7ShellPacking d₄ d₈) :
    class0Total packing = 0 ∧ class2Total packing = 0 := by
  have heq := class0Total_eq_class2Total packing
  have hbound := class2ProfileTotalLowerBound
    (class2Profile packing) (class2Profile_satisfies packing)
  have hprofileTotal :
      profileTotal (class2Profile packing) = class2Total packing := by
    rfl
  rw [hprofileTotal] at hbound
  have hlt := class0Total_lt_sixty packing
  rcases hbound with hzero | hlarge
  · exact ⟨heq.trans hzero, hzero⟩
  · omega

theorem class1Total_eq_two_hundred_twenty
    (packing : E7ShellPacking d₄ d₈) :
    class1Total packing = 220 := by
  have hsum := classTotals_sum packing
  have hzero := outerTotals_zero packing
  omega

theorem class1_row_eq_thirty
    (packing : E7ShellPacking d₄ d₈) (i : Class1Index)
    (hi : 0 < packing.multiplicity (class1Vertex i)) :
    ∑ j : Class1Index,
        class1C i j * packing.multiplicity (class1Vertex j) = 30 := by
  have hprofile := class1Profile_satisfies packing i
    (by simpa [class1Profile] using Nat.ne_of_gt hi)
  have hneighbours :
      (∑ j : Class1Index,
          (if class1Adjacent i j then 1 else 0) *
            packing.multiplicity (class1Vertex j)) =
        profileNeighbourSum class1Adjacent (class1Profile packing) i := by
    rw [profileNeighbourSum, profileNeighbours, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hadj : class1Adjacent i j = true
    · simp [hadj, class1Profile]
    · simp [hadj]
  have hdiagonal :
      (∑ j : Class1Index, (if i = j then 3 else 0) *
          packing.multiplicity (class1Vertex j)) =
        3 * packing.multiplicity (class1Vertex i) := by
    simp
  simp only [class1C, add_mul, Finset.sum_add_distrib]
  rw [hneighbours, hdiagonal]
  simpa only [class1Profile] using hprofile

def class1Quadratic (packing : E7ShellPacking d₄ d₈) : ℕ :=
  ∑ i : Class1Index,
    packing.multiplicity (class1Vertex i) *
      ∑ j : Class1Index,
        class1C i j * packing.multiplicity (class1Vertex j)

theorem class1Quadratic_eq
    (packing : E7ShellPacking d₄ d₈) :
    class1Quadratic packing = 30 * class1Total packing := by
  rw [class1Quadratic, class1Total, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : packing.multiplicity (class1Vertex i) = 0
  · simp [hzero]
  · rw [class1_row_eq_thirty packing i (Nat.pos_of_ne_zero hzero)]
    ring

theorem centered_quadratic_identity
    (packing : E7ShellPacking d₄ d₈) :
    rationalQuadraticForm class1Centered
        (fun i => (packing.multiplicity (class1Vertex i) : ℚ)) =
      96 * (class1Quadratic packing : ℚ) -
        18 * (class1Total packing : ℚ) ^ 2 := by
  let x : Class1Index → ℚ :=
    fun i => (packing.multiplicity (class1Vertex i) : ℚ)
  have hqcast :
      (class1Quadratic packing : ℚ) =
        ∑ i : Class1Index, ∑ j : Class1Index,
          x i * class1C i j * x j := by
    simp only [class1Quadratic, x]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have htotalcast :
      (class1Total packing : ℚ) = ∑ i : Class1Index, x i := by
    simp only [class1Total, x, Nat.cast_sum]
  have hallones :
      (∑ i : Class1Index, ∑ j : Class1Index, x i * x j) =
        (∑ i : Class1Index, x i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  change rationalQuadraticForm class1Centered x =
    96 * (class1Quadratic packing : ℚ) -
      18 * (class1Total packing : ℚ) ^ 2
  calc
    rationalQuadraticForm class1Centered x =
        96 * (∑ i : Class1Index, ∑ j : Class1Index,
          x i * class1C i j * x j) -
        18 * (∑ i : Class1Index, ∑ j : Class1Index,
          x i * x j) := by
      simp only [rationalQuadraticForm, class1Centered,
        class1CenteredInt]
      calc
        _ = ∑ i : Class1Index, ∑ j : Class1Index,
            (96 * (x i * class1C i j * x j) -
              18 * (x i * x j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          push_cast
          ring
        _ = _ := by
          calc
            _ = ∑ i : Class1Index, (
                (96 * ∑ j : Class1Index,
                    x i * class1C i j * x j) -
                  18 * ∑ j : Class1Index, x i * x j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
            _ = _ := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
    _ = _ := by rw [← hqcast, hallones, ← htotalcast]

theorem no_packing : IsEmpty (E7ShellPacking d₄ d₈) := by
  refine ⟨fun packing => ?_⟩
  have hpsd := class1Centered_quadratic_nonnegative
    (fun i => (packing.multiplicity (class1Vertex i) : ℚ))
  rw [centered_quadratic_identity packing,
    class1Quadratic_eq packing,
    class1Total_eq_two_hundred_twenty packing] at hpsd
  norm_num at hpsd

end E7FourEightGeneric
end SRG266
