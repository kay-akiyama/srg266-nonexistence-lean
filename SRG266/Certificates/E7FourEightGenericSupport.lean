import SRG266.Certificates.E7FourEightGenericBase

open scoped BigOperators

namespace SRG266

theorem sum_bool_nat (f : Bool → Nat) :
    (∑ b : Bool, f b) = f false + f true := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

theorem sum_indicator_eq_nat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] (e : ι) :
    (∑ x : ι, if P x ∧ x = e then 1 else 0) =
      if P e then 1 else 0 := by
  classical
  by_cases hP : P e
  · have hset :
        (Finset.univ.filter fun x : ι => P x ∧ x = e) = {e} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · exact fun hx => hx.2
      · intro hx
        subst x
        exact ⟨hP, rfl⟩
    rw [Finset.sum_boole, hset]
    simp [hP]
  · have hset :
        (Finset.univ.filter fun x : ι => P x ∧ x = e) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      intro hx
      apply hP
      rw [← hx.2]
      exact hx.1
    rw [Finset.sum_boole, hset]
    simp [hP]

namespace E7FourEightGenericData

def class2LayerIndex (side : Bool) (e : Fin 15) : Class2Index :=
  if side then ⟨15 + e.1, by omega⟩ else ⟨e.1, by omega⟩

theorem class2LayerIndex_bijective :
    Function.Bijective (fun p : Bool × Fin 15 =>
      class2LayerIndex p.1 p.2) := by
  decide +kernel +revert

noncomputable def class2LayerEquiv : Bool × Fin 15 ≃ Class2Index :=
  Equiv.ofBijective _ class2LayerIndex_bijective

@[simp] theorem class2LayerEquiv_apply (p : Bool × Fin 15) :
    class2LayerEquiv p = class2LayerIndex p.1 p.2 := rfl

def class2LayerSupportMask
    (m : Class2Index → ProfileValue) (side : Bool) : BitVec 15 :=
  (BitVec.iunfoldr
    (fun e (_ : Unit) =>
      ((), decide ((m (class2LayerIndex side e)).1 ≠ 0))) ()).2

@[simp] theorem class2LayerSupportMask_getElem
    (m : Class2Index → ProfileValue) (side : Bool) (e : Fin 15) :
    (class2LayerSupportMask m side)[e.1] =
      decide ((m (class2LayerIndex side e)).1 ≠ 0) := by
  have h := BitVec.iunfoldr_getLsbD (f :=
      fun e (_ : Unit) =>
        ((), decide ((m (class2LayerIndex side e)).1 ≠ 0)))
      (fun _ => ()) e (by simp)
  rw [BitVec.getLsbD_eq_getElem e.2] at h
  exact h

def class2MaskCard (mask : BitVec 15) : Nat :=
  ∑ e : Fin 15, if mask[e.1] then 1 else 0

def class2MaskHasSingleMissing (mask : BitVec 15) : Prop :=
  ∃ e : Fin 15, mask[e.1] = false ∧
    ∀ f : Fin 15, f ≠ e → mask[f.1] = true

def class2MaskIsFull (mask : BitVec 15) : Prop :=
  ∀ e : Fin 15, mask[e.1] = true

def class2MaskInnerDegree (mask : BitVec 15) (e : Fin 15) : Nat :=
  ∑ f : Fin 15,
    if mask[f.1] &&
        class2Adjacent (class2LayerIndex false f)
          (class2LayerIndex false e) then 1 else 0

def class2PairAdmissible (left right : BitVec 15) : Prop :=
  (∀ e : Fin 15, left[e.1] = true →
    7 ≤ class2MaskInnerDegree left e +
      (if right[e.1] then 1 else 0)) ∧
  ∀ e : Fin 15, right[e.1] = true →
    7 ≤ class2MaskInnerDegree right e +
      (if left[e.1] then 1 else 0)

def class2PairConclusion (left right : BitVec 15) : Prop :=
  (left = 0#15 ∧ right = 0#15) ∨
  (left = 0#15 ∧
    (class2MaskCard right = 14 ∨ class2MaskCard right = 15)) ∨
  (right = 0#15 ∧
    (class2MaskCard left = 14 ∨ class2MaskCard left = 15)) ∨
  (left ≠ 0#15 ∧ right ≠ 0#15 ∧
    (24 ≤ class2MaskCard left + class2MaskCard right ∨
      (left = right ∧ class2MaskCard left = 10 ∧
        ∀ e : Fin 15, left[e.1] = true →
          class2MaskInnerDegree left e = 6)))

theorem class2Adjacent_layer
    (sourceSide targetSide : Bool) (f e : Fin 15) :
    class2Adjacent (class2LayerIndex sourceSide f)
        (class2LayerIndex targetSide e) =
      if sourceSide = targetSide then
        class2Adjacent (class2LayerIndex false f)
          (class2LayerIndex false e)
      else decide (f = e) := by
  decide +kernel +revert

theorem class2Adjacent_true_true (f e : Fin 15) :
    class2Adjacent (class2LayerIndex true f)
        (class2LayerIndex true e) =
      class2Adjacent (class2LayerIndex false f)
        (class2LayerIndex false e) := by
  decide +kernel +revert

theorem class2Adjacent_false_true (f e : Fin 15) :
    class2Adjacent (class2LayerIndex false f)
        (class2LayerIndex true e) = decide (f = e) := by
  decide +kernel +revert

theorem class2Adjacent_true_false (f e : Fin 15) :
    class2Adjacent (class2LayerIndex true f)
        (class2LayerIndex false e) = decide (f = e) := by
  decide +kernel +revert

theorem class2MaskCard_support
    (m : Class2Index → ProfileValue) (side : Bool) :
    class2MaskCard (class2LayerSupportMask m side) =
      (Finset.univ.filter fun e : Fin 15 =>
        (m (class2LayerIndex side e)).1 ≠ 0).card := by
  simp only [class2MaskCard, class2LayerSupportMask_getElem,
    decide_eq_true_eq]
  simpa using
    (Finset.sum_boole (R := ℕ)
      (fun e : Fin 15 => (m (class2LayerIndex side e)).1 ≠ 0)
      Finset.univ)

end E7FourEightGenericData

def profileSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ProfileValue) : Finset ι :=
  Finset.univ.filter fun i => (m i).1 ≠ 0

@[simp] theorem mem_profileSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ProfileValue) (i : ι) :
    i ∈ profileSupport m ↔ (m i).1 ≠ 0 := by
  simp [profileSupport]

theorem sum_profileSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ProfileValue) :
    (∑ i ∈ profileSupport m, (m i).1) = profileTotal m := by
  unfold profileSupport profileTotal
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : (m i).1 = 0 <;> simp [hz]

def supportInDegree
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (support : Finset ι) (j : ι) : ℕ :=
  (support.filter fun i => adjacent i j = true).card

theorem neighbourSum_over_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue) :
    (∑ i ∈ profileSupport m, profileNeighbourSum adjacent m i) =
      ∑ j ∈ profileSupport m, (m j).1 *
        supportInDegree adjacent (profileSupport m) j := by
  classical
  simp only [profileNeighbourSum, profileNeighbours, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [supportInDegree]
  calc
    (∑ y, ∑ x ∈ profileSupport m,
        if adjacent x y = true then (m y).1 else 0) =
        ∑ y ∈ profileSupport m, ∑ x ∈ profileSupport m,
          if adjacent x y = true then (m y).1 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hz : (m y).1 = 0 := by
        simpa only [mem_profileSupport, not_not] using hy
      simp [hz]
    _ = ∑ y ∈ profileSupport m,
          (m y).1 * {i ∈ profileSupport m | adjacent i y = true}.card := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ x ∈ profileSupport m,
            if adjacent x y = true then (m y).1 else 0) =
            ∑ x ∈ profileSupport m,
              (if adjacent x y = true then 1 else 0) * (m y).1 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases ha : adjacent x y = true <;> simp [ha]
        _ = (∑ x ∈ profileSupport m,
              if adjacent x y = true then 1 else 0) * (m y).1 := by
          rw [Finset.sum_mul]
        _ = {i ∈ profileSupport m | adjacent i y = true}.card * (m y).1 := by
          simp
        _ = (m y).1 * {i ∈ profileSupport m | adjacent i y = true}.card := by
          exact Nat.mul_comm _ _

theorem profileNeighbourSum_le_three_mul_supportInDegree
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool)
    (hsymm : ∀ i j, adjacent i j = adjacent j i)
    (m : ι → ProfileValue) (j : ι) :
    profileNeighbourSum adjacent m j ≤
      3 * supportInDegree adjacent (profileSupport m) j := by
  let activeNeighbours :=
    (profileNeighbours adjacent j).filter fun i => i ∈ profileSupport m
  have hrestrict :
      (∑ i ∈ activeNeighbours, (m i).1) =
        profileNeighbourSum adjacent m j := by
    unfold profileNeighbourSum
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hnotSupport : i ∉ profileSupport m := by
      intro his
      apply hnot
      exact Finset.mem_filter.mpr ⟨hi, his⟩
    have hz : (m i).1 = 0 := by
      simpa only [mem_profileSupport, not_not] using hnotSupport
    simp [hz]
  have hle :
      (∑ i ∈ activeNeighbours, (m i).1) ≤
        ∑ _i ∈ activeNeighbours, 3 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.le_of_lt_succ (m i).2
  have hcard :
      activeNeighbours.card =
        supportInDegree adjacent (profileSupport m) j := by
    have hset : activeNeighbours =
        (profileSupport m).filter fun i => adjacent i j = true := by
      ext i
      simp only [activeNeighbours, Finset.mem_filter, profileNeighbours,
        Finset.mem_univ, true_and]
      rw [hsymm j i]
      tauto
    rw [hset]
    rfl
  calc
    profileNeighbourSum adjacent m j =
        ∑ i ∈ activeNeighbours, (m i).1 := hrestrict.symm
    _ ≤ ∑ _i ∈ activeNeighbours, 3 := hle
    _ = 3 * activeNeighbours.card := by
      simp
      omega
    _ = 3 * supportInDegree adjacent (profileSupport m) j := by rw [hcard]

theorem profileSupport_equation_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue)
    (h : ProfileSatisfies adjacent m) :
    30 * (profileSupport m).card =
      ∑ j ∈ profileSupport m, (m j).1 *
        (supportInDegree adjacent (profileSupport m) j + 3) := by
  have heq :
      (∑ i ∈ profileSupport m,
        (profileNeighbourSum adjacent m i + 3 * (m i).1)) =
      ∑ _i ∈ profileSupport m, 30 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact h i ((mem_profileSupport m i).1 hi)
  rw [Finset.sum_add_distrib, neighbourSum_over_support] at heq
  rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] at heq
  symm
  calc
    (∑ j ∈ profileSupport m, (m j).1 *
        (supportInDegree adjacent (profileSupport m) j + 3)) =
        ∑ j ∈ profileSupport m,
          ((m j).1 * supportInDegree adjacent (profileSupport m) j +
            3 * (m j).1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.mul_add]
      omega
    _ = (∑ j ∈ profileSupport m,
          (m j).1 * supportInDegree adjacent (profileSupport m) j) +
        ∑ j ∈ profileSupport m, 3 * (m j).1 := by
      rw [Finset.sum_add_distrib]
    _ = 30 * (profileSupport m).card := by
      simpa using heq

theorem profileTotal_ge_sixty_of_support_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue)
    (h : ProfileSatisfies adjacent m)
    (hdegree : ∀ j ∈ profileSupport m,
      supportInDegree adjacent (profileSupport m) j ≤ 9)
    (hcard : 24 ≤ (profileSupport m).card) :
    60 ≤ profileTotal m := by
  have heq := profileSupport_equation_sum adjacent m h
  have hle :
      (∑ j ∈ profileSupport m, (m j).1 *
        (supportInDegree adjacent (profileSupport m) j + 3)) ≤
      ∑ j ∈ profileSupport m, 12 * (m j).1 := by
    apply Finset.sum_le_sum
    intro j hj
    have hd := hdegree j hj
    have hfactor :
        supportInDegree adjacent (profileSupport m) j + 3 ≤ 12 := by
      omega
    calc
      (m j).1 * (supportInDegree adjacent (profileSupport m) j + 3) ≤
          (m j).1 * 12 := Nat.mul_le_mul_left _ hfactor
      _ = 12 * (m j).1 := by omega
  have htotal := sum_profileSupport m
  have hsum :
      (∑ j ∈ profileSupport m, 12 * (m j).1) =
        12 * profileTotal m := by
    rw [← Finset.mul_sum, htotal]
  rw [← heq, hsum] at hle
  omega

theorem profileTotal_eq_sixty_of_support_degree_seven
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue)
    (h : ProfileSatisfies adjacent m)
    (hdegree : ∀ j ∈ profileSupport m,
      supportInDegree adjacent (profileSupport m) j = 7)
    (hcard : (profileSupport m).card = 20) :
    profileTotal m = 60 := by
  have heq := profileSupport_equation_sum adjacent m h
  have hrhs :
      (∑ j ∈ profileSupport m, (m j).1 *
        (supportInDegree adjacent (profileSupport m) j + 3)) =
      10 * profileTotal m := by
    calc
      (∑ j ∈ profileSupport m, (m j).1 *
          (supportInDegree adjacent (profileSupport m) j + 3)) =
          ∑ j ∈ profileSupport m, 10 * (m j).1 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdegree j hj]
        omega
      _ = 10 * profileTotal m := by
        rw [← Finset.mul_sum, sum_profileSupport]
  rw [hcard, hrhs] at heq
  omega

namespace E7FourEightGenericData

theorem class2Adjacent_symmetric (i j : Class2Index) :
    class2Adjacent i j = class2Adjacent j i := by
  decide +kernel +revert

theorem class2_fullInDegree (j : Class2Index) :
    ((Finset.univ : Finset Class2Index).filter fun i =>
      class2Adjacent i j = true).card = 9 := by
  decide +kernel +revert

theorem class2_supportInDegree_le_nine
    (support : Finset Class2Index) (j : Class2Index) :
    supportInDegree class2Adjacent support j ≤ 9 := by
  unfold supportInDegree
  rw [← class2_fullInDegree j]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, hi.2⟩

theorem class2_supportInDegree_layer
    (m : Class2Index → ProfileValue) (side : Bool) (e : Fin 15) :
    supportInDegree class2Adjacent (profileSupport m)
        (class2LayerIndex side e) =
      class2MaskInnerDegree (class2LayerSupportMask m side) e +
        (if (class2LayerSupportMask m (!side))[e.1] then 1 else 0) := by
  calc
    supportInDegree class2Adjacent (profileSupport m)
        (class2LayerIndex side e) =
        ∑ i : Class2Index,
          if i ∈ profileSupport m ∧
              class2Adjacent i (class2LayerIndex side e) = true
            then 1 else 0 := by
      unfold supportInDegree
      rw [Finset.sum_boole]
      congr 1
      ext i
      simp
    _ = ∑ p : Bool × Fin 15,
          if class2LayerEquiv p ∈ profileSupport m ∧
              class2Adjacent (class2LayerEquiv p)
                (class2LayerIndex side e) = true
            then 1 else 0 := by
      symm
      apply Fintype.sum_equiv class2LayerEquiv
      intro p
      rfl
    _ = class2MaskInnerDegree (class2LayerSupportMask m side) e +
        (if (class2LayerSupportMask m (!side))[e.1] then 1 else 0) := by
      fin_cases side <;>
        simp only [Fintype.sum_prod_type, class2LayerEquiv_apply,
          mem_profileSupport, class2LayerSupportMask_getElem,
          decide_eq_true_eq, Bool.not_false, Bool.not_true,
          class2MaskInnerDegree]
      · rw [sum_bool_nat]
        simp only [class2Adjacent_false_true, class2Adjacent_true_true,
          decide_eq_true_eq]
        rw [sum_indicator_eq_nat]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      · rw [sum_bool_nat]
        simp only [class2Adjacent_true_false, decide_eq_true_eq]
        rw [sum_indicator_eq_nat]
        simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem class2_profileSupport_card
    (m : Class2Index → ProfileValue) :
    (profileSupport m).card =
      class2MaskCard (class2LayerSupportMask m false) +
        class2MaskCard (class2LayerSupportMask m true) := by
  have hcard :
      (profileSupport m).card =
        ∑ i : Class2Index, if (m i).1 ≠ 0 then 1 else 0 := by
    rw [profileSupport]
    symm
    simpa using
      (Finset.sum_boole (R := ℕ)
        (fun i : Class2Index => (m i).1 ≠ 0) Finset.univ)
  rw [hcard]
  calc
    (∑ i : Class2Index, if (m i).1 ≠ 0 then 1 else 0) =
        ∑ p : Bool × Fin 15,
          if (m (class2LayerEquiv p)).1 ≠ 0 then 1 else 0 := by
      symm
      apply Fintype.sum_equiv class2LayerEquiv
      intro p
      rfl
    _ = class2MaskCard (class2LayerSupportMask m false) +
        class2MaskCard (class2LayerSupportMask m true) := by
      simp only [Fintype.sum_prod_type, class2LayerEquiv_apply,
        class2MaskCard, class2LayerSupportMask_getElem,
        decide_eq_true_eq]
      simp
      omega

theorem class2_pairAdmissible_of_satisfies
    (m : Class2Index → ProfileValue)
    (h : ProfileSatisfies class2Adjacent m) :
    class2PairAdmissible (class2LayerSupportMask m false)
      (class2LayerSupportMask m true) := by
  have hadmissible (side : Bool) (e : Fin 15)
      (hbit : (class2LayerSupportMask m side)[e.1] = true) :
      7 ≤ class2MaskInnerDegree (class2LayerSupportMask m side) e +
        (if (class2LayerSupportMask m (!side))[e.1] then 1 else 0) := by
    have hnonzero : (m (class2LayerIndex side e)).1 ≠ 0 := by
      simpa only [class2LayerSupportMask_getElem, decide_eq_true_eq]
        using hbit
    have heq := h (class2LayerIndex side e) hnonzero
    have hle := profileNeighbourSum_le_three_mul_supportInDegree
      class2Adjacent class2Adjacent_symmetric m
        (class2LayerIndex side e)
    have hmle : (m (class2LayerIndex side e)).1 ≤ 3 :=
      Nat.le_of_lt_succ (m (class2LayerIndex side e)).2
    have hdegree := class2_supportInDegree_layer m side e
    rw [hdegree] at hle
    omega
  constructor
  · intro e he
    simpa using hadmissible false e he
  · intro e he
    simpa using hadmissible true e he

end E7FourEightGenericData

end SRG266
