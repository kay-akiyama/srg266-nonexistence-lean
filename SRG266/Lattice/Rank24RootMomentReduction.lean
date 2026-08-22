/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ThetaSecondMomentReduction

/-!
# Reduction of the low-rank theta moment to rank twenty four

This file is the algebraic half of the even-neighbour route to
`SRG266.ThetaRootSecondMomentInput`.  Let `L` be a norm-one-free positive-definite
unimodular lattice of rank `n`, where `12 <= n <= 15`, and put `m = 24 - n`.
The standard even neighbour of

`L orthogonal-sum Z^m`

has rank twenty four.  It contains the doubled copy `2L`; its roots split as
the roots of `L` and the roots of `D_m`.  Consequently, if the roots of every
even unimodular rank-24 lattice have a scalar second moment, that scalar can be
read off on the `D_m` factor.  It is `4 * (m - 1) = 4 * (23 - n)`.  Evaluating
the rank-24 identity on doubled vectors from `L` introduces a factor four on
both sides, which cancels and gives exactly the moment required by
`ThetaRootSecondMomentInput`.

The construction of the standard even neighbour is deliberately represented
by `EvenNeighbor24Data`; a separate file constructs this data.  The present
file proves everything after that construction.  In particular:

* `DRoot m` is an explicit, duplicate-free parametrisation of the roots of
  `D_m`;
* the four numerical moments needed for `m = 9, 10, 11, 12` are checked by the
  kernel with ordinary `decide`;
* `thetaRootSecondMoment_of_evenNeighbor24` performs the exact sum transport
  and determines the rank-24 scalar.

No native or bit-vector decision procedure is used.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

/-! ## The roots of `D_m` -/

/-- A sign represented without quotienting: `false` is `-1` and `true` is
`1`. -/
def signedUnit : Bool → ℤ
  | false => -1
  | true => 1

/-- A duplicate-free root of `D_m`: two ordered positions `i < j`, with an
independent sign at each position. -/
structure DRoot (m : ℕ) where
  i : Fin m
  j : Fin m
  lt : i < j
  si : Bool
  sj : Bool
  deriving DecidableEq, Fintype

/-- The ordinary coordinate vector represented by a `D_m` root. -/
def DRoot.vector {m : ℕ} (r : DRoot m) : Fin m → ℤ := fun k =>
  if k = r.i then signedUnit r.si else if k = r.j then signedUnit r.sj else 0

/-- The standard integral dot product. -/
def intDot {m : ℕ} (x y : Fin m → ℤ) : ℤ :=
  ∑ i, x i * y i

theorem intDot_self_nonneg {m : ℕ} (x : Fin m → ℤ) :
    0 ≤ intDot x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem intDot_self_eq_zero_iff {m : ℕ} (x : Fin m → ℤ) :
    intDot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi : x i * x i ≤ intDot x x :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (x j))
        (Finset.mem_univ i)
    rw [h] at hi
    have hs := mul_self_nonneg (x i)
    exact mul_self_eq_zero.mp (le_antisymm hi hs)
  · rintro rfl
    simp [intDot]

/-- The fixed root `e_0 + e_1`, available as soon as `2 <= m`. -/
def DRoot.test {m : ℕ} (hm : 2 ≤ m) : DRoot m where
  i := ⟨0, by omega⟩
  j := ⟨1, hm⟩
  lt := by simp
  si := true
  sj := true

@[simp]
theorem signedUnit_sq (s : Bool) : signedUnit s * signedUnit s = 1 := by
  cases s <;> decide

/-- Every listed `D_m` vector has squared norm two. -/
theorem DRoot.intDot_self {m : ℕ} (r : DRoot m) :
    intDot r.vector r.vector = 2 := by
  classical
  rw [show intDot r.vector r.vector =
      ∑ k, ((if k = r.i then 1 else 0) + if k = r.j then 1 else 0) by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : k = r.i
    · subst k
      simp [DRoot.vector, signedUnit_sq, ne_of_lt r.lt]
    · by_cases hj : k = r.j
      · subst k
        simp [DRoot.vector, hi, signedUnit_sq]
      · simp [DRoot.vector, hi, hj]]
  simp [Finset.sum_add_distrib]

/-- The coordinate sum of a `D_m` root is the sum of its two signs. -/
theorem DRoot.sum_vector {m : ℕ} (r : DRoot m) :
    (∑ i, r.vector i) = signedUnit r.si + signedUnit r.sj := by
  classical
  rw [show (∑ i, r.vector i) =
      ∑ i, ((if i = r.i then signedUnit r.si else 0) +
        (if i = r.j then signedUnit r.sj else 0)) by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = r.i
    · subst i
      simp [DRoot.vector, ne_of_lt r.lt]
    · by_cases hj : i = r.j
      · subst i
        simp [DRoot.vector, ne_of_gt r.lt]
      · simp [DRoot.vector, hi, hj]]
  rw [Finset.sum_add_distrib]
  simp

/-- The coordinate sum of every `D_m` root is even. -/
theorem DRoot.sum_vector_even {m : ℕ} (r : DRoot m) :
    ∃ a : ℤ, (∑ i, r.vector i) = 2 * a := by
  rw [r.sum_vector]
  cases r.si <;> cases r.sj
  · exact ⟨-1, by norm_num [signedUnit]⟩
  · exact ⟨0, by norm_num [signedUnit]⟩
  · exact ⟨0, by norm_num [signedUnit]⟩
  · exact ⟨1, by norm_num [signedUnit]⟩

@[simp]
theorem signedUnit_ne_zero (s : Bool) : signedUnit s ≠ 0 := by
  cases s <;> decide

theorem signedUnit_injective : Function.Injective signedUnit := by
  intro s t h
  cases s <;> cases t <;> simp_all [signedUnit]

@[simp]
theorem DRoot.vector_i {m : ℕ} (r : DRoot m) :
    r.vector r.i = signedUnit r.si := by
  simp [DRoot.vector]

@[simp]
theorem DRoot.vector_j {m : ℕ} (r : DRoot m) :
    r.vector r.j = signedUnit r.sj := by
  simp [DRoot.vector, ne_of_gt r.lt]

theorem DRoot.vector_ne_zero_iff {m : ℕ} (r : DRoot m) (k : Fin m) :
    r.vector k ≠ 0 ↔ k = r.i ∨ k = r.j := by
  by_cases hi : k = r.i
  · simp [hi]
  · by_cases hj : k = r.j
    · subst k
      simp [DRoot.vector, ne_of_gt r.lt]
    · simp [DRoot.vector, hi, hj]

/-- The duplicate-free parametrisation really is injective. -/
theorem DRoot.vector_injective {m : ℕ} :
    Function.Injective (@DRoot.vector m) := by
  intro r s hrs
  have hi : r.i = s.i ∨ r.i = s.j :=
    (s.vector_ne_zero_iff r.i).mp (by
      rw [← hrs]
      show r.vector r.i ≠ 0
      rw [r.vector_i]
      exact signedUnit_ne_zero r.si)
  have hj : r.j = s.i ∨ r.j = s.j :=
    (s.vector_ne_zero_iff r.j).mp (by
      rw [← hrs]
      show r.vector r.j ≠ 0
      rw [r.vector_j]
      exact signedUnit_ne_zero r.sj)
  have hii : r.i = s.i := by
    rcases hi with hi | hi
    · exact hi
    · rcases hj with hj | hj
      · exfalso
        have hsr : s.i < r.i := by simpa [hi] using s.lt
        have hrs' : r.i < s.i := by simpa [hj] using r.lt
        exact lt_asymm hsr hrs'
      · exact absurd (hi.trans hj.symm) (ne_of_lt r.lt)
  have hjj : r.j = s.j := by
    rcases hj with hj | hj
    · exact absurd (hii.trans hj.symm) (ne_of_lt r.lt)
    · exact hj
  have hsi : r.si = s.si := by
    apply signedUnit_injective
    calc
      signedUnit r.si = r.vector r.i := r.vector_i.symm
      _ = s.vector r.i := congrFun hrs r.i
      _ = s.vector s.i := congrArg s.vector hii
      _ = signedUnit s.si := s.vector_i
  have hsj : r.sj = s.sj := by
    apply signedUnit_injective
    calc
      signedUnit r.sj = r.vector r.j := r.vector_j.symm
      _ = s.vector r.j := congrFun hrs r.j
      _ = s.vector s.j := congrArg s.vector hjj
      _ = signedUnit s.sj := s.vector_j
  cases r
  cases s
  simp_all

/-- An integral coordinate whose square occurs in a square-sum equal to two
is `0`, `1`, or `-1`. -/
theorem int_eq_zero_or_signedUnit_of_sq_le_two (z : ℤ) (hz : z * z ≤ 2) :
    z = 0 ∨ ∃ s : Bool, signedUnit s = z := by
  have hlo : -1 ≤ z := by
    by_contra h
    have : z ≤ -2 := by omega
    nlinarith
  have hhi : z ≤ 1 := by
    by_contra h
    have : 2 ≤ z := by omega
    nlinarith
  interval_cases z
  · exact Or.inr ⟨false, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨true, rfl⟩

/-- Every integral vector of squared norm two is represented by exactly one
listed `D_m` root. -/
theorem DRoot.exists_vector_eq_of_intDot_self_eq_two {m : ℕ}
    (z : Fin m → ℤ) (hz : intDot z z = 2) :
    ∃ r : DRoot m, r.vector = z := by
  classical
  let support : Finset (Fin m) := Finset.univ.filter fun i => z i ≠ 0
  have hle : ∀ i, z i * z i ≤ 2 := by
    intro i
    calc
      z i * z i ≤ ∑ j, z j * z j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (z j))
          (Finset.mem_univ i)
      _ = 2 := hz
  have hunit : ∀ i, z i = 0 ∨ ∃ s : Bool, signedUnit s = z i := fun i =>
    int_eq_zero_or_signedUnit_of_sq_le_two (z i) (hle i)
  have hsumCard : (support.card : ℤ) = 2 := by
    calc
      (support.card : ℤ) = (∑ i ∈ support, (1 : ℤ)) := by simp
      _ = ∑ i, z i * z i := by
        calc
          (∑ i ∈ support, (1 : ℤ)) =
              ∑ i, if z i ≠ 0 then (1 : ℤ) else 0 := by
            dsimp only [support]
            exact Finset.sum_filter (s := Finset.univ)
              (fun i => z i ≠ 0) (fun _ => (1 : ℤ))
          _ = ∑ i, z i * z i := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : z i = 0
            · simp [hi]
            · obtain ⟨s, hs⟩ := (hunit i).resolve_left hi
              simp [← hs, signedUnit_sq]
      _ = 2 := hz
  have hcard : support.card = 2 := by omega
  obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hcard
  have hi : z i ≠ 0 := by
    have : i ∈ support := by simp [hsupp]
    simpa [support] using this
  have hj : z j ≠ 0 := by
    have : j ∈ support := by simp [hsupp]
    simpa [support] using this
  obtain ⟨si, hsi⟩ := (hunit i).resolve_left hi
  obtain ⟨sj, hsj⟩ := (hunit j).resolve_left hj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let r : DRoot m := ⟨i, j, hijlt, si, sj⟩
    refine ⟨r, funext fun k => ?_⟩
    by_cases hki : k = i
    · subst k
      change (if i = i then signedUnit si else
        if i = j then signedUnit sj else 0) = z i
      rw [if_pos rfl]
      exact hsi
    · by_cases hkj : k = j
      · subst k
        change (if j = i then signedUnit si else
          if j = j then signedUnit sj else 0) = z j
        rw [if_neg (ne_of_gt hijlt), if_pos rfl]
        exact hsj
      · have hknot : k ∉ support := by simp [hsupp, hki, hkj]
        have hkzero : z k = 0 := by simpa [support] using hknot
        simp [r, DRoot.vector, hki, hkj, hkzero]
  · let r : DRoot m := ⟨j, i, hjilt, sj, si⟩
    refine ⟨r, funext fun k => ?_⟩
    by_cases hkj : k = j
    · subst k
      change (if j = j then signedUnit sj else
        if j = i then signedUnit si else 0) = z j
      rw [if_pos rfl]
      exact hsj
    · by_cases hki : k = i
      · subst k
        change (if i = j then signedUnit sj else
          if i = i then signedUnit si else 0) = z i
        rw [if_neg (ne_of_gt hjilt), if_pos rfl]
        exact hsi
      · have hknot : k ∉ support := by simp [hsupp, hki, hkj]
        have hkzero : z k = 0 := by simpa [support] using hknot
        simp [r, DRoot.vector, hki, hkj, hkzero]

/-- Coordinate classification of the roots of the standard `D_m` lattice. -/
noncomputable def DRoot.vectorEquiv (m : ℕ) :
    DRoot m ≃ {z : Fin m → ℤ // intDot z z = 2} :=
  Equiv.ofBijective (fun r => ⟨r.vector, r.intDot_self⟩) ⟨
    fun r s h => DRoot.vector_injective (Subtype.ext_iff.mp h),
    fun z => by
      obtain ⟨r, hr⟩ := DRoot.exists_vector_eq_of_intDot_self_eq_two z.1 z.2
      exact ⟨r, Subtype.ext hr⟩⟩

/-- The `D_9` test-root second moment.  This and its three companions are
small closed integer computations, evaluated by the kernel. -/
theorem dRoot_test_secondMoment_9 :
    (∑ r : DRoot 9,
      intDot r.vector (DRoot.test (m := 9) (by omega)).vector ^ 2) =
      8 * (9 - 1) := by
  set_option maxRecDepth 100000 in
    decide

theorem dRoot_test_secondMoment_10 :
    (∑ r : DRoot 10,
      intDot r.vector (DRoot.test (m := 10) (by omega)).vector ^ 2) =
      8 * (10 - 1) := by
  set_option maxRecDepth 100000 in
    decide

theorem dRoot_test_secondMoment_11 :
    (∑ r : DRoot 11,
      intDot r.vector (DRoot.test (m := 11) (by omega)).vector ^ 2) =
      8 * (11 - 1) := by
  set_option maxRecDepth 100000 in
    decide

theorem dRoot_test_secondMoment_12 :
    (∑ r : DRoot 12,
      intDot r.vector (DRoot.test (m := 12) (by omega)).vector ^ 2) =
      8 * (12 - 1) := by
  set_option maxRecDepth 100000 in
    decide

/-- The test-root second moment in precisely the four dimensions occurring in
the rank-24 stabilization. -/
theorem dRoot_test_secondMoment {m : ℕ} (hmlo : 9 ≤ m) (hmhi : m ≤ 12) :
    (∑ r : DRoot m, intDot r.vector (DRoot.test (by omega)).vector ^ 2) =
      8 * (m - 1) := by
  interval_cases m
  · exact dRoot_test_secondMoment_9
  · exact dRoot_test_secondMoment_10
  · exact dRoot_test_secondMoment_11
  · exact dRoot_test_secondMoment_12

/-! ## The exact output of the even-neighbour construction -/

/-- Data supplied by the standard even-neighbour construction for
`L orthogonal-sum Z^(24-n)`.

The `rootSum` field is a sum-level formulation of the exact disjoint root
decomposition.  It is stronger than a mere cover: it records multiplicities,
which prevents either duplicate `D_m` roots or overlap with the roots of `L`.
The construction file proves it from an explicit equivalence of finite root
types. -/
structure EvenNeighbor24Data {n : ℕ} (L : PDUnimodularLattice n) where
  /-- The even unimodular neighbour. -/
  neighbor : PDUnimodularLattice 24
  /-- Every norm in the neighbour is even. -/
  evenNorm : ∀ z : neighbor.carrier, Even (neighbor.pairing z z)
  /-- The doubled original lattice inside its even neighbour.  An odd lattice
  itself cannot embed isometrically into an even lattice. -/
  leftDouble : L.carrier →ₗ[ℤ] neighbor.carrier
  /-- Doubling multiplies the pairing by four. -/
  leftDoublePairing : ∀ x y,
    neighbor.pairing (leftDouble x) (leftDouble y) = 4 * L.pairing x y
  /-- A root of `L`, which has even norm, lies in the even sublattice and hence
  in the neighbour without being doubled. -/
  leftRoot : NormTwoRoot L → neighbor.carrier
  /-- Pairing a left root with a doubled left vector contributes twice the
  original pairing. -/
  leftRootPairing : ∀ r x,
    neighbor.pairing (leftRoot r) (leftDouble x) = 2 * L.pairing r.1 x
  /-- The explicitly parametrised `D_(24-n)` roots in the neighbour. -/
  dRoot : DRoot (24 - n) → neighbor.carrier
  /-- Their pairings are their ordinary coordinate dot products. -/
  dRootPairing : ∀ r s,
    neighbor.pairing (dRoot r) (dRoot s) = intDot r.vector s.vector
  /-- The doubled left factor and the `D_m` factor are orthogonal. -/
  crossDoublePairing : ∀ x r,
    neighbor.pairing (leftDouble x) (dRoot r) = 0
  /-- Left roots and `D_m` roots are orthogonal. -/
  crossRootPairing : ∀ x r,
    neighbor.pairing (leftRoot x) (dRoot r) = 0
  /-- Every root occurs exactly once in one of the two displayed families. -/
  rootSum : ∀ f : neighbor.carrier → ℤ,
    (∑ r : NormTwoRoot neighbor, f r.1) =
      (∑ r : NormTwoRoot L, f (leftRoot r)) +
        ∑ r : DRoot (24 - n), f (dRoot r)

/-- The purely algebraic existence statement for the standard even neighbour.
Unlike the theta statement below, this contains no modular-form assertion. -/
abbrev EvenNeighbor24Input : Prop :=
  ∀ (n : ℕ), 12 ≤ n → n ≤ 15 → ∀ L : PDUnimodularLattice n,
    (∀ v : L.carrier, L.pairing v v ≠ 1) → Nonempty (EvenNeighbor24Data L)

/-- The rank-24 analytic statement needed by this route: the root second
moment of an even positive-definite unimodular lattice is scalar.  The scalar
is not specified; the `D_m` factor determines it internally. -/
abbrev EvenUnimodular24RootScalarInput : Prop :=
  ∀ N : PDUnimodularLattice 24,
    (∀ z : N.carrier, Even (N.pairing z z)) →
      ∃ c : ℤ, RootSecondMomentIdentity N c

/-! ## Moment transport -/

/-- **Rank-24 moment transport.**  The standard even neighbour and the scalar
rank-24 root moment imply the exact low-rank moment
`4 * (23 - n)`.

The proof first evaluates the unknown rank-24 scalar on the fixed root
`e_0 + e_1` of the `D_(24-n)` factor.  The original roots contribute zero and
the explicit `D_m` computation contributes `8 * (m-1)`, while the test vector
has norm two.  It then evaluates the same identity on two vectors of `L`; now
the `D_m` contribution is zero. -/
theorem rootSecondMoment_of_evenNeighbor24
    (h24 : EvenUnimodular24RootScalarInput)
    {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n ≤ 15)
    (L : PDUnimodularLattice n) (E : EvenNeighbor24Data L) :
    RootSecondMomentIdentity L (thetaRootSecondMomentScalar n) := by
  classical
  let m := 24 - n
  have hmlo : 9 ≤ m := by omega
  have hmhi : m ≤ 12 := by omega
  obtain ⟨c, hc⟩ := h24 E.neighbor E.evenNorm
  let q : DRoot m := DRoot.test (by omega)
  have hscalarEq : 2 * c = 8 * (m - 1) := by
    have htest := hc (E.dRoot q) (E.dRoot q)
    rw [show
      (∑ r : NormTwoRoot E.neighbor,
        E.neighbor.pairing r.1 (E.dRoot q) *
          E.neighbor.pairing r.1 (E.dRoot q)) =
        (∑ r : NormTwoRoot L,
          E.neighbor.pairing (E.leftRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.leftRoot r) (E.dRoot q)) +
          ∑ r : DRoot (24 - n),
            E.neighbor.pairing (E.dRoot r) (E.dRoot q) *
              E.neighbor.pairing (E.dRoot r) (E.dRoot q) from
      E.rootSum (fun z =>
        E.neighbor.pairing z (E.dRoot q) * E.neighbor.pairing z (E.dRoot q))]
      at htest
    have hleft :
        (∑ r : NormTwoRoot L,
          (E.neighbor.pairing (E.leftRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.leftRoot r) (E.dRoot q))) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [E.crossRootPairing]
      simp
    have hright :
        (∑ r : DRoot m,
          (E.neighbor.pairing (E.dRoot r) (E.dRoot q) *
            E.neighbor.pairing (E.dRoot r) (E.dRoot q))) = 8 * (m - 1) := by
      simpa only [E.dRootPairing, pow_two] using
        dRoot_test_secondMoment hmlo hmhi
    rw [hleft, zero_add, hright, E.dRootPairing, DRoot.intDot_self] at htest
    linarith
  have hcval : c = thetaRootSecondMomentScalar n := by
    simp only [thetaRootSecondMomentScalar]
    omega
  intro x y
  have hxy := hc (E.leftDouble x) (E.leftDouble y)
  rw [show
    (∑ r : NormTwoRoot E.neighbor,
      E.neighbor.pairing r.1 (E.leftDouble x) *
        E.neighbor.pairing r.1 (E.leftDouble y)) =
      (∑ r : NormTwoRoot L,
        E.neighbor.pairing (E.leftRoot r) (E.leftDouble x) *
          E.neighbor.pairing (E.leftRoot r) (E.leftDouble y)) +
        ∑ r : DRoot (24 - n),
          E.neighbor.pairing (E.dRoot r) (E.leftDouble x) *
            E.neighbor.pairing (E.dRoot r) (E.leftDouble y) from
    E.rootSum (fun z =>
      E.neighbor.pairing z (E.leftDouble x) *
        E.neighbor.pairing z (E.leftDouble y))]
    at hxy
  have hd :
      (∑ r : DRoot m,
        (E.neighbor.pairing (E.dRoot r) (E.leftDouble x) *
          E.neighbor.pairing (E.dRoot r) (E.leftDouble y))) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [E.neighbor.symmetric.eq (E.dRoot r) (E.leftDouble x),
      E.neighbor.symmetric.eq (E.dRoot r) (E.leftDouble y),
      E.crossDoublePairing, E.crossDoublePairing]
    simp
  rw [hd, add_zero, E.leftDoublePairing, hcval] at hxy
  simp only [E.leftRootPairing] at hxy
  have hfour :
      4 * (∑ r : NormTwoRoot L,
        L.pairing r.1 x * L.pairing r.1 y) =
        4 * (thetaRootSecondMomentScalar n * L.pairing x y) := by
    calc
      4 * (∑ r : NormTwoRoot L,
          L.pairing r.1 x * L.pairing r.1 y) =
          ∑ r : NormTwoRoot L,
            (2 * L.pairing r.1 x) * (2 * L.pairing r.1 y) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring
      _ = 4 * (thetaRootSecondMomentScalar n * L.pairing x y) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hxy
  exact mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) hfour

/-- The rank-24 route supplies the complete residual theta input. -/
theorem thetaRootSecondMoment_of_evenNeighbor24
    (hNeighbor : EvenNeighbor24Input)
    (h24 : EvenUnimodular24RootScalarInput) :
    ThetaRootSecondMomentInput := by
  intro n hnlo hnhi L hfree
  exact rootSecondMoment_of_evenNeighbor24 h24 hnlo hnhi L
    (hNeighbor n hnlo hnhi L hfree).some

end Lattice
end SRG266
