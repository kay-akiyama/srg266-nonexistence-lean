/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.PDTransport
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The standard even neighbour

This file develops the abstract index-two construction used to stabilize an
odd unimodular lattice to an even unimodular lattice.  It is stated inside a
rational quadratic space, matching the project's existing dual-lattice and
basis-transport infrastructure.

For an integral self-dual lattice `M` and a characteristic vector `w in M`,
write

`M0 = {x in M | <w,x> is even}`.

If `<w,w>` is divisible by eight, the standard even neighbour is

`M0 + Z * (w/2)`.

The first half of the file proves finite generation, full rank, integrality
and evenness directly from this presentation.  The second half proves
self-duality from one vector pairing oddly with `w`; this is the primitive
condition automatically supplied by any standard `Z` summand.
-/

namespace SRG266.Lattice

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

/-- A rational number is an even integer. -/
def IsEvenInteger (q : ℚ) : Prop :=
  ∃ a : ℤ, q = ((2 * a : ℤ) : ℚ)

theorem isEvenInteger_zero : IsEvenInteger 0 := ⟨0, by norm_num⟩

theorem IsEvenInteger.add {a b : ℚ} (ha : IsEvenInteger a) (hb : IsEvenInteger b) :
    IsEvenInteger (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨x + y, ?_⟩
  push_cast
  ring

theorem IsEvenInteger.neg {a : ℚ} (ha : IsEvenInteger a) : IsEvenInteger (-a) := by
  obtain ⟨x, rfl⟩ := ha
  refine ⟨-x, ?_⟩
  push_cast
  ring

theorem IsEvenInteger.sub {a b : ℚ} (ha : IsEvenInteger a) (hb : IsEvenInteger b) :
    IsEvenInteger (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem IsEvenInteger.zsmul {a : ℚ} (ha : IsEvenInteger a) (z : ℤ) :
    IsEvenInteger (z • a) := by
  obtain ⟨x, rfl⟩ := ha
  refine ⟨z * x, ?_⟩
  change (z : ℚ) * ((2 * x : ℤ) : ℚ) = ((2 * (z * x) : ℤ) : ℚ)
  push_cast
  ring

/-- The index-two sublattice cut out by even pairing with `w`. -/
def characteristicEvenPart (F : LinearMap.BilinForm ℚ X)
    (M : Submodule ℤ X) (w : X) : Submodule ℤ X where
  carrier := {x | x ∈ M ∧ IsEvenInteger (F w x)}
  zero_mem' := ⟨M.zero_mem, by rw [map_zero]; exact isEvenInteger_zero⟩
  add_mem' := by
    rintro x y ⟨hx, hxw⟩ ⟨hy, hyw⟩
    refine ⟨M.add_mem hx hy, ?_⟩
    rw [map_add]
    exact hxw.add hyw
  smul_mem' := by
    rintro z x ⟨hx, hxw⟩
    refine ⟨M.smul_mem z hx, ?_⟩
    rw [map_zsmul]
    exact hxw.zsmul z

@[simp]
theorem mem_characteristicEvenPart {F : LinearMap.BilinForm ℚ X}
    {M : Submodule ℤ X} {w x : X} :
    x ∈ characteristicEvenPart F M w ↔ x ∈ M ∧ IsEvenInteger (F w x) :=
  Iff.rfl

/-- Half of a vector in the ambient rational space. -/
def halfVector (w : X) : X := (1 / 2 : ℚ) • w

@[simp]
theorem two_smul_halfVector (w : X) : (2 : ℤ) • halfVector w = w := by
  rw [← Int.cast_smul_eq_zsmul ℚ]
  change (2 : ℚ) • ((1 / 2 : ℚ) • w) = w
  rw [smul_smul]
  norm_num

/-- The standard even neighbour `M0 + Z * (w/2)`. -/
def evenNeighbor (F : LinearMap.BilinForm ℚ X) (M : Submodule ℤ X) (w : X) :
    Submodule ℤ X :=
  characteristicEvenPart F M w ⊔ Submodule.span ℤ {halfVector w}

/-- Every vector of the standard neighbour has an explicit even-part plus
integer half-characteristic decomposition. -/
theorem mem_evenNeighbor_iff {F : LinearMap.BilinForm ℚ X}
    {M : Submodule ℤ X} {w z : X} :
    z ∈ evenNeighbor F M w ↔
      ∃ x ∈ characteristicEvenPart F M w, ∃ a : ℤ,
        x + a • halfVector w = z := by
  rw [evenNeighbor, Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨x, hx, a, by rw [ha]; exact hxy⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨x, hx, a • halfVector w,
      Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, rfl⟩

theorem characteristicEvenPart_le {F : LinearMap.BilinForm ℚ X}
    {M : Submodule ℤ X} {w : X} : characteristicEvenPart F M w ≤ M :=
  fun _ hx => hx.1

theorem halfVector_mem_evenNeighbor (F : LinearMap.BilinForm ℚ X)
    (M : Submodule ℤ X) (w : X) :
    halfVector w ∈ evenNeighbor F M w :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem characteristicEvenPart_le_evenNeighbor (F : LinearMap.BilinForm ℚ X)
    (M : Submodule ℤ X) (w : X) :
    characteristicEvenPart F M w ≤ evenNeighbor F M w :=
  le_sup_left

/-- Twice every vector of `M` lies in the even part. -/
theorem two_smul_mem_characteristicEvenPart
    {F : LinearMap.BilinForm ℚ X} {M : Submodule ℤ X} {w x : X}
    (hx : x ∈ M) (hwx : F w x ∈ (1 : Submodule ℤ ℚ)) :
    (2 : ℤ) • x ∈ characteristicEvenPart F M w := by
  refine ⟨M.smul_mem 2 hx, ?_⟩
  obtain ⟨a, ha⟩ := mem_one_iff.mp hwx
  refine ⟨a, ?_⟩
  rw [map_zsmul, ← ha]
  norm_num

/-- The even neighbour spans the same rational space as `M`. -/
theorem evenNeighbor_spans {F : LinearMap.BilinForm ℚ X} {M : Submodule ℤ X}
    {w : X} (hM : IsLattice ℚ M) (hwdual : w ∈ F.dualSubmodule M) :
    Submodule.span ℚ ((evenNeighbor F M w : Submodule ℤ X) : Set X) = ⊤ := by
  apply top_unique
  rw [← hM.spans]
  apply Submodule.span_le.mpr
  intro x hx
  have h2 : (2 : ℤ) • x ∈ characteristicEvenPart F M w :=
    two_smul_mem_characteristicEvenPart hx (hwdual x hx)
  have h2H : (2 : ℤ) • x ∈ evenNeighbor F M w :=
    characteristicEvenPart_le_evenNeighbor F M w h2
  have hhalf : x = (1 / 2 : ℚ) • ((2 : ℤ) • x) := by
    rw [← Int.cast_smul_eq_zsmul ℚ]
    change x = (1 / 2 : ℚ) • ((2 : ℚ) • x)
    rw [smul_smul]
    norm_num
  rw [hhalf]
  exact (Submodule.span ℚ ((evenNeighbor F M w : Submodule ℤ X) : Set X)).smul_mem
    (1 / 2 : ℚ) (Submodule.subset_span h2H)

/-- The even neighbour is a full lattice. -/
theorem evenNeighbor_isLattice {F : LinearMap.BilinForm ℚ X} {M : Submodule ℤ X}
    {w : X} (hM : IsLattice ℚ M) (hwdual : w ∈ F.dualSubmodule M) :
    IsLattice ℚ (evenNeighbor F M w) := by
  refine ⟨Submodule.FG.sup (hM.fg.of_le characteristicEvenPart_le)
    ⟨{halfVector w}, by simp⟩, ?_⟩
  exact evenNeighbor_spans hM hwdual

/-- A characteristic vector, phrased in the rational presentation. -/
def IsCharacteristicIn (F : LinearMap.BilinForm ℚ X)
    (M : Submodule ℤ X) (w : X) : Prop :=
  ∀ x ∈ M, IsEvenInteger (F x x - F w x)

/-- Divisibility of the characteristic norm by eight. -/
def NormDivisibleByEight (F : LinearMap.BilinForm ℚ X) (w : X) : Prop :=
  ∃ a : ℤ, F w w = ((8 * a : ℤ) : ℚ)

/-- A vector of the even part has even norm. -/
theorem characteristicEvenPart_evenNorm
    {F : LinearMap.BilinForm ℚ X} {M : Submodule ℤ X} {w x : X}
    (hchar : IsCharacteristicIn F M w)
    (hx : x ∈ characteristicEvenPart F M w) : IsEvenInteger (F x x) := by
  have hd := hchar x hx.1
  have hw := hx.2
  have : F x x = (F x x - F w x) + F w x := by ring
  rw [this]
  exact hd.add hw

/-- The glue vector `w/2` has even norm. -/
theorem halfVector_evenNorm {F : LinearMap.BilinForm ℚ X} {w : X}
    (hw8 : NormDivisibleByEight F w) :
    IsEvenInteger (F (halfVector w) (halfVector w)) := by
  obtain ⟨a, ha⟩ := hw8
  refine ⟨a, ?_⟩
  simp only [halfVector, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [ha]
  push_cast
  ring

/-- The glue vector pairs integrally with the even part. -/
theorem characteristicEvenPart_pair_half_integral
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    {M : Submodule ℤ X} {w x : X}
    (hx : x ∈ characteristicEvenPart F M w) :
    F x (halfVector w) ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨a, ha⟩ := hx.2
  apply mem_one_iff.mpr
  refine ⟨a, ?_⟩
  simp only [halfVector, map_smul, smul_eq_mul]
  rw [hsymm.eq x w, ha]
  push_cast
  ring

/-- The standard even neighbour is integral. -/
theorem evenNeighbor_isIntegral
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    {M : Submodule ℤ X} {w : X}
    (hself : F.dualSubmodule M = M)
    (hw8 : NormDivisibleByEight F w) :
    IsIntegral F (evenNeighbor F M w) := by
  apply isIntegral_sup_span hsymm
  · intro x hx y hy
    exact (le_of_eq hself.symm) hx.1 y hy.1
  · intro x hx _ hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    exact characteristicEvenPart_pair_half_integral hsymm hx
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx
    subst hy
    obtain ⟨a, ha⟩ := halfVector_evenNorm hw8
    exact mem_one_iff.mpr ⟨2 * a, ha.symm⟩

/-- The vectors of even norm for an integral symmetric rational lattice form
a `Z`-submodule. -/
def evenNormSubmodule (F : LinearMap.BilinForm ℚ X) (hsymm : F.IsSymm)
    (P : Submodule ℤ X) (hP : IsIntegral F P) : Submodule ℤ X where
  carrier := {x | x ∈ P ∧ IsEvenInteger (F x x)}
  zero_mem' := ⟨P.zero_mem, by rw [map_zero]; exact isEvenInteger_zero⟩
  add_mem' := by
    rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
    refine ⟨P.add_mem hx hy, ?_⟩
    have hxy : F x y ∈ (1 : Submodule ℤ ℚ) := hP hx y hy
    obtain ⟨a, ha⟩ := mem_one_iff.mp hxy
    have hcross : IsEvenInteger (F x y + F y x) := by
      refine ⟨a, ?_⟩
      rw [hsymm.eq y x, ← ha]
      norm_cast
      ring
    have heq : F (x + y) (x + y) = F x x + F y y + (F x y + F y x) := by
      simp only [map_add, LinearMap.add_apply]
      ring
    rw [heq]
    exact (hxx.add hyy).add hcross
  smul_mem' := by
    rintro z x ⟨hx, hxx⟩
    refine ⟨P.smul_mem z hx, ?_⟩
    simp only [map_zsmul, LinearMap.smul_apply]
    obtain ⟨a, ha⟩ := hxx
    refine ⟨z ^ 2 * a, ?_⟩
    rw [ha]
    push_cast
    ring

/-- Every vector of the standard neighbour has even norm. -/
theorem evenNeighbor_evenNorm
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    {M : Submodule ℤ X} {w : X}
    (hself : F.dualSubmodule M = M)
    (hchar : IsCharacteristicIn F M w)
    (hw8 : NormDivisibleByEight F w) :
    ∀ x ∈ evenNeighbor F M w, IsEvenInteger (F x x) := by
  have hint := evenNeighbor_isIntegral hsymm hself hw8
  let E := evenNormSubmodule F hsymm (evenNeighbor F M w) hint
  have hleft : characteristicEvenPart F M w ≤ E := by
    intro x hx
    exact ⟨characteristicEvenPart_le_evenNeighbor F M w hx,
      characteristicEvenPart_evenNorm hchar hx⟩
  have hright : Submodule.span ℤ {halfVector w} ≤ E := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨halfVector_mem_evenNeighbor F M w, halfVector_evenNorm hw8⟩
  intro x hx
  exact (sup_le hleft hright hx).2

/-! ## Self-duality -/

/-- Pairing integrally with `w/2` forces even pairing with `w`. -/
theorem even_pairing_of_pair_half_integral
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm) {w z : X}
    (h : F z (halfVector w) ∈ (1 : Submodule ℤ ℚ)) :
    IsEvenInteger (F w z) := by
  obtain ⟨a, ha⟩ := mem_one_iff.mp h
  refine ⟨a, ?_⟩
  simp only [halfVector, map_smul, smul_eq_mul] at ha
  rw [hsymm.eq w z]
  push_cast at ha ⊢
  linarith

/-- If `y` pairs evenly with the kernel of the characteristic parity map,
then, modulo twice the original self-dual lattice, `y` is a multiple of the
characteristic vector.

The proof uses a vector `p` with `<w,p> = 1`.  For arbitrary `x`, the vector
`x - <w,x> p` lies in the even kernel. -/
theorem half_sub_smul_mem_of_even_on_characteristicPart
    {F : LinearMap.BilinForm ℚ X} (_hsymm : F.IsSymm)
    {M : Submodule ℤ X} {w p y : X}
    (hself : F.dualSubmodule M = M)
    (hwM : w ∈ M) (hpM : p ∈ M) (hwp : F w p = 1)
    (hyM : y ∈ M)
    (hyEven : ∀ x ∈ characteristicEvenPart F M w,
      IsEvenInteger (F y x)) :
    ∃ a : ℤ, ((a : ℚ) = F y p) ∧
      halfVector (y - a • w) ∈ M := by
  have hMint : IsIntegral F M := le_of_eq hself.symm
  obtain ⟨a, ha⟩ := mem_one_iff.mp (hMint hyM p hpM)
  refine ⟨a, ha, ?_⟩
  rw [← hself]
  intro x hx
  obtain ⟨b, hb⟩ := mem_one_iff.mp (hMint hwM x hx)
  let x0 : X := x - b • p
  have hx0M : x0 ∈ M := M.sub_mem hx (M.smul_mem b hpM)
  have hx0w : F w x0 = 0 := by
    dsimp only [x0]
    rw [map_sub, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, ← hb, hwp]
    norm_num
  have hx0 : x0 ∈ characteristicEvenPart F M w :=
    ⟨hx0M, by rw [hx0w]; exact isEvenInteger_zero⟩
  obtain ⟨d, hd⟩ := hyEven x0 hx0
  apply mem_one_iff.mpr
  refine ⟨d, ?_⟩
  have hform : F y x0 = F (y - a • w) x := by
    dsimp only [x0]
    simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    simp only [← Int.cast_smul_eq_zsmul ℚ]
    rw [← ha, ← hb]
    ring
  simp only [halfVector, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← hform, hd]
  push_cast
  ring

/-- **Self-duality of the standard even neighbour.**

The primitive witness `p` is intentionally an explicit hypothesis.  In the
rank-24 stabilization it is the first basis vector of the added standard
`Z`-summand, so `<w,p> = 1` definitionally. -/
theorem evenNeighbor_dual_eq_self
    {F : LinearMap.BilinForm ℚ X} (hsymm : F.IsSymm)
    {M : Submodule ℤ X} {w p : X}
    (hself : F.dualSubmodule M = M)
    (hwM : w ∈ M) (hpM : p ∈ M) (hwp : F w p = 1)
    (hw8 : NormDivisibleByEight F w) :
    F.dualSubmodule (evenNeighbor F M w) = evenNeighbor F M w := by
  letI : IsAddTorsionFree X := IsAddTorsionFree.of_module_rat X
  apply le_antisymm
  · intro z hz
    have hMint : IsIntegral F M := le_of_eq hself.symm
    have hwdual : w ∈ F.dualSubmodule M := by rw [hself]; exact hwM
    have h2dual : (2 : ℤ) • z ∈ F.dualSubmodule M := by
      intro x hx
      have h2x : (2 : ℤ) • x ∈ characteristicEvenPart F M w :=
        two_smul_mem_characteristicEvenPart hx (hwdual x hx)
      have hz2x := hz ((2 : ℤ) • x)
        (characteristicEvenPart_le_evenNeighbor F M w h2x)
      simpa only [map_zsmul, LinearMap.smul_apply] using hz2x
    have h2M : (2 : ℤ) • z ∈ M := by rw [← hself]; exact h2dual
    let y : X := (2 : ℤ) • z
    have hyM : y ∈ M := h2M
    have hyEven : ∀ x ∈ characteristicEvenPart F M w,
        IsEvenInteger (F y x) := by
      intro x hx
      have hzx := hz x (characteristicEvenPart_le_evenNeighbor F M w hx)
      obtain ⟨d, hd⟩ := mem_one_iff.mp hzx
      refine ⟨d, ?_⟩
      dsimp only [y]
      simp only [map_zsmul, LinearMap.smul_apply]
      rw [← hd]
      norm_num
    obtain ⟨a, ha, huM⟩ :=
      half_sub_smul_mem_of_even_on_characteristicPart hsymm hself hwM hpM hwp hyM hyEven
    let u : X := halfVector (y - a • w)
    have hu : u ∈ M := huM
    have hydecomp : y = a • w + (2 : ℤ) • u := by
      have h2u : (2 : ℤ) • u = y - a • w := by
        dsimp only [u]
        exact two_smul_halfVector (y - a • w)
      calc
        y = a • w + (y - a • w) := by abel
        _ = a • w + (2 : ℤ) • u := by rw [h2u]
    have hwzEven : IsEvenInteger (F w z) := by
      apply even_pairing_of_pair_half_integral hsymm
      exact hz (halfVector w) (halfVector_mem_evenNeighbor F M w)
    rcases Int.even_or_odd a with haEven | haOdd
    · obtain ⟨k, hk⟩ := haEven
      have hzEq : z = k • w + u := by
        apply zsmul_right_injective (show (2 : ℤ) ≠ 0 by norm_num)
        calc
          (2 : ℤ) • z = y := rfl
          _ = a • w + (2 : ℤ) • u := hydecomp
          _ = (k + k) • w + (2 : ℤ) • u := by rw [hk]
          _ = (2 : ℤ) • (k • w + u) := by module
      have hzM : z ∈ M := by
        rw [hzEq]
        exact M.add_mem (M.smul_mem k hwM) hu
      have hz0 : z ∈ characteristicEvenPart F M w := ⟨hzM, hwzEven⟩
      exact characteristicEvenPart_le_evenNeighbor F M w hz0
    · obtain ⟨k, hk⟩ := haOdd
      have hzEq : z = halfVector w + (k • w + u) := by
        apply zsmul_right_injective (show (2 : ℤ) ≠ 0 by norm_num)
        calc
          (2 : ℤ) • z = y := rfl
          _ = a • w + (2 : ℤ) • u := hydecomp
          _ = (2 * k + 1) • w + (2 : ℤ) • u := by rw [hk]
          _ = (2 : ℤ) • (halfVector w + (k • w + u)) := by
            have hhalf : (2 : ℤ) • halfVector w = w := two_smul_halfVector w
            rw [smul_add, smul_add, hhalf]
            rw [smul_smul]
            have hcoef : (2 * k + 1 : ℤ) = 1 + 2 * k := by ring
            rw [hcoef, add_smul, one_smul]
            exact add_assoc w ((2 * k) • w) ((2 : ℤ) • u)
      let v : X := k • w + u
      have hvM : v ∈ M := M.add_mem (M.smul_mem k hwM) hu
      have hhalfNorm : IsEvenInteger (F w (halfVector w)) := by
        obtain ⟨d, hd⟩ := hw8
        refine ⟨2 * d, ?_⟩
        simp only [halfVector, map_smul, smul_eq_mul]
        rw [hd]
        push_cast
        ring
      have hvEven : IsEvenInteger (F w v) := by
        have hsum : F w z = F w (halfVector w) + F w v := by
          rw [hzEq, map_add]
        rw [hsum] at hwzEven
        simpa only [add_sub_cancel_left] using hwzEven.sub hhalfNorm
      have hv0 : v ∈ characteristicEvenPart F M w := ⟨hvM, hvEven⟩
      rw [hzEq]
      exact (evenNeighbor F M w).add_mem
        (halfVector_mem_evenNeighbor F M w)
        (characteristicEvenPart_le_evenNeighbor F M w hv0)
  · exact evenNeighbor_isIntegral hsymm hself hw8

end SRG266.Lattice
