/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import SRG266.Lattice.Overlattice

/-!
# The discriminant group of a maximal integral overlattice

This module is the second half of the abstract overlattice theory begun in
`SRG266/Lattice/Overlattice.lean`.  Throughout, `B` is a symmetric nondegenerate
bilinear form on a `ℚ`-vector space `W` and `Ñ ⊆ W` is a *maximal* integral
lattice, so that `Ñ ⊆ Ñ^∨` and no strictly larger `ℤ`-submodule of `W` carries
integral values.

For a prime `p`, the `p`-torsion part `T_p = {y ∈ Ñ^∨ : p • y ∈ Ñ}`
(`SRG266.Lattice.torsionPart`) gives the **discriminant
group** `D_p = T_p / Ñ`, an elementary abelian `p`-group, that is, a vector space
over `ZMod p`.  It carries the **discriminant pairing**

`β_p(ȳ, ȳ') = (p ⟨y, y'⟩ : ℤ) mod p`,

which is well defined because `p ⟨y, y'⟩` is an integer for `y, y' ∈ T_p` and
changes by a multiple of `p` when a representative is shifted by `Ñ`.

The two main results are:

* `disc_dim_le_two` — `dim_{ZMod p} D_p ≤ 2` at a maximal overlattice.  Three
  independent classes would give a homogeneous quadratic form in three variables
  over `ZMod p`; **Chevalley–Warning** (`char_dvd_card_solutions`) produces a
  nontrivial zero of it, and the corresponding vector `y = ∑ aᵢ yᵢ` satisfies
  `⟨y, y⟩ ∈ ℤ` and `y ∉ Ñ`, so `Ñ + ℤy` would be a strictly larger integral
  lattice.
* `exists_orthogonal_glue_basis` — *Corollary S*: choosing a `β_p`-orthogonal basis of `D_p`
  (mathlib's `exists_orthogonal_basis`, legitimate because `2` is invertible in
  `ZMod p` for odd `p`) yields at most two vectors `y₁, …, y_a ∈ T_p` with

  - `T_p = Ñ + ∑ᵢ ℤ · yᵢ`,
  - `⟨yᵢ, yⱼ⟩ ∈ ℤ` for `i ≠ j`,
  - `p ⟨yᵢ, yᵢ⟩ = mᵢ` with `p ∤ mᵢ` — that is, `⟨yᵢ, yᵢ⟩ ≡ uᵢ / p` with `uᵢ` a
    unit of `ZMod p`,
  - and the `yᵢ` are independent modulo `Ñ`.

  This is the whole discriminant datum of a maximal overlattice: for
  `Ñ^∨ = T₃ + T₅` (the case of the local Gram lattice) it is a tuple of at most
  two units mod `3` and at most two units mod `5`.  `GlueBasis.exists_unit_diag`
  exhibits the diagonal entries as units of `ZMod p`, and
  `dual_eq_sup_span_glue` assembles two glue bases at coprime primes into the
  single statement `Ñ^∨ = Ñ + ∑ᵢ ℤ·yᵢ`.

Nondegeneracy of `β_p` (`discPairing_nondegenerate`) is what forces the diagonal
entries `uᵢ` to be units; it is proved from the double-dual identity
`(Ñ^∨)^∨ = Ñ` together with the coprime splitting `Ñ^∨ = T_p + T_q` of
`dual_eq_torsionPart_sup`.

The main results are `disc_dim_le_two`, `discPairing_nondegenerate`, and
`GlueBasis` together with `exists_orthogonal_glue_basis`.  Everything is stated for an
abstract `(W, B)`; nothing refers to a graph.
-/

namespace SRG266.Lattice

section Discriminant

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {Ñ : Submodule ℤ W} {p : ℕ}

/-! ### Rationals that happen to be integers

`(1 : Submodule ℤ ℚ)` is the image of `ℤ` in `ℚ`; membership in it is the
integrality condition used by `LinearMap.BilinForm.dualSubmodule`. -/

theorem mem_one_iff {x : ℚ} : x ∈ (1 : Submodule ℤ ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x :=
  ⟨fun h => by
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
      exact ⟨n, by simpa using hn⟩,
   fun h => by
      obtain ⟨n, hn⟩ := h
      exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩⟩

theorem intCast_mem_one (n : ℤ) : ((n : ℚ)) ∈ (1 : Submodule ℤ ℚ) :=
  mem_one_iff.mpr ⟨n, rfl⟩

/-- If two coprime multiples of a rational number are integers, so is the number
itself. -/
theorem mem_one_of_coprime {a b : ℤ} (hab : IsCoprime a b) {x : ℚ}
    (ha : (a : ℚ) * x ∈ (1 : Submodule ℤ ℚ)) (hb : (b : ℚ) * x ∈ (1 : Submodule ℤ ℚ)) :
    x ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨u, v, huv⟩ := hab
  have huv' : ((u : ℚ)) * (a : ℚ) + (v : ℚ) * (b : ℚ) = 1 := by
    have : ((u * a + v * b : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by rw [huv]
    push_cast at this
    linarith
  have hx : x = u • ((a : ℚ) * x) + v • ((b : ℚ) * x) := by
    simp only [zsmul_eq_mul]
    linear_combination (-x) * huv'
  rw [hx]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

/-! ### The integer `p ⟨y, y'⟩` -/

variable (B p) in
/-- The integer `p ⟨y, y'⟩`, read off as the numerator of the rational number
`p ⟨y, y'⟩`.  It is genuinely `p ⟨y, y'⟩` whenever that number is an integer,
which is the case for `y ∈ Ñ^∨` and `p • y' ∈ Ñ` (`discNum_cast`). -/
def discNum (y y' : W) : ℤ := ((p : ℚ) * B y y').num

/-- A rational number known to equal an integer pins down `discNum`. -/
theorem discNum_eq_of_cast {y y' : W} {n : ℤ} (h : (n : ℚ) = (p : ℚ) * B y y') :
    discNum B p y y' = n := by
  simp [discNum, ← h]

/-- **`discNum` computes `p ⟨y, y'⟩`.**  The pairing of a dual vector with a
vector whose `p`-th multiple lies in the lattice is `p`-integral. -/
theorem discNum_cast {y y' : W} (hy : y ∈ B.dualSubmodule Ñ) (hy' : (p : ℤ) • y' ∈ Ñ) :
    ((discNum B p y y' : ℤ) : ℚ) = (p : ℚ) * B y y' := by
  have h := hy _ hy'
  rw [map_zsmul, zsmul_eq_mul] at h
  push_cast at h
  obtain ⟨n, hn⟩ := mem_one_iff.mp h
  rw [discNum_eq_of_cast (B := B) (p := p) hn, hn]

theorem discNum_symm (hsymm : B.IsSymm) (y y' : W) :
    discNum B p y y' = discNum B p y' y := by
  simp [discNum, hsymm.eq y y']

theorem discNum_add_left {y₁ y₂ y' : W} (h₁ : y₁ ∈ B.dualSubmodule Ñ)
    (h₂ : y₂ ∈ B.dualSubmodule Ñ) (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p (y₁ + y₂) y' = discNum B p y₁ y' + discNum B p y₂ y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast h₁ hy', discNum_cast h₂ hy', map_add, LinearMap.add_apply]
  ring

theorem discNum_zsmul_left (c : ℤ) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p (c • y) y' = c * discNum B p y y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy hy', map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  ring

theorem discNum_add_right {y y₁' y₂' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (h₁ : (p : ℤ) • y₁' ∈ Ñ) (h₂ : (p : ℤ) • y₂' ∈ Ñ) :
    discNum B p y (y₁' + y₂') = discNum B p y y₁' + discNum B p y y₂' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy h₁, discNum_cast hy h₂, map_add]
  ring

theorem discNum_zsmul_right (c : ℤ) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) :
    discNum B p y (c • y') = c * discNum B p y y' := by
  refine discNum_eq_of_cast ?_
  push_cast
  rw [discNum_cast hy hy', map_zsmul, zsmul_eq_mul]
  ring

/-- A dual vector pairs integrally with the lattice, so `p ⟨y, y'⟩ ≡ 0 (mod p)`
as soon as the second argument lies in `Ñ`. -/
theorem dvd_discNum_of_mem {y y' : W} (hy : y ∈ B.dualSubmodule Ñ) (hy' : y' ∈ Ñ) :
    (p : ℤ) ∣ discNum B p y y' := by
  obtain ⟨n, hn⟩ := mem_one_iff.mp (hy _ hy')
  exact ⟨n, discNum_eq_of_cast (by rw [← hn]; push_cast; ring)⟩

/-- The converse bookkeeping step: `p ∣ p ⟨y, y'⟩` means `⟨y, y'⟩` is an
integer. -/
theorem mem_one_of_dvd_discNum (hp : p ≠ 0) {y y' : W} (hy : y ∈ B.dualSubmodule Ñ)
    (hy' : (p : ℤ) • y' ∈ Ñ) (h : (p : ℤ) ∣ discNum B p y y') :
    B y y' ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨m, hm⟩ := h
  have hc := discNum_cast hy hy'
  rw [hm] at hc
  push_cast at hc
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp
  exact mem_one_iff.mpr ⟨m, mul_left_cancel₀ hp0 hc⟩

/-! ### The discriminant group -/

variable (B Ñ p) in
/-- The **discriminant group** `D_p = T_p / Ñ` at the prime `p`. -/
abbrev discGroup : Type _ :=
  torsionPart B Ñ p ⧸ Ñ.comap (torsionPart B Ñ p).subtype

theorem discGroup_nsmul_eq_zero (q : discGroup B Ñ p) : p • q = 0 :=
  quotient_nsmul_eq_zero (fun _ hy => (mem_torsionPart.mp hy).2) q

/-- The discriminant group is killed by `p`, hence is a `ZMod p`-module. -/
instance discGroupZModModule : Module (ZMod p) (discGroup B Ñ p) :=
  AddCommGroup.zmodModule (discGroup_nsmul_eq_zero (B := B) (Ñ := Ñ) (p := p))

theorem torsion_mem_dual (y : torsionPart B Ñ p) : (y : W) ∈ B.dualSubmodule Ñ :=
  (mem_torsionPart.mp y.2).1

theorem torsion_zsmul_mem (y : torsionPart B Ñ p) : (p : ℤ) • (y : W) ∈ Ñ :=
  (mem_torsionPart.mp y.2).2

theorem discGroup_mk_eq_zero_iff {y : torsionPart B Ñ p} :
    (Submodule.Quotient.mk y : discGroup B Ñ p) = 0 ↔ (y : W) ∈ Ñ := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact Iff.rfl

/-- The discriminant group is a finite-dimensional `ZMod p`-vector space. -/
theorem discGroup_finite (hnd : B.Nondegenerate) (hN : IsLattice ℚ Ñ) :
    Module.Finite (ZMod p) (discGroup B Ñ p) := by
  classical
  have hDfg : (B.dualSubmodule Ñ).FG := (dual_isLattice B hN hnd).fg
  haveI : IsNoetherian ℤ (B.dualSubmodule Ñ) :=
    isNoetherian_of_fg_of_noetherian _ hDfg
  have hle : torsionPart B Ñ p ≤ B.dualSubmodule Ñ := torsionPart_le_dual Ñ p
  have hTfg : (torsionPart B Ñ p).FG := by
    have hcomap := IsNoetherian.noetherian
      ((torsionPart B Ñ p).comap (B.dualSubmodule Ñ).subtype)
    have hmap := hcomap.map (B.dualSubmodule Ñ).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at hmap
  haveI : Module.Finite ℤ (torsionPart B Ñ p) := Module.Finite.iff_fg.mpr hTfg
  haveI : Module.Finite ℤ (discGroup B Ñ p) := Module.Finite.quotient ℤ _
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := discGroup B Ñ p)
  refine ⟨⟨S, ?_⟩⟩
  refine top_unique fun q _ => ?_
  have hq : q ∈ Submodule.span ℤ (S : Set (discGroup B Ñ p)) := by
    rw [hS]; exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · exact fun y hy => Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · exact fun y z _ _ hy hz => Submodule.add_mem _ hy hz
  · intro a y _ hy
    rw [← Int.cast_smul_eq_zsmul (ZMod p) a y]
    exact Submodule.smul_mem _ _ hy

/-! ### The discriminant pairing -/

variable (B Ñ p) in
/-- The pairing `(y, y') ↦ p ⟨y, y'⟩ mod p` on the `p`-torsion part, before
descending to the discriminant group. -/
def torsionBilin :
    torsionPart B Ñ p →ₗ[ℤ] torsionPart B Ñ p →ₗ[ℤ] ZMod p :=
  LinearMap.mk₂ ℤ (fun y y' => ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p))
    (by
      intro y₁ y₂ y'
      rw [show ((y₁ + y₂ : torsionPart B Ñ p) : W) = (y₁ : W) + (y₂ : W) from rfl,
        discNum_add_left (torsion_mem_dual y₁) (torsion_mem_dual y₂) (torsion_zsmul_mem y')]
      push_cast
      ring)
    (by
      intro c y y'
      rw [show ((c • y : torsionPart B Ñ p) : W) = c • (y : W) from rfl,
        discNum_zsmul_left c (torsion_mem_dual y) (torsion_zsmul_mem y')]
      rw [zsmul_eq_mul]
      push_cast
      ring)
    (by
      intro y y₁' y₂'
      rw [show ((y₁' + y₂' : torsionPart B Ñ p) : W) = (y₁' : W) + (y₂' : W) from rfl,
        discNum_add_right (torsion_mem_dual y) (torsion_zsmul_mem y₁') (torsion_zsmul_mem y₂')]
      push_cast
      ring)
    (by
      intro c y y'
      rw [show ((c • y' : torsionPart B Ñ p) : W) = c • (y' : W) from rfl,
        discNum_zsmul_right c (torsion_mem_dual y) (torsion_zsmul_mem y')]
      rw [zsmul_eq_mul]
      push_cast
      ring)

@[simp]
theorem torsionBilin_apply (y y' : torsionPart B Ñ p) :
    torsionBilin B Ñ p y y' = ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

/-- The pairing kills `Ñ` in its second argument. -/
theorem torsionBilin_ker_right (y : torsionPart B Ñ p) :
    Ñ.comap (torsionPart B Ñ p).subtype ≤ LinearMap.ker (torsionBilin B Ñ p y) := by
  intro z hz
  have hzÑ : (z : W) ∈ Ñ := hz
  simp only [LinearMap.mem_ker, torsionBilin_apply]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_discNum_of_mem (torsion_mem_dual y) hzÑ)

variable (B Ñ p) in
/-- The pairing with a fixed first argument, descended to the discriminant
group. -/
def discPairingRight (y : torsionPart B Ñ p) : discGroup B Ñ p →ₗ[ℤ] ZMod p :=
  Submodule.liftQ _ (torsionBilin B Ñ p y) (torsionBilin_ker_right y)

@[simp]
theorem discPairingRight_mk (y y' : torsionPart B Ñ p) :
    discPairingRight B Ñ p y (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

variable (B Ñ p) in
/-- The pairing, descended in its second argument only. -/
def discPairingAux : torsionPart B Ñ p →ₗ[ℤ] discGroup B Ñ p →ₗ[ℤ] ZMod p where
  toFun := discPairingRight B Ñ p
  map_add' := by
    intro y₁ y₂
    refine LinearMap.ext fun d => ?_
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show torsionBilin B Ñ p (y₁ + y₂) y' =
      torsionBilin B Ñ p y₁ y' + torsionBilin B Ñ p y₂ y'
    rw [map_add, LinearMap.add_apply]
  map_smul' := by
    intro c y
    refine LinearMap.ext fun d => ?_
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show torsionBilin B Ñ p (c • y) y' = c • torsionBilin B Ñ p y y'
    rw [map_smul, LinearMap.smul_apply]

/-- With symmetry available the pairing also kills `Ñ` in its first argument. -/
theorem discPairingAux_ker (hsymm : B.IsSymm) :
    Ñ.comap (torsionPart B Ñ p).subtype ≤ LinearMap.ker (discPairingAux B Ñ p) := by
  intro z hz
  have hzÑ : (z : W) ∈ Ñ := hz
  refine LinearMap.mem_ker.mpr (LinearMap.ext fun d => ?_)
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d
  show ((discNum B p (z : W) (y' : W) : ℤ) : ZMod p) = 0
  rw [discNum_symm hsymm]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_discNum_of_mem (torsion_mem_dual y') hzÑ)

variable (B Ñ p) in
/-- The discriminant pairing as a `ℤ`-bilinear map on `D_p`. -/
def discPairingInt (hsymm : B.IsSymm) :
    discGroup B Ñ p →ₗ[ℤ] discGroup B Ñ p →ₗ[ℤ] ZMod p :=
  Submodule.liftQ _ (discPairingAux B Ñ p) (discPairingAux_ker hsymm)

@[simp]
theorem discPairingInt_mk (hsymm : B.IsSymm) (y y' : torsionPart B Ñ p) :
    discPairingInt B Ñ p hsymm (Submodule.Quotient.mk y) (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

variable (B Ñ p) in
/-- **The discriminant pairing** `β_p : D_p × D_p → ZMod p`.

A `ℤ`-bilinear form on a `ZMod p`-module with values in `ZMod p` is
automatically `ZMod p`-bilinear, because every scalar of `ZMod p` is the image of
an integer. -/
def discPairing (hsymm : B.IsSymm) : LinearMap.BilinForm (ZMod p) (discGroup B Ñ p) where
  toFun d :=
    { toFun := fun d' => discPairingInt B Ñ p hsymm d d'
      map_add' := fun d₁ d₂ => by simp
      map_smul' := fun c d' => by
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
        simp only [RingHom.id_apply]
        rw [Int.cast_smul_eq_zsmul (ZMod p) k d', map_smul,
          Int.cast_smul_eq_zsmul (ZMod p) k _] }
  map_add' := by
    intro d₁ d₂
    refine LinearMap.ext fun d' => ?_
    simp
  map_smul' := by
    intro c d
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    refine LinearMap.ext fun d' => ?_
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Int.cast_smul_eq_zsmul (ZMod p) k d, map_smul, LinearMap.smul_apply,
      Int.cast_smul_eq_zsmul (ZMod p) k _]

@[simp]
theorem discPairing_mk (hsymm : B.IsSymm) (y y' : torsionPart B Ñ p) :
    discPairing B Ñ p hsymm (Submodule.Quotient.mk y) (Submodule.Quotient.mk y') =
      ((discNum B p (y : W) (y' : W) : ℤ) : ZMod p) := rfl

/-- **The discriminant pairing is symmetric.** -/
theorem discPairing_isSymm (hsymm : B.IsSymm) : (discPairing B Ñ p hsymm).IsSymm := by
  refine ⟨fun d d' => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ d'
  rw [discPairing_mk, discPairing_mk, discNum_symm hsymm]

/-! ### Nondegeneracy of the discriminant pairing -/

/-- **Lemma N.**  The discriminant pairing is left-separating.

If `⟨y, ·⟩` is integral on `T_p` then it is integral on all of `Ñ^∨ = T_p + T_q`:
for `z ∈ T_q` both `p ⟨y, z⟩` and `q ⟨y, z⟩` are integers, and `p`, `q` are
coprime.  So `y ∈ (Ñ^∨)^∨ = Ñ`. -/
theorem discPairing_separatingLeft (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hp : p ≠ 0) {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    (discPairing B Ñ p hsymm).SeparatingLeft := by
  intro d hd
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  rw [discGroup_mk_eq_zero_iff]
  have hyd : (y : W) ∈ B.dualSubmodule Ñ := torsion_mem_dual y
  have hcop : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hpq)
  -- integrality against the `p`-part
  have hTp : ∀ z ∈ torsionPart B Ñ p, B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
    intro z hz
    have hz0 := hd (Submodule.Quotient.mk ⟨z, hz⟩)
    rw [discPairing_mk] at hz0
    exact mem_one_of_dvd_discNum hp hyd (mem_torsionPart.mp hz).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0)
  -- integrality against the `q`-part
  have hTq : ∀ z ∈ torsionPart B Ñ q, B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
    intro z hz
    have hzd : z ∈ B.dualSubmodule Ñ := (mem_torsionPart.mp hz).1
    have hqz : (q : ℤ) • z ∈ Ñ := (mem_torsionPart.mp hz).2
    have hpy : (p : ℤ) • (y : W) ∈ Ñ := torsion_zsmul_mem y
    have hp' : ((p : ℚ)) * B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
      have h := hzd _ hpy
      rw [map_zsmul, zsmul_eq_mul] at h
      push_cast at h
      rwa [hsymm.eq z (y : W)] at h
    have hq' : ((q : ℚ)) * B (y : W) z ∈ (1 : Submodule ℤ ℚ) := by
      have h := hyd _ hqz
      rw [map_zsmul, zsmul_eq_mul] at h
      push_cast at h
      exact h
    exact mem_one_of_coprime hcop (by exact_mod_cast hp') (by exact_mod_cast hq')
  -- hence `y` lies in the double dual, which is `Ñ`
  have hdd : (y : W) ∈ B.dualSubmodule (B.dualSubmodule Ñ) := by
    intro z hz
    rw [hsplit] at hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add]
    exact Submodule.add_mem _ (hTp z₁ hz₁) (hTq z₂ hz₂)
  rwa [dual_dual B hN hnd hsymm] at hdd

/-- **Lemma N.**  The discriminant pairing is nondegenerate. -/
theorem discPairing_nondegenerate (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hp : p ≠ 0) {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    (discPairing B Ñ p hsymm).Nondegenerate :=
  ((discPairing_isSymm hsymm).isRefl.nondegenerate_iff_separatingLeft).mpr
    (discPairing_separatingLeft hsymm hnd hN hp hpq hsplit)

/-! ### The rank bound via Chevalley–Warning -/

/-- A vector of `T_p` built from an integral combination of representatives. -/
private theorem bilin_sum_sum {n : ℕ} (a : Fin n → ℤ) (y : Fin n → W) :
    B (∑ i, a i • y i) (∑ j, a j • y j) =
      ∑ i, ∑ j, ((a i * a j : ℤ) : ℚ) * B (y i) (y j) := by
  have key : ∀ w : W, B w (∑ j, a j • y j) = ∑ j, ((a j : ℤ) : ℚ) * B w (y j) := by
    intro w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
  have key₂ : ∀ w : W, B (∑ i, a i • y i) w = ∑ i, ((a i : ℤ) : ℚ) * B (y i) w := by
    intro w
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  rw [key]
  simp_rw [key₂, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **Lemma R.**  At a maximal integral overlattice the discriminant group has
dimension at most two over `ZMod p`.

Three independent classes `y₁, y₂, y₃` would give the homogeneous quadratic form
`Q(X) = ∑ᵢⱼ (p ⟨yᵢ, yⱼ⟩) XᵢXⱼ` in three variables over `ZMod p`; its total degree
`2` is smaller than the number `3` of variables, so Chevalley–Warning makes the
number of its zeros divisible by `p`.  Since `0` is a zero there are at least `p`
of them, hence a nonzero one; the corresponding `y = ∑ aᵢ yᵢ` has `⟨y, y⟩ ∈ ℤ`
and lies outside `Ñ`, so `Ñ + ℤy` contradicts maximality. -/
theorem disc_dim_le_two [hp : Fact p.Prime] (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    (hN : IsLattice ℚ Ñ) (hmax : IsMaximalIntegral B Ñ) :
    Module.finrank (ZMod p) (discGroup B Ñ p) ≤ 2 := by
  classical
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  haveI : Module.Finite (ZMod p) (discGroup B Ñ p) := discGroup_finite hnd hN
  by_contra hcon
  -- three independent classes
  have h3 : 3 ≤ Module.finrank (ZMod p) (discGroup B Ñ p) := Nat.lt_of_not_le hcon
  set b := Module.finBasis (ZMod p) (discGroup B Ñ p) with hb
  set f : Fin 3 → Fin (Module.finrank (ZMod p) (discGroup B Ñ p)) :=
    fun i => ⟨i.1, lt_of_lt_of_le i.2 h3⟩ with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval := congrArg Fin.val hij
    exact Fin.ext hval
  have hv : LinearIndependent (ZMod p) (fun i => b (f i)) :=
    b.linearIndependent.comp f hfinj
  -- representatives
  choose y hy using fun i : Fin 3 => Submodule.Quotient.mk_surjective
    (Ñ.comap (torsionPart B Ñ p).subtype) (b (f i))
  set c : Fin 3 → Fin 3 → ZMod p :=
    fun i j => ((discNum B p (y i : W) (y j : W) : ℤ) : ZMod p) with hc
  -- the quadratic form and its zeros
  set Q : MvPolynomial (Fin 3) (ZMod p) :=
    ∑ i, ∑ j, MvPolynomial.C (c i j) * MvPolynomial.X i * MvPolynomial.X j with hQ
  have hdeg : Q.totalDegree < Fintype.card (Fin 3) := by
    have h2 : Q.totalDegree ≤ 2 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C (c i j) * MvPolynomial.X i).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      have h2 : (MvPolynomial.X j : MvPolynomial (Fin 3) (ZMod p)).totalDegree ≤ 1 := by
        simp [MvPolynomial.totalDegree_X]
      omega
    simpa using Nat.lt_of_le_of_lt h2 (by norm_num)
  have heval : ∀ x : Fin 3 → ZMod p,
      MvPolynomial.eval x Q = ∑ i, ∑ j, c i j * x i * x j := by
    intro x
    simp [hQ]
  have hzero : MvPolynomial.eval (0 : Fin 3 → ZMod p) Q = 0 := by
    rw [heval]
    simp
  have hcw := char_dvd_card_solutions (K := ZMod p) (σ := Fin 3) p hdeg
  have hpos : 0 < Fintype.card { x : Fin 3 → ZMod p // MvPolynomial.eval x Q = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, hzero⟩⟩
  have hcard : 1 < Fintype.card { x : Fin 3 → ZMod p // MvPolynomial.eval x Q = 0 } := by
    have hle := Nat.le_of_dvd hpos hcw
    have := hp.out.two_le
    omega
  obtain ⟨⟨x, hx⟩, hxne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, hzero⟩
  have hx0 : x ≠ 0 := fun h => hxne (Subtype.ext h)
  -- lift the solution to integers
  choose a ha using fun i : Fin 3 => ZMod.intCast_surjective (n := p) (x i)
  set z : torsionPart B Ñ p := ∑ i, a i • y i with hz
  have hzcoe : (z : W) = ∑ i, a i • (y i : W) := by
    rw [hz]
    push_cast
    rfl
  -- `z` is not in `Ñ`
  have hznot : (z : W) ∉ Ñ := by
    intro hmem
    have hmk : (Submodule.Quotient.mk z : discGroup B Ñ p) = 0 :=
      discGroup_mk_eq_zero_iff.mpr hmem
    have hsum : ∑ i, x i • b (f i) = 0 := by
      have hexp : (Submodule.Quotient.mk z : discGroup B Ñ p) = ∑ i, x i • b (f i) := by
        have hmkq : (Submodule.Quotient.mk z : discGroup B Ñ p) =
            (Ñ.comap (torsionPart B Ñ p).subtype).mkQ z := rfl
        rw [hmkq, hz, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        show a i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p) = x i • b (f i)
        rw [hy i, ← ha i, Int.cast_smul_eq_zsmul]
      rw [hexp] at hmk
      exact hmk
    have := Fintype.linearIndependent_iff.mp hv x hsum
    exact hx0 (funext this)
  -- but `⟨z, z⟩` is an integer, so `Ñ + ℤz` is integral: contradiction
  have hzz : B (z : W) (z : W) ∈ (1 : Submodule ℤ ℚ) := by
    set N : ℤ := ∑ i, ∑ j, a i * a j * discNum B p (y i : W) (y j : W) with hN'
    have hNcast : ((N : ℤ) : ℚ) = (p : ℚ) * B (z : W) (z : W) := by
      rw [hzcoe, bilin_sum_sum, hN']
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [discNum_cast (torsion_mem_dual (y i)) (torsion_zsmul_mem (y j))]
      ring
    have hx' : ∑ i, ∑ j, c i j * x i * x j = 0 := by rw [← heval x]; exact hx
    have hNdvd : (p : ℤ) ∣ N := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
      rw [hN']
      push_cast
      calc (∑ i, ∑ j, ((a i : ZMod p)) * ((a j : ZMod p)) *
              ((discNum B p (y i : W) (y j : W) : ℤ) : ZMod p))
          = ∑ i, ∑ j, c i j * x i * x j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hc, ha i, ha j]
            ring
        _ = 0 := hx'
    obtain ⟨k, hk⟩ := hNdvd
    have hp0 : ((p : ℚ)) ≠ 0 := by
      exact_mod_cast (NeZero.ne p)
    refine mem_one_iff.mpr ⟨k, ?_⟩
    have : ((p : ℚ)) * (k : ℚ) = (p : ℚ) * B (z : W) (z : W) := by
      rw [← hNcast, hk]
      push_cast
      ring
    exact mul_left_cancel₀ hp0 this
  have hzv : ∀ v ∈ Ñ, B (z : W) v ∈ (1 : Submodule ℤ ℚ) := fun v hv => torsion_mem_dual z v hv
  have hsup := hmax.maximal (Ñ ⊔ Submodule.span ℤ {(z : W)}) le_sup_left
    (isIntegral_sup_span_singleton B hsymm hmax.integral hzv hzz)
  have hmem : (z : W) ∈ Ñ ⊔ Submodule.span ℤ {(z : W)} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [hsup] at hmem
  exact hznot hmem

/-! ### Corollary S: the orthogonal glue basis -/

variable (B Ñ p) in
/-- **Corollary S.**  The discriminant datum of a maximal integral overlattice at
the prime `p`: at most two vectors of the `p`-torsion part which generate it
modulo `Ñ`, are pairwise integrally paired, are independent modulo `Ñ`, and whose
diagonal pairings have exact denominator `p`. -/
structure GlueBasis where
  /-- The number of glue vectors: at most two. -/
  rank : ℕ
  /-- The rank bound, from `disc_dim_le_two`. -/
  rank_le : rank ≤ 2
  /-- The glue vectors. -/
  vec : Fin rank → W
  /-- Each glue vector lies in the `p`-torsion part of the dual. -/
  mem : ∀ i, vec i ∈ torsionPart B Ñ p
  /-- The glue vectors generate the `p`-torsion part modulo `Ñ`. -/
  spans : torsionPart B Ñ p = Ñ ⊔ Submodule.span ℤ (Set.range vec)
  /-- Distinct glue vectors pair integrally. -/
  ortho : ∀ i j, i ≠ j → B (vec i) (vec j) ∈ (1 : Submodule ℤ ℚ)
  /-- The diagonal pairing is a unit over `p`: `⟨vᵢ, vᵢ⟩ = mᵢ / p` with `p ∤ mᵢ`. -/
  diag : ∀ i, ∃ m : ℤ, ¬ ((p : ℤ) ∣ m) ∧ ((p : ℚ)) * B (vec i) (vec i) = (m : ℚ)
  /-- The glue vectors are independent modulo `Ñ`. -/
  indep : ∀ c : Fin rank → ℤ, (∑ i, c i • vec i) ∈ Ñ → ∀ i, (p : ℤ) ∣ c i

/-- The diagonal pairing at a glue vector is `uᵢ / p` for a unit `uᵢ` of
`ZMod p`. -/
theorem GlueBasis.exists_unit_diag [Fact p.Prime] (S : GlueBasis B Ñ p) (i : Fin S.rank) :
    ∃ (u : (ZMod p)ˣ) (m : ℤ), ((m : ZMod p)) = (u : ZMod p) ∧
      ((p : ℚ)) * B (S.vec i) (S.vec i) = (m : ℚ) := by
  obtain ⟨m, hdvd, hm⟩ := S.diag i
  have hne : ((m : ZMod p)) ≠ 0 := fun h =>
    hdvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  exact ⟨(isUnit_iff_ne_zero.mpr hne).unit, m,
    ((isUnit_iff_ne_zero.mpr hne).unit_spec).symm, hm⟩

/-- **Corollary S.**  A maximal integral overlattice whose dual splits as
`T_p + T_q` with `p` an odd prime coprime to `q` admits an orthogonal glue basis
at `p`. -/
theorem exists_orthogonal_glue_basis [hp : Fact p.Prime] (hp2 : p ≠ 2) (hsymm : B.IsSymm)
    (hnd : B.Nondegenerate) (hN : IsLattice ℚ Ñ) (hmax : IsMaximalIntegral B Ñ)
    {q : ℕ} (hpq : Nat.Coprime p q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    Nonempty (GlueBasis B Ñ p) := by
  classical
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  haveI : Module.Finite (ZMod p) (discGroup B Ñ p) := discGroup_finite hnd hN
  haveI : Invertible (2 : ZMod p) := by
    refine invertibleOfNonzero ?_
    intro h2
    have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp hcast
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd)
  have hsep : (discPairing B Ñ p hsymm).SeparatingLeft :=
    discPairing_separatingLeft hsymm hnd hN (NeZero.ne p) hpq hsplit
  have hsymmD : (discPairing B Ñ p hsymm).IsSymm := discPairing_isSymm hsymm
  obtain ⟨b, hortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hsymmD)
  have hdiag : ∀ i, discPairing B Ñ p hsymm (b i) (b i) ≠ 0 := fun i =>
    hortho.not_isOrtho_basis_self_of_separatingLeft hsep i
  choose y hy using fun i => Submodule.Quotient.mk_surjective
    (Ñ.comap (torsionPart B Ñ p).subtype) (b i)
  refine ⟨{
    rank := Module.finrank (ZMod p) (discGroup B Ñ p)
    rank_le := disc_dim_le_two hsymm hnd hN hmax
    vec := fun i => (y i : W)
    mem := fun i => (y i).2
    spans := ?_
    ortho := ?_
    diag := ?_
    indep := ?_ }⟩
  · -- generation
    refine le_antisymm ?_ ?_
    · intro w hw
      set d : discGroup B Ñ p := Submodule.Quotient.mk ⟨w, hw⟩ with hd
      choose k hk using fun i => ZMod.intCast_surjective (n := p) (b.repr d i)
      have hrepr : d = ∑ i, (k i) • b i := by
        conv_lhs => rw [← b.sum_repr d]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hk i, Int.cast_smul_eq_zsmul]
      set t : torsionPart B Ñ p := ∑ i, k i • y i with ht
      have hmk : (Submodule.Quotient.mk t : discGroup B Ñ p) = d := by
        have hmkq : (Submodule.Quotient.mk t : discGroup B Ñ p) =
            (Ñ.comap (torsionPart B Ñ p).subtype).mkQ t := rfl
        rw [hmkq, ht, map_sum, hrepr]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        show k i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p) = k i • b i
        rw [hy i]
      have hsub : w - (t : W) ∈ Ñ := by
        have hzero : (Submodule.Quotient.mk (⟨w, hw⟩ - t) : discGroup B Ñ p) = 0 := by
          have hmkq : (Submodule.Quotient.mk (⟨w, hw⟩ - t) : discGroup B Ñ p) =
              (Ñ.comap (torsionPart B Ñ p).subtype).mkQ (⟨w, hw⟩ - t) := rfl
          rw [hmkq, map_sub]
          show (Submodule.Quotient.mk ⟨w, hw⟩ : discGroup B Ñ p) -
            (Submodule.Quotient.mk t : discGroup B Ñ p) = 0
          rw [hmk, hd, sub_self]
        have hmem₀ := discGroup_mk_eq_zero_iff.mp hzero
        simpa using hmem₀
      have htmem : (t : W) ∈ Submodule.span ℤ (Set.range fun i => (y i : W)) := by
        rw [ht]
        push_cast
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span ⟨i, rfl⟩
      have hdecomp : w = (w - (t : W)) + (t : W) := by abel
      rw [hdecomp]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hsub)
        (Submodule.mem_sup_right htmem)
    · refine sup_le (le_torsionPart hmax.integral p) ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (y i).2
  · -- orthogonality
    intro i j hij
    have h0 : discPairing B Ñ p hsymm (b i) (b j) = 0 := hortho hij
    rw [← hy i, ← hy j, discPairing_mk] at h0
    exact mem_one_of_dvd_discNum (NeZero.ne p) (torsion_mem_dual (y i))
      (torsion_zsmul_mem (y j)) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  · -- the diagonal is a unit over `p`
    intro i
    refine ⟨discNum B p (y i : W) (y i : W), ?_, ?_⟩
    · intro hdvd
      refine hdiag i ?_
      rw [← hy i, discPairing_mk]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    · exact (discNum_cast (torsion_mem_dual (y i)) (torsion_zsmul_mem (y i))).symm
  · -- independence modulo `Ñ`
    intro cf hmem i
    have hsum : ∑ i, ((cf i : ZMod p)) • b i = 0 := by
      have hmk : ((Ñ.comap (torsionPart B Ñ p).subtype).mkQ (∑ i, cf i • y i)) = 0 := by
        refine discGroup_mk_eq_zero_iff.mpr ?_
        have hco : ((∑ i, cf i • y i : torsionPart B Ñ p) : W) = ∑ i, cf i • (y i : W) := by
          push_cast
          rfl
        rw [hco]
        exact hmem
      rw [map_sum] at hmk
      rw [← hmk]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      show ((cf i : ZMod p)) • b i = cf i • (Submodule.Quotient.mk (y i) : discGroup B Ñ p)
      rw [hy i, Int.cast_smul_eq_zsmul]
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => ((cf i : ZMod p))) hsum i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

/-- **Corollary S(1).**  Glue bases at two coprime primes whose torsion parts
exhaust the dual generate the whole dual lattice over `Ñ`:
`Ñ^∨ = Ñ + ∑ ℤ·yᵢ`. -/
theorem dual_eq_sup_span_glue {q : ℕ} (S : GlueBasis B Ñ p) (T : GlueBasis B Ñ q)
    (hsplit : B.dualSubmodule Ñ = torsionPart B Ñ p ⊔ torsionPart B Ñ q) :
    B.dualSubmodule Ñ = Ñ ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec) := by
  rw [hsplit, S.spans, T.spans, Submodule.span_union, sup_sup_sup_comm, sup_idem]

end Discriminant

end SRG266.Lattice
