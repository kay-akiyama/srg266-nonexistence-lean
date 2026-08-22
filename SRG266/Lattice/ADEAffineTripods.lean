/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADETripodShape

/-!
# The three affine tripod obstructions

The elementary ADE classification needs only three forbidden subgraphs.  In
arm-length notation they are `(2,2,2)`, `(1,3,3)`, and `(1,2,5)`, corresponding
to the affine diagrams `Ẽ6`, `Ẽ7`, and `Ẽ8`.  Each has an explicit
nonzero nonnegative null vector for `2I-A`.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

/-- Vertices of a tripod: a centre and three disjoint finite arms. -/
abbrev TripodVertex (a b c : ℕ) := Option (Fin a ⊕ (Fin b ⊕ Fin c))

/-- Whether an arm vertex is the one next to the centre. -/
def tripodArmZero {a b c : ℕ} : Fin a ⊕ (Fin b ⊕ Fin c) → Prop
  | .inl i => i.1 = 0
  | .inr (.inl i) => i.1 = 0
  | .inr (.inr i) => i.1 = 0

/-- Adjacency inside one of the three arms. -/
def tripodArmRel {a b c : ℕ} :
    Fin a ⊕ (Fin b ⊕ Fin c) → Fin a ⊕ (Fin b ⊕ Fin c) → Prop
  | .inl i, .inl j => (pathGraph a).Adj i j
  | .inr (.inl i), .inr (.inl j) => (pathGraph b).Adj i j
  | .inr (.inr i), .inr (.inr j) => (pathGraph c).Adj i j
  | _, _ => False

/-- A directed presentation whose symmetric closure is the tripod graph. -/
def tripodRel {a b c : ℕ} : TripodVertex a b c → TripodVertex a b c → Prop
  | none, some x => tripodArmZero x
  | some x, some y => tripodArmRel x y
  | _, _ => False

/-- The tree with a centre and arms of lengths `a`, `b`, and `c`. -/
def tripodGraph (a b c : ℕ) : SimpleGraph (TripodVertex a b c) :=
  SimpleGraph.fromRel tripodRel

/-- Embed the first arm as a path in the tripod. -/
def tripodArm0Hom (a b c : ℕ) : pathGraph a →g tripodGraph a b c where
  toFun i := some (.inl i)
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

/-- Embed the second arm as a path in the tripod. -/
def tripodArm1Hom (a b c : ℕ) : pathGraph b →g tripodGraph a b c where
  toFun i := some (.inr (.inl i))
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

/-- Embed the third arm as a path in the tripod. -/
def tripodArm2Hom (a b c : ℕ) : pathGraph c →g tripodGraph a b c where
  toFun i := some (.inr (.inr i))
  map_rel' := by
    intro i j hij
    rw [tripodGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp [hij.ne], Or.inl hij⟩

/-- A tripod with three nonempty arms is connected. -/
theorem tripodGraph_connected {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (tripodGraph a b c).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  intro x
  cases x with
  | none => exact .rfl
  | some x =>
      rcases x with i | x
      · let z₀ : Fin a := ⟨0, ha⟩
        have hz : (tripodGraph a b c).Adj none (some (.inl z₀)) := by
          rw [tripodGraph, SimpleGraph.fromRel_adj]
          exact ⟨by simp, Or.inl rfl⟩
        exact hz.reachable.trans
          ((SimpleGraph.pathGraph_preconnected a z₀ i).map (tripodArm0Hom a b c))
      · rcases x with i | i
        · let z₁ : Fin b := ⟨0, hb⟩
          have hz : (tripodGraph a b c).Adj none (some (.inr (.inl z₁))) := by
            rw [tripodGraph, SimpleGraph.fromRel_adj]
            exact ⟨by simp, Or.inl rfl⟩
          exact hz.reachable.trans
            ((SimpleGraph.pathGraph_preconnected b z₁ i).map (tripodArm1Hom a b c))
        · let z₂ : Fin c := ⟨0, hc⟩
          have hz : (tripodGraph a b c).Adj none (some (.inr (.inr z₂))) := by
            rw [tripodGraph, SimpleGraph.fromRel_adj]
            exact ⟨by simp, Or.inl rfl⟩
          exact hz.reachable.trans
            ((SimpleGraph.pathGraph_preconnected c z₂ i).map (tripodArm2Hom a b c))

/-- Null weight for the affine `(2,2,2)` tripod. -/
def affineE6Weight : TripodVertex 2 2 2 → ℤ
  | none => 3
  | some (.inl i) => 2 - i.1
  | some (.inr (.inl i)) => 2 - i.1
  | some (.inr (.inr i)) => 2 - i.1

/-- Null weight for the affine `(1,3,3)` tripod. -/
def affineE7Weight : TripodVertex 1 3 3 → ℤ
  | none => 4
  | some (.inl _) => 2
  | some (.inr (.inl i)) => 3 - i.1
  | some (.inr (.inr i)) => 3 - i.1

/-- Null weight for the affine `(1,2,5)` tripod. -/
def affineE8Weight : TripodVertex 1 2 5 → ℤ
  | none => 6
  | some (.inl _) => 3
  | some (.inr (.inl i)) => 4 - 2 * i.1
  | some (.inr (.inr i)) => 5 - i.1

set_option maxHeartbeats 2000000 in
/-- The affine `Ẽ6` tripod has Cartan energy zero. -/
theorem affineE6_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 2 2 2) affineE6Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE6Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

set_option maxHeartbeats 2000000 in
/-- The affine `Ẽ7` tripod has Cartan energy zero. -/
theorem affineE7_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 1 3 3) affineE7Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE7Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

set_option maxHeartbeats 2000000 in
/-- The affine `Ẽ8` tripod has Cartan energy zero. -/
theorem affineE8_cartanEnergy_zero :
    graphCartanEnergy (tripodGraph 1 2 5) affineE8Weight = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    tripodGraph, tripodRel, tripodArmRel, tripodArmZero,
    affineE8Weight, SimpleGraph.fromRel_adj, SimpleGraph.pathGraph_adj,
    Fin.sum_univ_succ]
  decide

theorem affineE6Weight_nonnegative (x) : 0 ≤ affineE6Weight x := by
  rcases x with _ | x
  · norm_num [affineE6Weight]
  rcases x with i | x
  · fin_cases i <;> norm_num [affineE6Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE6Weight]

theorem affineE7Weight_nonnegative (x) : 0 ≤ affineE7Weight x := by
  rcases x with _ | x
  · norm_num [affineE7Weight]
  rcases x with i | x
  · fin_cases i; norm_num [affineE7Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE7Weight]

theorem affineE8Weight_nonnegative (x) : 0 ≤ affineE8Weight x := by
  rcases x with _ | x
  · norm_num [affineE8Weight]
  rcases x with i | x
  · fin_cases i; norm_num [affineE8Weight]
  rcases x with i | i <;> fin_cases i <;> norm_num [affineE8Weight]

theorem affineE6Weight_ne_zero : affineE6Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 2 2 2)
  norm_num [affineE6Weight] at this

theorem affineE7Weight_ne_zero : affineE7Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 1 3 3)
  norm_num [affineE7Weight] at this

theorem affineE8Weight_ne_zero : affineE8Weight ≠ 0 := by
  intro h
  have := congrFun h (none : TripodVertex 1 2 5)
  norm_num [affineE8Weight] at this

/-! ## Transporting an affine tripod into an ambient Cartan graph -/

/-- Map the centre and the three arms into a common vertex type. -/
def tripodVertexMap {V : Type*} {a b c : ℕ} (z : V)
    (f₀ : Fin a → V) (f₁ : Fin b → V) (f₂ : Fin c → V) :
    TripodVertex a b c → V
  | none => z
  | some (.inl i) => f₀ i
  | some (.inr (.inl i)) => f₁ i
  | some (.inr (.inr i)) => f₂ i

/-- Three injective, pairwise-disjoint arms disjoint from the centre give an
embedding of the tripod vertex type. -/
def tripodVertexEmbedding {V : Type*} {a b c : ℕ} (z : V)
    (f₀ : Fin a ↪ V) (f₁ : Fin b ↪ V) (f₂ : Fin c ↪ V)
    (h₀z : ∀ i, f₀ i ≠ z) (h₁z : ∀ i, f₁ i ≠ z)
    (h₂z : ∀ i, f₂ i ≠ z)
    (h₀₁ : ∀ i j, f₀ i ≠ f₁ j) (h₀₂ : ∀ i j, f₀ i ≠ f₂ j)
    (h₁₂ : ∀ i j, f₁ i ≠ f₂ j) : TripodVertex a b c ↪ V :=
  ⟨tripodVertexMap z f₀ f₁ f₂, by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            rcases y with y | y
            · exact (h₀z y hxy.symm).elim
            · rcases y with y | y
              · exact (h₁z y hxy.symm).elim
              · exact (h₂z y hxy.symm).elim
    | some x =>
        cases y with
        | none =>
            rcases x with x | x
            · exact (h₀z x hxy).elim
            · rcases x with x | x
              · exact (h₁z x hxy).elim
              · exact (h₂z x hxy).elim
        | some y =>
            rcases x with x | x
            · rcases y with y | y
              · exact congr_arg (some ∘ Sum.inl) (f₀.injective hxy)
              · rcases y with y | y
                · exact (h₀₁ x y hxy).elim
                · exact (h₀₂ x y hxy).elim
            · rcases x with x | x
              · rcases y with y | y
                · exact (h₀₁ y x hxy.symm).elim
                · rcases y with y | y
                  · exact congr_arg (some ∘ Sum.inr ∘ Sum.inl) (f₁.injective hxy)
                  · exact (h₁₂ x y hxy).elim
              · rcases y with y | y
                · exact (h₀₂ y x hxy.symm).elim
                · rcases y with y | y
                  · exact (h₁₂ y x hxy.symm).elim
                  · exact congr_arg (some ∘ Sum.inr ∘ Sum.inr) (f₂.injective hxy)⟩

/-- A mapped tripod relation is an ambient edge when the arm paths and the
three centre edges are respected. -/
theorem tripodRel_map {V : Type*} {G : SimpleGraph V} {a b c : ℕ}
    (z : V) (f₀ : Fin a → V) (f₁ : Fin b → V) (f₂ : Fin c → V)
    (h₀ : ∀ {i j}, (pathGraph a).Adj i j → G.Adj (f₀ i) (f₀ j))
    (h₁ : ∀ {i j}, (pathGraph b).Adj i j → G.Adj (f₁ i) (f₁ j))
    (h₂ : ∀ {i j}, (pathGraph c).Adj i j → G.Adj (f₂ i) (f₂ j))
    (hz₀ : ∀ i, i.1 = 0 → G.Adj z (f₀ i))
    (hz₁ : ∀ i, i.1 = 0 → G.Adj z (f₁ i))
    (hz₂ : ∀ i, i.1 = 0 → G.Adj z (f₂ i))
    {x y : TripodVertex a b c} (hxy : tripodRel x y) :
    G.Adj (tripodVertexMap z f₀ f₁ f₂ x)
      (tripodVertexMap z f₀ f₁ f₂ y) := by
  cases x with
  | none =>
      cases y with
      | none => simp [tripodRel] at hxy
      | some y =>
          rcases y with y | y
          · exact hz₀ y hxy
          · rcases y with y | y
            · exact hz₁ y hxy
            · exact hz₂ y hxy
  | some x =>
      cases y with
      | none => simp [tripodRel] at hxy
      | some y =>
          rcases x with x | x
          · rcases y with y | y
            · exact h₀ hxy
            · rcases y with y | y <;> simp [tripodRel, tripodArmRel] at hxy
          · rcases x with x | x
            · rcases y with y | y
              · simp [tripodRel, tripodArmRel] at hxy
              · rcases y with y | y
                · exact h₁ hxy
                · simp [tripodRel, tripodArmRel] at hxy
            · rcases y with y | y
              · simp [tripodRel, tripodArmRel] at hxy
              · rcases y with y | y
                · simp [tripodRel, tripodArmRel] at hxy
                · exact h₂ hxy

/-- A nonzero nonnegative null vector on a tripod rules out its embedding in
a positive ambient Cartan graph. -/
theorem false_of_tripod_null_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hpos : IsPositiveCartan G)
    {a b c : ℕ} (f : TripodVertex a b c ↪ V)
    (hmap : ∀ {x y}, (tripodGraph a b c).Adj x y → G.Adj (f x) (f y))
    (w : TripodVertex a b c → ℤ) (hw0 : w ≠ 0) (hw : ∀ x, 0 ≤ w x)
    (henergy : graphCartanEnergy (tripodGraph a b c) w ≤ 0) : False := by
  classical
  have hle : tripodGraph a b c ≤ G.comap f := by
    intro x y hxy
    simpa only [SimpleGraph.comap_adj] using hmap hxy
  have hcomp : IsPositiveCartan (G.comap f) := hpos.comap f
  exact (not_isPositiveCartan_of_nonpositive_subgraph hle hw0 hw henergy) hcomp

/-- Three sufficiently long oriented punctured components realize any smaller
tripod as a subgraph of the ambient tree. -/
theorem false_of_orientedArm_tripod
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    {a b c : ℕ} (ha : a ≤ A₀.length) (hb : b ≤ A₁.length)
    (hc : c ≤ A₂.length)
    (w : TripodVertex a b c → ℤ) (hw0 : w ≠ 0) (hw : ∀ x, 0 ≤ w x)
    (henergy : graphCartanEnergy (tripodGraph a b c) w ≤ 0) : False := by
  classical
  let f₀ := A₀.prefixEmbedding ha
  let f₁ := A₁.prefixEmbedding hb
  let f₂ := A₂.prefixEmbedding hc
  let f : TripodVertex a b c ↪ V := tripodVertexEmbedding z f₀ f₁ f₂
    (fun i ↦ A₀.prefixEmbedding_ne_center ha i)
    (fun i ↦ A₁.prefixEmbedding_ne_center hb i)
    (fun i ↦ A₂.prefixEmbedding_ne_center hc i)
    (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₁ h₀₁ ha hb i j)
    (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₂ h₀₂ ha hc i j)
    (fun i j ↦ A₁.prefixEmbedding_ne_of_component_ne A₂ h₁₂ hb hc i j)
  have hmap : ∀ {x y}, (tripodGraph a b c).Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    rw [tripodGraph, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with hxy | hxy
    · exact tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj ha h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj hb h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj hc h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero ha i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero hb i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero hc i hi) hxy
    · exact (tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj ha h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj hb h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj hc h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero ha i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero hb i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero hc i hi) hxy).symm
  exact false_of_tripod_null_embedding hpos f hmap w hw0 hw henergy

/-- No three oriented arms can all have length at least two. -/
theorem not_all_three_arms_length_two
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 2 ≤ A₀.length) (h₁ : 2 ≤ A₁.length) (h₂ : 2 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE6Weight affineE6Weight_ne_zero
    affineE6Weight_nonnegative affineE6_cartanEnergy_zero.le

/-- Arms of lengths at least `(1,3,3)` contain the affine `Ẽ7` tripod. -/
theorem not_arms_length_one_three_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 1 ≤ A₀.length) (h₁ : 3 ≤ A₁.length) (h₂ : 3 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE7Weight affineE7Weight_ne_zero
    affineE7Weight_nonnegative affineE7_cartanEnergy_zero.le

/-- Arms of lengths at least `(1,2,5)` contain the affine `Ẽ8` tripod. -/
theorem not_arms_length_one_two_five
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component)
    (h₀ : 1 ≤ A₀.length) (h₁ : 2 ≤ A₁.length) (h₂ : 5 ≤ A₂.length) :
    False :=
  false_of_orientedArm_tripod hpos hconn A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
    h₀ h₁ h₂ affineE8Weight affineE8Weight_ne_zero
    affineE8Weight_nonnegative affineE8_cartanEnergy_zero.le

end Lattice
end SRG266
