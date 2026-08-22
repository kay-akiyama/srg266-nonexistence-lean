/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADEPositiveArmClassification

/-!
# Coordinates for a positive Cartan tripod

Three oriented punctured components cover the ambient tree.  Their path
coordinates therefore assemble into an isomorphism from the corresponding
abstract tripod graph.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

theorem eq_one_of_three_of_card_eq_three
    {K : Type*} [Fintype K] [DecidableEq K]
    (hcard : Fintype.card K = 3) {a b c : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : K) :
    x = a ∨ x = b ∨ x = c := by
  have hs_card : ({a, b, c} : Finset K).card = 3 := by
    simp [hab, hac, hbc]
  have hs_univ : ({a, b, c} : Finset K) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa only [Finset.card_univ, hcard, hs_card] using (le_refl 3)
  have hx : x ∈ ({a, b, c} : Finset K) := by rw [hs_univ]; simp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

/-- Three distinct oriented components, when there are exactly three
punctured components, give the whole ambient graph as a tripod. -/
theorem exists_tripodGraph_iso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected) {z : V}
    (hcomponents : Fintype.card (G.induce {x | x ≠ z}).ConnectedComponent = 3)
    (A₀ A₁ A₂ : OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩)
    (h₀₁ : A₀.component ≠ A₁.component)
    (h₀₂ : A₀.component ≠ A₂.component)
    (h₁₂ : A₁.component ≠ A₂.component) :
    Nonempty (tripodGraph A₀.length A₁.length A₂.length ≃g G) := by
  classical
  let f₀ := A₀.prefixEmbedding (le_refl A₀.length)
  let f₁ := A₁.prefixEmbedding (le_refl A₁.length)
  let f₂ := A₂.prefixEmbedding (le_refl A₂.length)
  let f : TripodVertex A₀.length A₁.length A₂.length ↪ V :=
    tripodVertexEmbedding z f₀ f₁ f₂
      (fun i ↦ A₀.prefixEmbedding_ne_center _ i)
      (fun i ↦ A₁.prefixEmbedding_ne_center _ i)
      (fun i ↦ A₂.prefixEmbedding_ne_center _ i)
      (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₁ h₀₁ _ _ i j)
      (fun i j ↦ A₀.prefixEmbedding_ne_of_component_ne A₂ h₀₂ _ _ i j)
      (fun i j ↦ A₁.prefixEmbedding_ne_of_component_ne A₂ h₁₂ _ _ i j)
  have hf_surj : Function.Surjective f := by
    intro v
    by_cases hv : v = z
    · refine ⟨none, ?_⟩
      change z = v
      exact hv.symm
    · let rv : {x : V // x ≠ z} := ⟨v, hv⟩
      let C := (G.induce {x | x ≠ z}).connectedComponentMk rv
      rcases eq_one_of_three_of_card_eq_three hcomponents h₀₁ h₀₂ h₁₂ C with
        hC | hC | hC
      · have hmem : rv ∈ A₀.component := by
          change (G.induce {x | x ≠ z}).connectedComponentMk rv = A₀.component
          exact hC
        obtain ⟨i, hi⟩ := A₀.coord.surjective ⟨rv, hmem⟩
        refine ⟨some (.inl i), ?_⟩
        change A₀.vertex (Fin.castLE (le_refl A₀.length) i) = v
        simpa only [Fin.castLE_refl, OrientedPuncturedArm.vertex] using
          congr_arg (fun y : A₀.component ↦ y.1.1) hi
      · have hmem : rv ∈ A₁.component := by
          change (G.induce {x | x ≠ z}).connectedComponentMk rv = A₁.component
          exact hC
        obtain ⟨i, hi⟩ := A₁.coord.surjective ⟨rv, hmem⟩
        refine ⟨some (.inr (.inl i)), ?_⟩
        change A₁.vertex (Fin.castLE (le_refl A₁.length) i) = v
        simpa only [Fin.castLE_refl, OrientedPuncturedArm.vertex] using
          congr_arg (fun y : A₁.component ↦ y.1.1) hi
      · have hmem : rv ∈ A₂.component := by
          change (G.induce {x | x ≠ z}).connectedComponentMk rv = A₂.component
          exact hC
        obtain ⟨i, hi⟩ := A₂.coord.surjective ⟨rv, hmem⟩
        refine ⟨some (.inr (.inr i)), ?_⟩
        change A₂.vertex (Fin.castLE (le_refl A₂.length) i) = v
        simpa only [Fin.castLE_refl, OrientedPuncturedArm.vertex] using
          congr_arg (fun y : A₂.component ↦ y.1.1) hi
  let e : TripodVertex A₀.length A₁.length A₂.length ≃ V :=
    Equiv.ofBijective f ⟨f.injective, hf_surj⟩
  let H : SimpleGraph V :=
    (tripodGraph A₀.length A₁.length A₂.length).map e
  have hmap : ∀ {x y},
      (tripodGraph A₀.length A₁.length A₂.length).Adj x y →
        G.Adj (e x) (e y) := by
    intro x y hxy
    rw [tripodGraph, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with hxy | hxy
    · exact tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj _ h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj _ h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj _ h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero _ i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero _ i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero _ i hi) hxy
    · exact (tripodRel_map z f₀ f₁ f₂
        (fun h ↦ A₀.adj_prefixEmbedding_of_path_adj _ h)
        (fun h ↦ A₁.adj_prefixEmbedding_of_path_adj _ h)
        (fun h ↦ A₂.adj_prefixEmbedding_of_path_adj _ h)
        (fun i hi ↦ A₀.adj_center_prefixEmbedding_of_val_eq_zero _ i hi)
        (fun i hi ↦ A₁.adj_center_prefixEmbedding_of_val_eq_zero _ i hi)
        (fun i hi ↦ A₂.adj_center_prefixEmbedding_of_val_eq_zero _ i hi) hxy).symm
  have hHG : H ≤ G := by
    intro x y hxy
    change ((tripodGraph A₀.length A₁.length A₂.length).map e).Adj x y at hxy
    rw [SimpleGraph.map_adj'] at hxy
    obtain ⟨_, i, j, hij, rfl, rfl⟩ := hxy
    exact hmap hij
  have hHconn : H.Connected := by
    exact (SimpleGraph.Iso.map e
      (tripodGraph A₀.length A₁.length A₂.length)).connected_iff.mp
        (tripodGraph_connected A₀.length_pos A₁.length_pos A₂.length_pos)
  have hHacyc : H.IsAcyclic := SimpleGraph.IsAcyclic.anti hHG hpos.isAcyclic
  letI : DecidableRel H.Adj := Classical.decRel _
  have hHtree : H.IsTree := ⟨hHconn, hHacyc⟩
  have hGtree : G.IsTree := ⟨hconn, hpos.isAcyclic⟩
  have hedge_card : H.edgeFinset.card = G.edgeFinset.card := by
    have hHcard := hHtree.card_edgeFinset
    have hGcard := hGtree.card_edgeFinset
    omega
  have hedge : H.edgeFinset = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hHG)
    simpa only [hedge_card] using le_rfl
  have hH_eq_G : H = G := SimpleGraph.edgeFinset_inj.mp hedge
  refine ⟨?_⟩
  simpa only [H, hH_eq_G] using
    SimpleGraph.Iso.map e (tripodGraph A₀.length A₁.length A₂.length)

end Lattice
end SRG266
