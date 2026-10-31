import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes.Node_3633848309_047de4fc_8cd7925a

open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1032661153_b6ef2974 : ∀ {X Θ : Type*} [MeasurableSpace X]
    (μ : Measure X) (k : Θ → X → ℝ) (hK : ∀ p : Θ, IsProbDensity μ (k p))
    (t : ℕ) (ht : 2 ≤ t)
    (W : ℕ → ExactMixture Θ X μ k t)
    (ℓ : Fin t) (σ : Fin (t - 1) → Fin t)
    (hσ_inj : Function.Injective σ)
    (hσ_mono : StrictMono σ)
    (hσ_range : Set.range σ = {j : Fin t | j ≠ ℓ}),
    ∃ G : ℕ → ExactMixture Θ X μ k (t - 1),
      (∀ (i : ℕ) (r : Fin (t - 1)),
        (G i).weights r = (W i).weights (σ r) / (1 - (W i).weights ℓ)) ∧
      (∀ (i : ℕ) (r : Fin (t - 1)), (G i).params r = (W i).params (σ r)) ∧
      (∀ (i : ℕ) (x : X),
        (G i).f x = ∑ r : Fin (t - 1),
          ((W i).weights (σ r) / (1 - (W i).weights ℓ)) * k ((W i).params (σ r)) x) := by
  /- @proof-region region.target-node.session.4a5ae5d6313b791a begin -/
  intro X Θ _ μ k hK t ht W ℓ σ hσ_inj hσ_mono hσ_range
  have ht1 : 1 ≤ t - 1 := by omega
  haveI : Nonempty (Fin (t - 1)) := ⟨⟨0, by omega⟩⟩
  have key : ∀ i : ℕ, 1 - (W i).weights ℓ = ∑ r : Fin (t - 1), (W i).weights (σ r) := by
    intro i
    have himage : Finset.univ.image σ = Finset.univ.erase ℓ := by
      ext j
      constructor
      · intro hj
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hj
        have h : σ r ∈ Set.range σ := ⟨r, rfl⟩
        rw [hσ_range] at h
        simpa using h
      · intro hj
        rw [Finset.mem_erase] at hj
        have hj' : j ∈ Set.range σ := by
          rw [hσ_range]
          exact hj.1
        obtain ⟨r, hr⟩ := hj'
        exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩
    have hℓ : ℓ ∉ Finset.univ.image σ := by
      rw [himage]
      simp
    have hins : (Finset.univ : Finset (Fin t)) = insert ℓ (Finset.univ.image σ) := by
      rw [himage, Finset.insert_erase (Finset.mem_univ ℓ)]
    have hsplit : ∑ j : Fin t, (W i).weights j
        = (W i).weights ℓ + ∑ r : Fin (t - 1), (W i).weights (σ r) := by
      rw [hins, Finset.sum_insert hℓ]
      rw [Finset.sum_image (fun x _ y _ hxy => hσ_inj hxy)]
    have hws := (W i).weights_sum
    rw [hsplit] at hws
    linarith
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · have hden := key i
    have hden_pos : 0 < 1 - (W i).weights ℓ := by
      rw [hden]
      exact Finset.sum_pos (fun r _ => (W i).weights_pos (σ r)) Finset.univ_nonempty
    have hwpos : ∀ r : Fin (t - 1), 0 < (W i).weights (σ r) / (1 - (W i).weights ℓ) :=
      fun r => div_pos ((W i).weights_pos (σ r)) hden_pos
    have hwsum : ∑ r : Fin (t - 1), (W i).weights (σ r) / (1 - (W i).weights ℓ) = 1 := by
      rw [← Finset.sum_div, ← hden]
      exact div_self (ne_of_gt hden_pos)
    exact
      { f := fun x => ∑ r : Fin (t - 1),
          ((W i).weights (σ r) / (1 - (W i).weights ℓ)) * k ((W i).params (σ r)) x
        dens := statopia_math_node_3633848309_047de4fc μ k hK (t - 1) ht1
          (fun r => (W i).weights (σ r) / (1 - (W i).weights ℓ)) hwpos hwsum
          (fun r => (W i).params (σ r))
        weights := fun r => (W i).weights (σ r) / (1 - (W i).weights ℓ)
        params := fun r => (W i).params (σ r)
        weights_pos := hwpos
        weights_sum := hwsum
        params_injective := fun x y hxy => hσ_inj ((W i).params_injective hxy)
        eq_mixture := rfl }
  · intro i r
    rfl
  · intro i r
    rfl
  · intro i x
    rfl
  /- @proof-region region.target-node.session.4a5ae5d6313b791a end -/

end Statlib.Imported
