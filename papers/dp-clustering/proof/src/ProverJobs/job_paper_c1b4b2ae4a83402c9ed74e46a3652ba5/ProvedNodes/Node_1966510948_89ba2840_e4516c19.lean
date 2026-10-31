import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Vocabulary
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.Base
import ProverJobs.job_paper_c1b4b2ae4a83402c9ed74e46a3652ba5.ProvedNodes.Node_566849461_e206dd4e_57422b29

open MeasureTheory Filter Topology
open scoped ENNReal
open Statlib.Imported

open MeasureTheory Filter Topology
open scoped ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1966510948_89ba2840 : ∀ {X Θ : Type*} [MeasurableSpace X]
    (μ : Measure X) (k : Θ → X → ℝ) (hK : ∀ θ : Θ, IsProbDensity μ (k θ))
    (t : ℕ) (ht : 2 ≤ t)
    (W : ℕ → ExactMixture Θ X μ k t)
    (l : Fin t) (sigma : Fin (t - 1) → Fin t)
    (hsigma_mono : StrictMono sigma)
    (hsigma_range : Set.range sigma = ({l} : Set (Fin t))ᶜ)
    (G : ℕ → ExactMixture Θ X μ k (t - 1))
    (hG : ∀ (i : ℕ) (x : X),
      (G i).f x = ∑ r : Fin (t - 1),
        ((W i).weights (sigma r) / (1 - (W i).weights l)) * k ((W i).params (sigma r)) x),
    ∀ i : ℕ, ∫ x, |(W i).f x - (G i).f x| ∂μ ≤ 2 * (W i).weights l := by
  /- @proof-region region.target-node.session.c23d4ed5d5b23561 begin -/
  intro X Θ _ μ k hK t ht W l sigma hsigma_mono hsigma_range G hG i
  have hsplit : ∀ (F : Fin t → ℝ), ∑ j : Fin t, F j = F l + ∑ r : Fin (t - 1), F (sigma r) := by
    intro F
    have key : ∑ r : Fin (t - 1), F (sigma r) = ∑ j ∈ (Finset.univ.erase l : Finset (Fin t)), F j := by
      refine Finset.sum_bij (fun r _ => sigma r) ?_ ?_ ?_ ?_
      · intro r _
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        have hr : sigma r ∈ Set.range sigma := ⟨r, rfl⟩
        rw [hsigma_range] at hr
        simpa using hr
      · intro a _ b _ hab
        exact hsigma_mono.injective hab
      · intro b hb
        have hbne : b ≠ l := (Finset.mem_erase.mp hb).1
        have hbr : b ∈ Set.range sigma := by
          rw [hsigma_range]
          simpa using hbne
        obtain ⟨r, hr⟩ := hbr
        exact ⟨r, Finset.mem_univ r, hr⟩
      · intro a _
        rfl
    have h1 : ∑ j : Fin t, F j = F l + ∑ j ∈ (Finset.univ.erase l : Finset (Fin t)), F j := by
      rw [← Finset.sum_insert (show l ∉ (Finset.univ.erase l : Finset (Fin t)) from by simp)]
      rw [Finset.insert_erase (Finset.mem_univ l)]
    rw [h1, key]
  have hsum_w : 1 - (W i).weights l = ∑ r : Fin (t - 1), (W i).weights (sigma r) := by
    have h := hsplit (W i).weights
    linarith [(W i).weights_sum]
  have h1mq_pos : 0 < 1 - (W i).weights l := by
    rw [hsum_w]
    let r₀ : Fin (t - 1) := ⟨0, by omega⟩
    have hins : (Finset.univ : Finset (Fin (t - 1))) = insert r₀ (Finset.univ.erase r₀) :=
      (Finset.insert_erase (Finset.mem_univ r₀)).symm
    have hsp : ∑ r : Fin (t - 1), (W i).weights (sigma r)
        = (W i).weights (sigma r₀)
          + ∑ r ∈ (Finset.univ.erase r₀ : Finset (Fin (t - 1))), (W i).weights (sigma r) := by
      conv_lhs => rw [hins]
      rw [Finset.sum_insert (show r₀ ∉ (Finset.univ.erase r₀ : Finset (Fin (t - 1))) from by simp)]
    have hnn : 0 ≤ ∑ r ∈ (Finset.univ.erase r₀ : Finset (Fin (t - 1))), (W i).weights (sigma r) :=
      Finset.sum_nonneg (fun r _ => le_of_lt ((W i).weights_pos (sigma r)))
    linarith [hsp, hnn, (W i).weights_pos (sigma r₀)]

  have h1mq_ne : 1 - (W i).weights l ≠ 0 := ne_of_gt h1mq_pos
  have hq_pos : 0 < (W i).weights l := (W i).weights_pos l
  have hmain := statopia_math_node_566849461_e206dd4e μ (G i).f (G i).dens
  have hkl : Integrable (k ((W i).params l)) μ ∧ ∫ x, k ((W i).params l) x ∂μ = 1 :=
    hmain.2 Θ k hK ((W i).params l)
  have hgi : Integrable (G i).f μ ∧ ∫ x, (G i).f x ∂μ = 1 := hmain.1
  have hkl_nn : ∀ᵐ x ∂μ, 0 ≤ k ((W i).params l) x := (hK ((W i).params l)).2.1
  have hg_nn : ∀ᵐ x ∂μ, 0 ≤ (G i).f x := (G i).dens.2.1
  have hbound_ae : ∀ᵐ x ∂μ,
      |k ((W i).params l) x - (G i).f x| ≤ k ((W i).params l) x + (G i).f x := by
    filter_upwards [hkl_nn, hg_nn] with x h1 h2
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have h_lg : ∫ x, |k ((W i).params l) x - (G i).f x| ∂μ ≤ 2 := by
    have hmono : ∫ x, |k ((W i).params l) x - (G i).f x| ∂μ
        ≤ ∫ x, (k ((W i).params l) x + (G i).f x) ∂μ :=
      MeasureTheory.integral_mono_ae (hkl.1.sub hgi.1).abs (hkl.1.add hgi.1) hbound_ae
    have hinter : ∫ x, (k ((W i).params l) x + (G i).f x) ∂μ = 2 := by
      rw [MeasureTheory.integral_add hkl.1 hgi.1, hkl.2, hgi.2]
      norm_num
    linarith

  have hfeq : ∀ x : X, (W i).f x
      = (W i).weights l * k ((W i).params l) x + (1 - (W i).weights l) * (G i).f x := by
    intro x
    have hf : (W i).f x = ∑ j : Fin t, (W i).weights j * k ((W i).params j) x := by
      rw [(W i).eq_mixture]
    have hgx : (1 - (W i).weights l) * (G i).f x
        = ∑ r : Fin (t - 1), (W i).weights (sigma r) * k ((W i).params (sigma r)) x := by
      rw [hG i x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      have hcoef : (1 - (W i).weights l) * ((W i).weights (sigma r) / (1 - (W i).weights l))
          = (W i).weights (sigma r) := by field_simp
      rw [← mul_assoc, hcoef]
    rw [hf, hsplit (fun j => (W i).weights j * k ((W i).params j) x), hgx]
  have hdiff : ∀ x : X, (W i).f x - (G i).f x
      = (W i).weights l * (k ((W i).params l) x - (G i).f x) := by
    intro x
    rw [hfeq x]
    ring
  have hpt : ∀ x : X, |(W i).f x - (G i).f x|
      = (W i).weights l * |k ((W i).params l) x - (G i).f x| := by
    intro x
    rw [hdiff x, abs_mul, abs_of_pos hq_pos]
  calc ∫ x, |(W i).f x - (G i).f x| ∂μ
      = ∫ x, (W i).weights l * |k ((W i).params l) x - (G i).f x| ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall hpt
    _ = (W i).weights l * ∫ x, |k ((W i).params l) x - (G i).f x| ∂μ :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (W i).weights l * 2 := mul_le_mul_of_nonneg_left h_lg (le_of_lt hq_pos)
    _ = 2 * (W i).weights l := by ring

  /- @proof-region region.target-node.session.c23d4ed5d5b23561 end -/

end Statlib.Imported
