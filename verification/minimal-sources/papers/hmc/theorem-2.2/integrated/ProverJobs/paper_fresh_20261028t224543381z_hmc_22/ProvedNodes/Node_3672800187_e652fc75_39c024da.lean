import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_hmc_22.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_hmc_22.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_3672800187_e652fc75 : ∀ (d : ℕ) (s : Fin d → Set ℝ)
    (hs : ∀ i : Fin d, MeasurableSet (s i)),
    ∫⁻ x in Set.univ.pi s,
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2))
        ∂(volume : Measure (Fin d → ℝ))
      = ∏ i : Fin d, ∫⁻ t in s i, ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) := by
  /- @proof-region region.target-node.session.a358737109874275 begin -/
  intro d s hs
  set g : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) with hgdef
  have hg : Measurable g := by rw [hgdef]; measurability
  have hpt : ∀ x : Fin d → ℝ, ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (x i) ^ 2)) = ∏ i : Fin d, g (x i) := by
    intro x
    rw [hgdef]
    have h1 : -(1 / 2) * ∑ i : Fin d, (x i) ^ 2 = ∑ i : Fin d, -((x i) ^ 2) / 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
    intro i _
    positivity
  have hU : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : ∀ x : Fin d → ℝ, (Set.univ.pi s).indicator (fun y : Fin d → ℝ => ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (y i) ^ 2))) x = ∏ i : Fin d, (s i).indicator g (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, hpt x]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem ((Set.mem_univ_pi.mp hx) i)]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra h
        push_neg at h
        exact hx (Set.mem_univ_pi.mpr h)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi g)]
  have key : ∀ (d : ℕ) (f : Fin d → ℝ → ENNReal), (∀ i, Measurable (f i)) →
      ∫⁻ x : (Fin d → ℝ), (∏ i : Fin d, f i (x i)) ∂(volume : Measure (Fin d → ℝ))
        = ∏ i : Fin d, ∫⁻ t, f i t ∂(volume : Measure ℝ) := by
    intro d
    induction d with
    | zero =>
        intro f hf
        simp only [Finset.univ_eq_empty, Finset.prod_empty]
        rw [MeasureTheory.lintegral_one, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
        simp
    | succ n ih =>
        intro f hf
        set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) with he
        have hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
            ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
          rw [he]
          simpa using MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
        have hg_prod : Measurable (fun b : Fin n → ℝ => ∏ j : Fin n, f ((Fin.last n).succAbove j) (b j)) := by
          apply Finset.measurable_prod
          intro j _
          exact (hf ((Fin.last n).succAbove j)).comp (measurable_pi_apply j)
        have hG : Measurable (fun y : ℝ × (Fin n → ℝ) => f (Fin.last n) y.1 * ∏ j : Fin n, f ((Fin.last n).succAbove j) (y.2 j)) := by
          apply Measurable.mul
          · exact (hf (Fin.last n)).comp measurable_fst
          · exact hg_prod.comp measurable_snd
        have hstep : ∫⁻ x : (Fin (n + 1) → ℝ), (∏ i : Fin (n + 1), f i (x i)) ∂(volume : Measure (Fin (n + 1) → ℝ))
            = ∫⁻ y : ℝ × (Fin n → ℝ), (f (Fin.last n) y.1 * ∏ j : Fin n, f ((Fin.last n).succAbove j) (y.2 j)) ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
          have hpt : (fun x : Fin (n + 1) → ℝ => ∏ i : Fin (n + 1), f i (x i))
              = fun x => f (Fin.last n) (e x).1 * ∏ j : Fin n, f ((Fin.last n).succAbove j) ((e x).2 j) := by
            funext x
            have hex : e x = (x (Fin.last n), fun j => x ((Fin.last n).succAbove j)) := by rw [he]; rfl
            rw [hex]
            exact Fin.prod_univ_succAbove (fun i => f i (x i)) (Fin.last n)
          rw [hpt]
          exact hmp.lintegral_comp hG
        have hfactor : ∫⁻ y : ℝ × (Fin n → ℝ), (f (Fin.last n) y.1 * ∏ j : Fin n, f ((Fin.last n).succAbove j) (y.2 j)) ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
            = (∫⁻ a : ℝ, f (Fin.last n) a ∂(volume : Measure ℝ)) * (∫⁻ b : Fin n → ℝ, (∏ j : Fin n, f ((Fin.last n).succAbove j) (b j)) ∂(volume : Measure (Fin n → ℝ))) := by
          exact MeasureTheory.lintegral_prod_mul (f := fun a : ℝ => f (Fin.last n) a) (g := fun b : Fin n → ℝ => ∏ j : Fin n, f ((Fin.last n).succAbove j) (b j)) (hf (Fin.last n)).aemeasurable hg_prod.aemeasurable
        have hIH : ∫⁻ b : Fin n → ℝ, (∏ j : Fin n, f ((Fin.last n).succAbove j) (b j)) ∂(volume : Measure (Fin n → ℝ))
            = ∏ j : Fin n, ∫⁻ t, f ((Fin.last n).succAbove j) t ∂(volume : Measure ℝ) :=
          ih (fun j => f ((Fin.last n).succAbove j)) (fun j => hf _)
        rw [hstep, hfactor, hIH]
        rw [Fin.prod_univ_succAbove (fun i : Fin (n + 1) => ∫⁻ t, f i t ∂(volume : Measure ℝ)) (Fin.last n)]
  rw [← MeasureTheory.lintegral_indicator hU]
  rw [show (fun x : Fin d → ℝ => (Set.univ.pi s).indicator (fun y : Fin d → ℝ => ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i : Fin d, (y i) ^ 2))) x) = fun x => ∏ i : Fin d, (s i).indicator g (x i) from funext hind]
  rw [key d (fun i => (s i).indicator g) (fun i => hg.indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [MeasureTheory.lintegral_indicator (hs i)]
  /- @proof-region region.target-node.session.a358737109874275 end -/

end Statlib.Imported

end

