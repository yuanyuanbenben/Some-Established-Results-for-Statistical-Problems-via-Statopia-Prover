import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Vocabulary
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.Base
import ProverJobs.job_paper_df5fdc450bf24d85b08215e07b20fdad.ExternalNodes.Node_4e38c0b212aeaf238af1

namespace PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open _root_.PaperProofTasks.job_paper_df5fdc450bf24d85b08215e07b20fdad.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
namespace Statlib.Imported
open _root_.Statlib

set_option autoImplicit false in
theorem statopia_math_node_2137929089_5f7d7f94 : ∃ K : ℝ, 0 < K ∧
      ∀ q : ℝ, 1 ≤ q →
        LqNorm (fun x : ℝ => x) q (ProbabilityTheory.gaussianReal 0 (1 : NNReal))
          ≤ ENNReal.ofReal (K * q) := by
  /- @proof-region region.target-node.session.45c6a303ed7de277 begin -/
  obtain ⟨_, _, hC⟩ := ext_model_2
  have hd : ∃ K4 : ℝ, 0 < K4 ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|ω| / K4))
        ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)) ≤ 2 := by
    have hbound : Integrable (fun x : ℝ => Real.exp (|x|))
        (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) := by
      simpa using
        Statlib.StatFoundation.RandomVariable.Gaussian.integrable_exp_abs_gaussianReal
          (0 : ℝ) (1 : NNReal) (1 : ℝ)
    have hone : (∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) = 1 := by
      simp
    have hmain : Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, Real.exp (|x| / ((n : ℝ) + 1))
          ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)))
        Filter.atTop
        (nhds (∫ x : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)))) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := ProbabilityTheory.gaussianReal 0 (1 : NNReal))
        (F := fun n : ℕ => fun x : ℝ => Real.exp (|x| / ((n : ℝ) + 1)))
        (f := fun _ => (1 : ℝ))
        (bound := fun x : ℝ => Real.exp (|x|)) ?_ hbound ?_ ?_
      · intro n
        have hc : Continuous fun x : ℝ => Real.exp (|x| / ((n : ℝ) + 1)) := by fun_prop
        exact hc.aestronglyMeasurable
      · intro n
        refine Filter.Eventually.of_forall fun x => ?_
        have hle : |x| / ((n : ℝ) + 1) ≤ |x| := by
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
            linarith
          rw [div_le_iff₀ hpos]
          nlinarith [abs_nonneg x]
        have hnn : ‖Real.exp (|x| / ((n : ℝ) + 1))‖ = Real.exp (|x| / ((n : ℝ) + 1)) := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (|x| / ((n : ℝ) + 1)))]
        rw [hnn]
        exact Real.exp_le_exp.2 hle
      · refine Filter.Eventually.of_forall fun x => ?_
        have h2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h3 : Filter.Tendsto (fun n : ℕ => |x| * (1 / ((n : ℝ) + 1)))
            Filter.atTop (nhds (|x| * 0)) := tendsto_const_nhds.mul h2
        have h4 : Filter.Tendsto (fun n : ℕ => |x| / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
          simpa [div_eq_mul_inv] using h3
        simpa using (Real.continuous_exp.tendsto 0).comp h4
    have htend : Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, Real.exp (|x| / ((n : ℝ) + 1))
          ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)))
        Filter.atTop (nhds 1) := by
      simpa [hone] using hmain
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        (∫ x : ℝ, Real.exp (|x| / ((n : ℝ) + 1))
          ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) < 2 := by
      have hlt : ∀ᶠ n : ℕ in Filter.atTop,
          (∫ x : ℝ, Real.exp (|x| / ((n : ℝ) + 1))
            ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) < 3 / 2 :=
        (tendsto_order.1 htend).2 (3 / 2) (by norm_num)
      filter_upwards [hlt] with n hn using lt_trans hn (by norm_num)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    have hfin : (∫ x : ℝ, Real.exp (|x| / ((N : ℝ) + 1))
        ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) ≤ 2 := le_of_lt (hN N le_rfl)
    refine ⟨(N : ℝ) + 1, by positivity, ?_⟩
    have hInt : Integrable (fun x : ℝ => Real.exp (|x| / ((N : ℝ) + 1)))
        (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) := by
      have h := Statlib.StatFoundation.RandomVariable.Gaussian.integrable_exp_abs_gaussianReal
        (0 : ℝ) (1 : NNReal) (1 / ((N : ℝ) + 1))
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have heq : ENNReal.ofReal (∫ x : ℝ, Real.exp (|x| / ((N : ℝ) + 1))
          ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)))
        = ∫⁻ x, ENNReal.ofReal (Real.exp (|x| / ((N : ℝ) + 1)))
            ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun x => (Real.exp_pos (|x| / ((N : ℝ) + 1))).le)
    rw [← heq]
    calc ENNReal.ofReal (∫ x : ℝ, Real.exp (|x| / ((N : ℝ) + 1))
          ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal)))
        ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hfin
      _ = 2 := by simp
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, _, _, _⟩ :=
    hC ℝ (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) (fun x : ℝ => x) measurable_id
  obtain ⟨K2, hK2ge, _, hK2⟩ := h10 hd
  exact ⟨K2, lt_of_lt_of_le zero_lt_one hK2ge, hK2⟩
  /- @proof-region region.target-node.session.45c6a303ed7de277 end -/

end Statlib.Imported

