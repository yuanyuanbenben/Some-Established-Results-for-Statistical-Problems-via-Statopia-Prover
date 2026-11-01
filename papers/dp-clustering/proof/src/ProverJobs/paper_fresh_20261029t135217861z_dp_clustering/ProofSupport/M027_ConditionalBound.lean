import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M020_Conditional
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M026_Pointwise

/- Original module ProverJobs.manual_dp_cons_finish_20261031.ConditionalBound; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

lemma window_sum_lintegral_bound (C : LocationConfig) (n : ℕ) (hn : 1 ≤ n)
    (lab : Fin n → Fin C.t) (hcounts : ∀ j, 1 ≤ labelCounts C lab j)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (partitionSum C.g C.q0 n k x)
      ∂Measure.pi (fun i => volume.restrict (Set.Icc (C.theta (lab i)-C.c) (C.theta (lab i)+C.c)))) ≤
    ENNReal.ofReal ((∏ j : Fin C.t, ((labelCounts C lab j).factorial : ℝ) / (labelCounts C lab j : ℝ)^2) *
      (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ)) := by
  let mu : Fin n → Measure ℝ := fun i => volume.restrict (Set.Icc (C.theta (lab i)-C.c) (C.theta (lab i)+C.c))
  haveI : ∀ i, IsFiniteMeasure (mu i) := fun i => isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hi := partitionSum_integrable C.g C.q0 C.hg C.hg0 C.M C.hM C.hgM C.hq C.hq0 C.hQ mu k
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (partitionSum_nonneg C.g C.q0 C.hg0 C.hq0 n k))]
  apply ENNReal.ofReal_le_ofReal
  exact window_sum_integral_bound C.t C.ht C.c C.hc C.g C.q0 C.theta C.m C.U C.hm C.hU
    C.hg C.hg0 C.hgzero C.hglo C.hgnorm C.M C.hM C.hgM C.hq C.hq0 C.hqnorm C.hQ
    C.hT3 C.hsep n hn lab hcounts k hk

/-- The actual conditional data likelihood ratio has the full-partition expectation bound. -/
theorem conditional_ratio_bound (C : LocationConfig) (n : ℕ) (hn : 3 ≤ n)
    (lab : Fin n → Fin C.t) (k : ℕ) (hk : 1 ≤ k) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (ratioIntegrand C n k x) ∂labelLaw C n lab) ≤
      ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ)) := by
  classical
  by_cases hcounts : ∀ j, 1 ≤ labelCounts C lab j
  · let countFactor : ℝ := ∏ j : Fin C.t, (labelCounts C lab j : ℝ) / ((labelCounts C lab j-1).factorial : ℝ)
    let coeffFactor : ℝ := ∏ j : Fin C.t, ((labelCounts C lab j).factorial : ℝ) / (labelCounts C lab j : ℝ)^2
    have hcount : 0 ≤ countFactor := Finset.prod_nonneg (fun j hj => by positivity)
    have hA : 0 ≤ denominatorLoss C n * countFactor := mul_nonneg (denominatorLoss_nonneg C n) hcount
    have hpoint : ∀ᵐ x ∂labelLaw C n lab,
        ratioIntegrand C n k x ≤ (denominatorLoss C n * countFactor) * partitionSum C.g C.q0 n k x /
          (∏ i, C.g (x i-C.theta (lab i))) := by
      filter_upwards [labelLaw_ae_cell C n lab, labelLaw_ae_interior C n lab] with x hcell hinterior
      have hh := omega_indicator_partition_ratio_label C.c C.R C.L C.r
        ((Real.log (n:ℝ))^((1:ℝ)/(2*(C.t:ℝ)))) C.theta C.N (prefixPath x) C.g C.q0
        C.hg C.hg0 C.hgpos C.hgdiff C.hgderiv ⟨C.M,C.hM,C.hgM⟩ C.hq C.hq0 C.hqint C.hR C.hL C.hr
        (logroot_one_le C.t n hn) C.hT4 C.hN rfl
        (by simpa using hinterior) C.hsep C.ht (by exact_mod_cast (show 1<n by omega)) k lab
        (by simpa using hcell)
      simpa only [Xseq_prefixPath, prefixPath_apply, ratioIntegrand, countFactor, labelCounts, denominatorLoss] using hh
    have hbound := ManualDPConsDensity.window_density_cancel
      (fun i y => C.g (y-C.theta (lab i)))
      (fun i => Set.Icc (C.theta (lab i)-C.c) (C.theta (lab i)+C.c))
      (fun i => C.hg.comp (measurable_id.sub_const _)) (fun i y => C.hg0 _) (fun i => measurableSet_Icc)
      (fun i y hy => C.hgzero _ (by intro hm; exact hy ⟨by linarith [hm.1], by linarith [hm.2]⟩))
      (fun i y hy => C.hgpos _ ⟨by linarith [hy.1], by linarith [hy.2]⟩)
      (denominatorLoss C n * countFactor) hA (partitionSum C.g C.q0 n k) (ratioIntegrand C n k) hpoint
    have hcoef := window_sum_lintegral_bound C n (by omega) lab hcounts k hk
    apply le_trans hbound
    apply le_trans (mul_le_mul_left' hcoef (ENNReal.ofReal (denominatorLoss C n * countFactor)))
    rw [← ENNReal.ofReal_mul hA]
    have hcanc := configuration_cancellation (labelCounts C lab) hcounts
    have heq : (denominatorLoss C n * countFactor) *
        (coeffFactor * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ)) =
        denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ) := by
      calc _ = denominatorLoss C n * (countFactor * coeffFactor) * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ) := by ring
        _ = _ := by rw [show countFactor*coeffFactor=1 from hcanc, mul_one]
    exact le_of_eq (congrArg ENNReal.ofReal heq)
  · have hex : ∃ j, labelCounts C lab j = 0 := by
      obtain ⟨j,hj⟩ := not_forall.mp hcounts
      exact ⟨j, by omega⟩
    obtain ⟨j,hj⟩ := hex
    have hzero : (fun x : Fin n → ℝ => ENNReal.ofReal (ratioIntegrand C n k x)) =ᵐ[labelLaw C n lab] 0 := by
      filter_upwards [labelLaw_ae_cell C n lab] with x hcell
      have hh := OfflineDPLabelCells.empty_label_not_omega C.c C.theta C.hsep C.N C.hN lab (prefixPath x)
        (by simpa using hcell) j hj
      simp [ratioIntegrand, hh]
    rw [lintegral_congr_ae hzero]
    simp

/-- Full finite-sample mixture data law, with all label vectors summed exactly. -/
theorem data_ratio_expectation_bound (C : LocationConfig) (p : Fin C.t → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (ratioIntegrand C n k x)
      ∂Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)) ≤
      ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ)) := by
  haveI : ∀ j, IsProbabilityMeasure (dpRmeasure C.g C.theta j) := C.hRprob
  have hsum : ∑ j, ENNReal.ofReal (p j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => hp j), hpsum, ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure (dpPlaw C.g C.theta p) := ⟨by
    simp only [dpPlaw, Measure.finset_sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact hsum⟩
  rw [OfflineDPRoot.mixture_product_lintegral (dpPlaw C.g C.theta p) (dpRmeasure C.g C.theta)
    (fun j => ENNReal.ofReal (p j)) rfl n]
  calc (∑ lab : Fin n → Fin C.t, (∏ i, ENNReal.ofReal (p (lab i))) *
        ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (ratioIntegrand C n k x) ∂Measure.pi (fun i => dpRmeasure C.g C.theta (lab i)))
      ≤ ∑ lab : Fin n → Fin C.t, (∏ i, ENNReal.ofReal (p (lab i))) *
        ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^k / (k.factorial : ℝ)) := by
          apply Finset.sum_le_sum
          intro lab hlab
          exact mul_le_mul_left' (conditional_ratio_bound C n hn lab k hk) _
    _ = _ := by rw [← Finset.sum_mul, OfflineDPRoot.label_weights_sum_one _ hsum n, one_mul]

end ManualDPCons
end
end DPCompletedProof
