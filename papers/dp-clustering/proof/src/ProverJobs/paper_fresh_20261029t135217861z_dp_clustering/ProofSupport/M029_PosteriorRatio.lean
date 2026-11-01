import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M027_ConditionalBound
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M025_Actual
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M028_Node_4139154565_e514172c_9252e54b

/- Original module ProverJobs.manual_dp_cons_finish_20261031.PosteriorRatio; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

structure ConcentrationPrior where
  dens : ℝ → ℝ
  measurable_dens : Measurable dens
  nonneg : ∀ a, 0 < a → 0 ≤ dens a
  zero : ∀ a, a ≤ 0 → dens a = 0
  norm : ∫ a, dens a ∂volume.restrict (Set.Ioi (0:ℝ)) = 1
  integrable_dens : Integrable dens (volume.restrict (Set.Ioi (0:ℝ)))
  A2 : ∃ eps delta beta : ℝ, 0<eps ∧ 0<delta ∧ 0<beta ∧
    ∀ a, 0<a → a<eps → (1/delta)*a^beta ≤ dens a ∧ dens a ≤ delta*a^beta

def concentrationIntegral (piDens : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ∫ a, (a^k / dpRisingFactorial a n) * piDens a ∂volume.restrict (Set.Ioi (0:ℝ))

def priorRatio (piDens : ℝ → ℝ) (t n s : ℕ) : ℝ :=
  concentrationIntegral piDens n (t+s) / concentrationIntegral piDens n t

def posteriorRatioIntegrand (C : LocationConfig) (piDens : ℝ → ℝ) (n s : ℕ) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if dpOmega C.c C.theta C.N n (prefixPath x) then dpRatio C.g C.q0 piDens C.t n s (prefixPath x) else 0


lemma source_concentration_spec (C : LocationConfig) (prior : ConcentrationPrior)
    (n s : ℕ) (htn : C.t ≤ n) (hs : 1 ≤ s) (hts : C.t+s ≤ n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      Integrable (fun a : ℝ => (a^k / dpRisingFactorial a n) * prior.dens a)
        (volume.restrict (Set.Ioi (0:ℝ))) ∧ 0 < concentrationIntegral prior.dens n k := by
  have hMpos : 0 < C.M := (C.hgpos 0 ⟨by linarith [C.hc], by linarith [C.hc]⟩).trans_le (C.hgM 0)
  have hgint : Integrable C.g volume := by
    by_contra h
    have hh := C.hgnorm
    rw [integral_undef h] at hh
    exact zero_ne_one hh
  exact (statopia_math_node_4139154565_e514172c C.t C.ht C.c C.hc C.g C.q0 C.theta C.M hMpos
    prior.dens n s htn hs hts C.hg C.hg0 C.hgzero C.hgpos (fun x hx => C.hgM x) C.hgnorm hgint
    C.hq C.hq0 C.hqnorm C.hqint prior.measurable_dens prior.nonneg prior.zero prior.norm prior.integrable_dens prior.A2).1

lemma source_ratio_identity (C : LocationConfig) (prior : ConcentrationPrior)
    (n s : ℕ) (htn : C.t ≤ n) (hs : 1 ≤ s) (hts : C.t+s ≤ n) :
    0 < priorRatio prior.dens C.t n s ∧
    ∀ omega : ℕ → ℝ, 0 < partitionSum C.g C.q0 n C.t (dpXseq n omega) →
      dpRatio C.g C.q0 prior.dens C.t n s omega =
        priorRatio prior.dens C.t n s *
          (partitionSum C.g C.q0 n (C.t+s) (dpXseq n omega) /
            partitionSum C.g C.q0 n C.t (dpXseq n omega)) := by
  classical
  have hMpos : 0 < C.M := (C.hgpos 0 ⟨by linarith [C.hc], by linarith [C.hc]⟩).trans_le (C.hgM 0)
  have hgint : Integrable C.g volume := by
    by_contra h
    have hh := C.hgnorm
    rw [integral_undef h] at hh
    exact zero_ne_one hh
  have h := statopia_math_node_4139154565_e514172c C.t C.ht C.c C.hc C.g C.q0 C.theta C.M hMpos
    prior.dens n s htn hs hts C.hg C.hg0 C.hgzero C.hgpos (fun x hx => C.hgM x) C.hgnorm hgint
    C.hq C.hq0 C.hqnorm C.hqint prior.measurable_dens prior.nonneg prior.zero prior.norm prior.integrable_dens prior.A2
  constructor
  · exact div_pos (h.1 (C.t+s) (by omega) hts).2 (h.1 C.t C.ht htn).2
  · intro omega hD
    exact (h.2 omega hD).2

lemma trueLaw_probability (C : LocationConfig) (p : Fin C.t → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) : IsProbabilityMeasure (dpPlaw C.g C.theta p) := by
  haveI : ∀ j, IsProbabilityMeasure (dpRmeasure C.g C.theta j) := C.hRprob
  constructor
  simp only [dpPlaw, Measure.finset_sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj => hp j), hpsum, ENNReal.ofReal_one]

lemma trueLaw_ae_goodPrefix (C : LocationConfig) (p : Fin C.t → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p),
      (∀ i : Fin n, ∃ j, x i ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c)) ∧
      (∀ j i, i ∈ dpBlock C.c C.theta n (prefixPath x) j → -C.c < x i-C.theta j) := by
  haveI := trueLaw_probability C p hp hpsum
  haveI : ∀ j, IsProbabilityMeasure (dpRmeasure C.g C.theta j) := C.hRprob
  rw [ae_iff, OfflineDPRoot.mixture_product_law (dpPlaw C.g C.theta p) (dpRmeasure C.g C.theta)
    (fun j => ENNReal.ofReal (p j)) rfl n]
  simp only [Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro lab hlab
  have hgood : ∀ᵐ x ∂labelLaw C n lab,
      (∀ i : Fin n, ∃ j, x i ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c)) ∧
      (∀ j i, i ∈ dpBlock C.c C.theta n (prefixPath x) j → -C.c < x i-C.theta j) := by
    filter_upwards [labelLaw_ae_cell C n lab, labelLaw_ae_interior C n lab] with x hx hi
    exact ⟨fun i => ⟨lab i, hx i⟩, hi⟩
  rw [show (Measure.pi (fun i => dpRmeasure C.g C.theta (lab i)))
    {x | ¬ ((∀ i : Fin n, ∃ j, x i ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c)) ∧
      (∀ j i, i ∈ dpBlock C.c C.theta n (prefixPath x) j → -C.c < x i-C.theta j))} = 0 from ae_iff.mp hgood,
    mul_zero]

/-- AE factorization of the actual posterior ratio; no replacement posterior is introduced. -/
lemma posterior_ratio_ae_factor (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (n s : ℕ) (hn : 3 ≤ n) (htn : C.t ≤ n) (hs : 1 ≤ s) (hts : C.t+s ≤ n) :
    posteriorRatioIntegrand C prior.dens n s =ᵐ[Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)]
      (fun x => priorRatio prior.dens C.t n s * ratioIntegrand C n (C.t+s) x) := by
  classical
  filter_upwards [trueLaw_ae_goodPrefix C p hp hpsum n] with x hx
  by_cases hOmega : dpOmega C.c C.theta C.N n (prefixPath x)
  · have hD := (omega_denominator_log_inverse C.c C.R C.L C.r
        ((Real.log (n:ℝ))^((1:ℝ)/(2*(C.t:ℝ)))) C.theta C.N (prefixPath x) C.g C.q0
        C.hg C.hg0 C.hgpos C.hgdiff C.hgderiv ⟨C.M,C.hM,C.hgM⟩ C.hq C.hq0 C.hqint C.hR C.hL C.hr
        (logroot_one_le C.t n hn) C.hT4 C.hN hOmega rfl (by simpa using hx.2) C.hsep
        (by simpa using hx.1) C.ht (by exact_mod_cast (show 1<n by omega))).1
    have hratio := (source_ratio_identity C prior n s htn hs hts).2 (prefixPath x) hD
    simpa only [posteriorRatioIntegrand, ratioIntegrand, if_pos hOmega, Xseq_prefixPath] using hratio
  · simp only [posteriorRatioIntegrand, ratioIntegrand, if_neg hOmega, mul_zero]

/-- Actual finite-sample posterior ratios, bounded by the prior factor times the proved full-partition data bound. -/
theorem posterior_ratio_expectation_bound (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (n s : ℕ) (hn : 3 ≤ n) (htn : C.t ≤ n) (hs : 1 ≤ s) (hts : C.t+s ≤ n) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s x)
      ∂Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)) ≤
      ENNReal.ofReal (priorRatio prior.dens C.t n s) *
        ENNReal.ofReal (denominatorLoss C n * (dpK5 C.U C.m C.c C.theta)^(C.t+s) / ((C.t+s).factorial : ℝ)) := by
  have hfactor := posterior_ratio_ae_factor C prior p hp hpsum n s hn htn hs hts
  have hf : (fun x : Fin n → ℝ => ENNReal.ofReal (posteriorRatioIntegrand C prior.dens n s x)) =ᵐ[
      Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)]
      (fun x => ENNReal.ofReal (priorRatio prior.dens C.t n s * ratioIntegrand C n (C.t+s) x)) :=
    hfactor.mono (fun x hx => congrArg ENNReal.ofReal hx)
  rw [lintegral_congr_ae hf]
  simp_rw [ENNReal.ofReal_mul (source_ratio_identity C prior n s htn hs hts).1.le]
  rw [lintegral_const_mul' _ _]
  · exact mul_le_mul_left' (data_ratio_expectation_bound C p hp hpsum n hn (C.t+s) (by omega)) _
  · exact ENNReal.ofReal_ne_top

end ManualDPCons
end
end DPCompletedProof
