import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M029_PosteriorRatio
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions

/- Original module ProverJobs.manual_dp_root_finish_20261031.NativePosterior; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Statlib.Imported ManualDPCons
noncomputable section
namespace OfflineDPNativePosterior

def concentrationFactor (piDens : ℝ → ℝ) (n k : ℕ) : ℝ :=
  ∫ α : ℝ, (α^k / dpRisingFactorial α n) * piDens α

def partitionKernelSum (g q0 : ℝ → ℝ) (n k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ A ∈ dpTau n k, ∏ B ∈ A,
    ((B.card - 1).factorial : ℝ) * dpMargLik g q0 x B

/-- The concentration-prior coefficient and the complete kernel partition sum
factor exactly. This is the actual dpNpost, not a replacement posterior. -/
theorem dpNpost_factor (g q0 piDens : ℝ → ℝ) (n k : ℕ) (x : Fin n → ℝ) :
    dpNpost g q0 piDens n k x =
      concentrationFactor piDens n k * partitionKernelSum g q0 n k x := by
  classical
  have hcard : ∀ A ∈ dpTau n k, A.card = k := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2.1
  have hfun : (fun α : ℝ => (∑ A ∈ dpTau n k,
      dpPartPrior α n A * ∏ B ∈ A, dpMargLik g q0 x B) * piDens α) =
      (fun α : ℝ => (α^k / dpRisingFactorial α n * piDens α) *
        partitionKernelSum g q0 n k x) := by
    funext α
    rw [partitionKernelSum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    rw [dpPartPrior, hcard A hA, Finset.prod_mul_distrib]
    ring
  rw [dpNpost, hfun, integral_mul_const]
  rfl



def normalizedDensity (pidens : ℝ → ℝ) (a : ℝ) : ℝ :=
  if 0 < a then max (pidens a) 0 else 0

lemma normalizedDensity_nonneg (pidens : ℝ → ℝ) (a : ℝ) : 0 ≤ normalizedDensity pidens a := by
  unfold normalizedDensity
  split_ifs <;> simp
lemma normalizedDensity_zero (pidens : ℝ → ℝ) (a : ℝ) (ha : a ≤ 0) : normalizedDensity pidens a = 0 := by
  simp only [normalizedDensity, if_neg (not_lt.mpr ha)]
lemma normalizedDensity_measurable (pidens : ℝ → ℝ) (hp : Measurable pidens) :
    Measurable (normalizedDensity pidens) :=
  Measurable.ite measurableSet_Ioi (hp.max measurable_const) measurable_const

/-- This representative preserves the actual positive-supported concentration prior. -/
lemma prior_eq_normalized (π : Measure ℝ) (pidens : ℝ → ℝ)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0 < a) :
    π = volume.withDensity (fun a => ENNReal.ofReal (normalizedDensity pidens a)) := by
  have hind : (fun a => ENNReal.ofReal (normalizedDensity pidens a)) =
      (Set.Ioi (0:ℝ)).indicator (fun a => ENNReal.ofReal (pidens a)) := by
    funext a
    by_cases ha : 0 < a <;> simp [normalizedDensity,ha]
  rw [hind, withDensity_indicator measurableSet_Ioi, ← restrict_withDensity measurableSet_Ioi,
    ← hpi]
  exact (Measure.restrict_eq_self_of_ae_mem hpos).symm

lemma normalizedDensity_A2 (pidens : ℝ → ℝ) (hA2 : A2Cond pidens) :
    ∃ eps delta beta : ℝ, 0<eps ∧ 0<delta ∧ 0<beta ∧
      ∀ a, 0<a → a<eps → (1/delta)*a^beta ≤ normalizedDensity pidens a ∧
        normalizedDensity pidens a ≤ delta*a^beta := by
  obtain ⟨eps,delta,beta,he,hd,hb,hbound⟩ := hA2
  refine ⟨eps,delta,beta,he,hd,hb,?_⟩
  intro a ha hae
  obtain ⟨hl,hu⟩ := hbound a ha hae
  have hnn : 0 ≤ pidens a := (div_pos (Real.rpow_pos_of_pos ha beta) hd).le.trans hl
  simp only [normalizedDensity,if_pos ha,max_eq_left hnn]
  refine ⟨?_,hu⟩
  convert hl using 1 <;> ring

/-- All analytic prior fields are discharged from the source prior, not postulated. -/
def concentrationPriorOf (π : Measure ℝ) [IsProbabilityMeasure π]
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (hA2 : A2Cond pidens) : ConcentrationPrior := by
  let pd := normalizedDensity pidens
  have hmeas := normalizedDensity_measurable pidens hp
  have hnn := normalizedDensity_nonneg pidens
  have hmeasure := prior_eq_normalized π pidens hpi hpos
  have hmass : π (Set.Ioi (0:ℝ)) = 1 := by
    calc π (Set.Ioi (0:ℝ)) = π Set.univ := measure_congr (hpos.mono (fun a ha => by
      apply propext
      change (0<a ↔ True)
      exact iff_true_intro ha))
         _ = 1 := measure_univ
  have hlin : ∫⁻ a in Set.Ioi (0:ℝ), ENNReal.ofReal (pd a) = 1 := by
    rw [hmeasure,withDensity_apply _ measurableSet_Ioi] at hmass
    exact hmass
  have hint : Integrable pd (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Eventually.of_forall hnn)).mp
    rw [hlin]
    exact ENNReal.one_ne_top
  have hnorm : ∫ a, pd a ∂volume.restrict (Set.Ioi (0:ℝ)) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas.aestronglyMeasurable,hlin]
    simp
  exact ⟨pd,hmeas,fun a _ => hnn a,fun a ha => normalizedDensity_zero pidens a ha,
    hnorm,hint,normalizedDensity_A2 pidens hA2⟩

lemma tau_eq (n k : ℕ) : dpTau n k = tau n k := by
  classical
  ext A
  simp [dpTau,tau,dpIsPartition,IsPartitionOf]

lemma jointMass_factor (g q0 : ℝ → ℝ) (π : Measure ℝ) (n k : ℕ) (x : Fin n → ℝ) :
    jointMass g q0 π n k x = (∫ a, a^k / ascFact a n ∂π) *
      partitionKernelSum g q0 n k x := by
  classical
  have hcard : ∀ A ∈ tau n k, A.card = k := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2.1
  unfold jointMass
  have hterm : ∀ A ∈ tau n k, prA π n A * ∏ B ∈ A, margLik g q0 B x =
      (∫ a, a^k / ascFact a n ∂π) *
        ∏ B ∈ A, (((B.card-1).factorial:ℝ) * dpMargLik g q0 x B) := by
    intro A hA
    rw [prA]
    simp only [eppf,hcard A hA,integral_mul_const,Finset.prod_mul_distrib,dpMargLik,margLik]
    ring
  rw [Finset.sum_congr rfl hterm,← Finset.mul_sum]
  rw [partitionKernelSum,tau_eq]

/-- Finite-density change of measure; no integrability hypothesis is needed for
this equality of Bochner integral conventions. -/
lemma normalized_integral (π : Measure ℝ) (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (f : ℝ → ℝ) :
    (∫ a, f a ∂π) = ∫ a, f a * normalizedDensity pidens a := by
  rw [prior_eq_normalized π pidens hpi hpos,
    integral_withDensity_eq_integral_toReal_smul
      (normalizedDensity_measurable pidens hp).ennreal_ofReal
      (Eventually.of_forall (fun a => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with a
  simp only [ENNReal.toReal_ofReal (normalizedDensity_nonneg pidens a),smul_eq_mul,mul_comm]

/-- Exact bridge from the native integrated posterior numerator to the original
partition numerator, with the original concentration measure unchanged. -/
theorem native_numerator_eq (g q0 : ℝ → ℝ) (π : Measure ℝ)
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (n k : ℕ) (x : Fin n → ℝ) :
    dpNpost g q0 (normalizedDensity pidens) n k x = jointMass g q0 π n k x := by
  rw [dpNpost_factor,jointMass_factor]
  congr 1
  exact (normalized_integral π pidens hp hpi hpos (fun a => a^k / ascFact a n)).symm

/-- Actual posterior probabilities agree, including the zero-evidence convention. -/
theorem native_posterior_eq (g q0 : ℝ → ℝ) (π : Measure ℝ)
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (n k : ℕ) (x : Fin n → ℝ) :
    dpPostK g q0 (normalizedDensity pidens) n k x = postProb g q0 π n k x := by
  classical
  have hZ : dpZpost g q0 (normalizedDensity pidens) n x =
      ∑ j ∈ Finset.Icc 1 n, jointMass g q0 π n j x := by
    unfold dpZpost
    exact Finset.sum_congr rfl (fun j _ => native_numerator_eq g q0 π pidens hp hpi hpos n j x)
  unfold dpPostK postProb
  rw [hZ,native_numerator_eq g q0 π pidens hp hpi hpos]
  split_ifs with h
  · rw [h,div_zero]
  · rfl

lemma native_sample_posterior_eq (g q0 : ℝ → ℝ) (π : Measure ℝ)
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (n k : ℕ) (ω : ℕ → ℝ) :
    dpPostProb g q0 (normalizedDensity pidens) n k ω =
      postProb g q0 π n k (dpXseq n ω) :=
  native_posterior_eq g q0 π pidens hp hpi hpos n k _

@[simp] lemma concentrationPriorOf_dens (π : Measure ℝ) [IsProbabilityMeasure π]
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (hA2 : A2Cond pidens) :
    (concentrationPriorOf π pidens hp hpi hpos hA2).dens = normalizedDensity pidens := rfl

lemma prior_eq_concentrationPriorOf (π : Measure ℝ) [IsProbabilityMeasure π]
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (hA2 : A2Cond pidens) :
    π = volume.withDensity (fun a => ENNReal.ofReal
      ((concentrationPriorOf π pidens hp hpi hpos hA2).dens a)) :=
  prior_eq_normalized π pidens hpi hpos

lemma native_ratio_eq (g q0 : ℝ → ℝ) (π : Measure ℝ)
    (pidens : ℝ → ℝ) (hp : Measurable pidens)
    (hpi : π = volume.withDensity (fun a => ENNReal.ofReal (pidens a)))
    (hpos : ∀ᵐ a ∂π, 0<a) (t n s : ℕ) (ω : ℕ → ℝ) :
    dpRatio g q0 (normalizedDensity pidens) t n s ω =
      postProb g q0 π n (t+s) (dpXseq n ω) / postProb g q0 π n t (dpXseq n ω) := by
  classical
  unfold dpRatio
  simp only [native_sample_posterior_eq g q0 π pidens hp hpi hpos]
  split_ifs with h
  · rw [h,div_zero]
  · rfl

end OfflineDPNativePosterior
end
end DPCompletedProof
