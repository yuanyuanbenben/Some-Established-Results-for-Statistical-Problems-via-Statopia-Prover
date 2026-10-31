import ProverJobs.manual_dp_cons_finish_20261031.MarginalTransport
import ProverJobs.manual_dp_cons_finish_20261031.WindowCoefficients
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace ManualDPCons
open Statlib.Imported

def partitionSum (g q0 : ℝ → ℝ) (n k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 x B

lemma marginal_as_Q0_integral {n : ℕ} (g q0 : ℝ → ℝ)
    (hq : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z)
    (x : Fin n → ℝ) (B : Finset (Fin n)) :
    dpMargLik g q0 x B = ∫ z, ∏ i ∈ B, g (x i-z) ∂dpQ0 q0 := by
  classical
  rw [dpQ0, integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
    (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by simp [dpMargLik, ENNReal.toReal_ofReal (hq0 z), smul_eq_mul, mul_comm])

lemma partitionSum_nonneg (g q0 : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hq0 : ∀ z, 0 ≤ q0 z)
    (n k : ℕ) (x : Fin n → ℝ) : 0 ≤ partitionSum g q0 n k x := by
  classical
  apply Finset.sum_nonneg
  intro A hA
  apply Finset.prod_nonneg
  intro B hB
  exact mul_nonneg (by positivity) (integral_nonneg (fun z =>
    mul_nonneg (Finset.prod_nonneg (fun i hi => hg0 _)) (hq0 z)))

lemma partitionSum_integrable {n : ℕ} (g q0 : ℝ → ℝ)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ z, g z ≤ M)
    (hq : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hQ : IsProbabilityMeasure (dpQ0 q0))
    (mu : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (mu i)] (k : ℕ) :
    Integrable (partitionSum g q0 n k) (Measure.pi mu) := by
  classical
  haveI := hQ
  unfold partitionSum
  apply integrable_finset_sum
  intro A hA
  simp_rw [marginal_as_Q0_integral g q0 hq hq0, Finset.prod_mul_distrib]
  apply Integrable.const_mul
  apply partition_product_integrable mu (dpQ0 q0) (fun z x : ℝ => g (x-z))
    (hg.comp (measurable_snd.sub measurable_fst)) M hM (fun z x => hg0 _) (fun z x => hgM _)

/-- Integrate all model partitions on a fixed label cell and apply the closed coefficient bound. -/
theorem window_sum_integral_bound
    (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (theta : Fin t → ℝ) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgzero : ∀ z, z ∉ Set.Icc (-c) c → g z = 0)
    (hglo : ∀ z ∈ Set.Icc (-c) c, m ≤ g z) (hgnorm : ∫ z, g z ∂volume = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ z, g z ≤ M)
    (hq : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hqnorm : ∫ z, q0 z ∂volume = 1)
    (hQ : IsProbabilityMeasure (dpQ0 q0))
    (hT3 : ∀ j y, y ∈ Set.Icc (0 : ℝ) (2 * c) → q0 (theta j + y) + q0 (theta j - y) ≤ U)
    (hsep : ∀ j k, j ≠ k → 2 * c < |theta j - theta k|)
    (n : ℕ) (hn : 1 ≤ n) (lab : Fin n → Fin t)
    (hnclass : ∀ l, 1 ≤ (Finset.univ.filter (fun i => lab i = l)).card)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : Fin n → ℝ, partitionSum g q0 n k x
      ∂Measure.pi (fun i => volume.restrict (Set.Icc (theta (lab i) - c) (theta (lab i) + c)))) ≤
      (∏ l : Fin t, (((Finset.univ.filter (fun i => lab i = l)).card.factorial : ℝ) /
        (((Finset.univ.filter (fun i => lab i = l)).card : ℝ) ^ 2))) *
          (dpK5 U m c theta) ^ k / (k.factorial : ℝ) := by
  classical
  let mu : Fin n → Measure ℝ := fun i => volume.restrict (Set.Icc (theta (lab i) - c) (theta (lab i) + c))
  haveI : ∀ i, IsFiniteMeasure (mu i) := fun i => isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  haveI := hQ
  have htermInt : ∀ A : Finset (Finset (Fin n)),
      Integrable (fun x => ∏ B ∈ A, ((B.card-1).factorial : ℝ) * dpMargLik g q0 x B) (Measure.pi mu) := by
    intro A
    simp_rw [marginal_as_Q0_integral g q0 hq hq0, Finset.prod_mul_distrib]
    apply Integrable.const_mul
    exact partition_product_integrable mu (dpQ0 q0) (fun z x : ℝ => g (x-z))
      (hg.comp (measurable_snd.sub measurable_fst)) M hM (fun z x => hg0 _) (fun z x => hgM _) A
  unfold partitionSum
  rw [integral_finset_sum _ (fun A hA => htermInt A)]
  have hbounds := window_partition_bound t ht c hc g q0 theta m U hm hU hg hg0 hgzero hglo hgnorm
    hq hq0 hqnorm hT3 hsep n hn lab hnclass k hk
  convert hbounds using 1
  apply Finset.sum_congr rfl
  intro A hA
  exact window_partition_integral c hc g q0 theta lab hg hg0 M hM hgM hq hq0 hQ A k
    (Finset.mem_filter.mp hA).2

lemma factorial_cancellation (a : ℕ) (ha : 1 ≤ a) :
    ((a : ℝ) / ((a-1).factorial : ℝ)) * ((a.factorial : ℝ) / (a : ℝ)^2) = 1 := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hf0 : ((a-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a-1)
  have hfac : (a.factorial : ℝ) = (a : ℝ) * ((a-1).factorial : ℝ) := by
    have hh : a.factorial = a * (a-1).factorial := by
      cases a with
      | zero => omega
      | succ a => simp [Nat.factorial_succ]
    exact_mod_cast hh
  rw [hfac]
  field_simp

lemma configuration_cancellation {t : ℕ} (counts : Fin t → ℕ) (hc : ∀ j, 1 ≤ counts j) :
    (∏ j, (counts j : ℝ) / ((counts j-1).factorial : ℝ)) *
      (∏ j, ((counts j).factorial : ℝ) / (counts j : ℝ)^2) = 1 := by
  classical
  rw [← Finset.prod_mul_distrib]
  simp only [factorial_cancellation _ (hc _), Finset.prod_const_one]

#print axioms partitionSum_integrable
#print axioms window_sum_integral_bound
#print axioms configuration_cancellation
end ManualDPCons
