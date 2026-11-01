import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M098_Node_2291078137_86c48b81_e6a93cbc
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M099_Node_1429964664_ddbd65e4_693e6971

/- Original module ProverJobs.manual_dp_root_finish_20261031.FixedAlpha; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported
noncomputable section
namespace OfflineDPRootFixedAlpha

/-- The finite-sample good event used by the genuine fixed-alpha bound. -/
def goodEvent (t n : ℕ) (θ : Fin t → ℝ) (c : ℝ) : Set (ℕ → ℝ) :=
  {ω | (∀ j : Fin t, 1 ≤ (Finset.univ.filter
      (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θ j - c) (θ j + c))).card) ∧
    (∑ j : Fin t, (Finset.univ.filter
      (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θ j - c) (θ j + c))).card = n) ∧
    (∀ i : Fin n, ∀ j : Fin t, ω (i : ℕ) ≠ θ j - c ∧ ω (i : ℕ) ≠ θ j + c)}

lemma goodEvent_measurable (t n : ℕ) (θ : Fin t → ℝ) (c : ℝ) :
    MeasurableSet (goodEvent t n θ c) := by
  classical
  have hcount : ∀ j : Fin t, Measurable (fun ω : ℕ → ℝ =>
      (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θ j - c) (θ j + c))).card) := by
    intro j
    have heq : (fun ω : ℕ → ℝ => (Finset.univ.filter
        (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (θ j - c) (θ j + c))).card) =
        (fun ω : ℕ → ℝ => ∑ i : Fin n,
          if ω (i : ℕ) ∈ Set.Icc (θ j - c) (θ j + c) then (1 : ℕ) else 0) := by
      funext ω
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [heq]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_Icc.preimage (measurable_pi_apply (i : ℕ))) measurable_const)
  have hfirst : MeasurableSet {ω : ℕ → ℝ | ∀ j : Fin t,
      1 ≤ (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈
        Set.Icc (θ j - c) (θ j + c))).card} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const (hcount j))
  have hsum := Finset.measurable_sum Finset.univ (fun j _ => hcount j)
  have hsecond : MeasurableSet {ω : ℕ → ℝ |
      ∑ j : Fin t, (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈
        Set.Icc (θ j - c) (θ j + c))).card = n} :=
    measurableSet_eq_fun hsum measurable_const
  have hthird : MeasurableSet {ω : ℕ → ℝ | ∀ i : Fin n, ∀ j : Fin t,
      ω (i : ℕ) ≠ θ j - c ∧ ω (i : ℕ) ≠ θ j + c} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    exact ((measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const).compl).inter
      ((measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const).compl)
  exact hfirst.inter (hsecond.inter hthird)

/-- Source Theorem 1, fixed-positive-alpha inconsistency half. All original root
hypotheses and the actual EPPF posterior are retained; no probabilistic bound is
introduced as a free premise. -/
theorem fixed_alpha_inconsistency
    (g q0 : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x, 0 ≤ q0 x)
    (hq0_density : ∫⁻ x, ENNReal.ofReal (q0 x) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hT2 : DifferentiableOn ℝ g (Set.Ioo (-c) c) ∧
      ∃ Rd : ℝ, 0 < Rd ∧ ∀ x ∈ Set.Ioo (-c) c, |deriv g x / g x| ≤ Rd)
    (hT3 : ∃ U : ℝ, 0 < U ∧ ∀ y ∈ Set.Icc (0 : ℝ) (2 * c), q0 y + q0 (-y) ≤ U) :
    ∀ αstar : ℝ, 0 < αstar →
      ∀ (t : ℕ) (P : Measure ℝ) (p : Fin t → ℝ) (Rm : Fin t → Measure ℝ)
        (θstar : Fin t → ℝ), IsDataConfig g q0 c t P p Rm θstar →
        ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
          iidLaw P {ω : ℕ → ℝ |
            1 - η < postProb g q0 (Measure.dirac αstar) n t (fun i : Fin n => ω (i : ℕ))}
              ≤ ENNReal.ofReal ε := by
  classical
  intro αstar hα t P p Rm θstar hconfig
  rcases hconfig with ⟨ht, hp, hp1, hR, hReq, hRinj, hsep, hsupp, hT4, hP⟩
  obtain ⟨m,M,hm,hmM,hg_bounds⟩ := hT1
  obtain ⟨L,hL,hnear⟩ := hT4
  have hradii : ∀ j : Fin t, ∃ d : ℝ, 0 < d ∧
      ∀ y ∈ Set.Ioo (θstar j - d) (θstar j + d), L ≤ q0 y := by
    intro j
    obtain ⟨d,hd,hbound⟩ := Metric.eventually_nhds_iff.mp (hnear j)
    refine ⟨d,hd,fun y hy => hbound ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1,hy.2]
  choose delta hdelta hlocal using hradii
  haveI : Nonempty (Fin t) := ⟨⟨0,ht⟩⟩
  have hmin : 0 < ⨅ j : Fin t, delta j := by
    obtain ⟨j,hj⟩ := exists_eq_ciInf_of_finite (f := delta)
    rw [← hj]
    exact hdelta j
  have hPprob : IsProbabilityMeasure P := by
    rw [hP]
    have hmass : (∑ j : Fin t, ENNReal.ofReal (p j) • Rm j) Set.univ = 1 := by
      rw [Measure.finset_sum_apply]
      simp only [Measure.smul_apply, smul_eq_mul, (fun j => (hR j).measure_univ), mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hp j).le), hp1]
      simp
    exact ⟨hmass⟩
  haveI := hPprob
  haveI : IsProbabilityMeasure (iidLaw P) :=
    show IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => P)) from inferInstance
  let c0 : ℝ := αstar * (m * (L * min c (⨅ j : Fin t, delta j))) /
    (M * (t : ℝ) * ((t : ℝ)+1))
  have hc0 : 0 < c0 := by
    dsimp [c0]
    have htR : 0 < (t : ℝ) := by exact_mod_cast ht
    exact div_pos (mul_pos hα (mul_pos hm (mul_pos hL (lt_min hc hmin))))
      (mul_pos (mul_pos (hm.trans_le hmM) htR) (by positivity))
  refine ⟨c0/(1+c0), div_pos hc0 (by positivity), ?_⟩
  have hgood : Tendsto (fun n => iidLaw P (goodEvent t n θstar c)) atTop (𝓝 1) := by
    exact statopia_math_node_1429964664_ddbd65e4 g q0 c t P p Rm θstar hc (by omega)
      hg_meas hg_nonneg hg_support hg_density hq0_meas hq0_nonneg hp hp1 hR hReq hsep hP
  have hgood_real : Tendsto (fun n => (iidLaw P (goodEvent t n θstar c)).toReal)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hgood
  have hcompl_eq : ∀ n, iidLaw P (goodEvent t n θstar c)ᶜ =
      ENNReal.ofReal (1 - (iidLaw P (goodEvent t n θstar c)).toReal) := by
    intro n
    rw [measure_compl (goodEvent_measurable t n θstar c) (measure_ne_top _ _), measure_univ]
    rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hcomp : Tendsto (fun n => iidLaw P (goodEvent t n θstar c)ᶜ) atTop (𝓝 0) := by
    simp_rw [hcompl_eq]
    have hr : Tendsto (fun n => (1 : ℝ) - (iidLaw P (goodEvent t n θstar c)).toReal)
        atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hgood_real)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  intro ε hε
  have hevent : ∀ᶠ n in atTop, iidLaw P (goodEvent t n θstar c)ᶜ < ENNReal.ofReal ε :=
    hcomp.eventually_lt_const (ENNReal.ofReal_pos.mpr hε)
  filter_upwards [eventually_ge_atTop (t+1), hevent] with n hn hprob
  refine le_trans (measure_mono ?_) hprob.le
  intro ω hω
  change ω ∉ goodEvent t n θstar c
  intro hG
  obtain ⟨hcount,hsum,hne⟩ := hG
  have hb := statopia_math_node_2291078137_86c48b81 g q0 c hc hg_meas hg_nonneg hg_support
    hq0_meas hq0_nonneg hq0_density m M hm hmM hg_bounds t ht θstar hsep L hL delta hdelta hlocal
    n hn (fun i : Fin n => ω (i : ℕ)) hcount hsum hne αstar hα
  change 1 - c0 / (1+c0) < _ at hω
  exact (not_lt_of_ge (hb.1.trans_eq hb.2)) hω

end OfflineDPRootFixedAlpha
end
end DPCompletedProof
