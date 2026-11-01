import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M020_Conditional
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M080_Node_1466837249_dca9d403_f0505257

/- Original module ProverJobs.manual_dp_root_finish_20261031.GoodOmega; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators
open Statlib.Imported ManualDPCons
noncomputable section
namespace OfflineDPRootGoodOmega

/-- The original good event has a different default maximum on empty blocks.
Those defaults are immaterial once N_j >= 1 is required. -/
def sourceOmega (C : LocationConfig) (n : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∀ j : Fin C.t,
    let B := dpBlock C.c C.theta n ω j
    let mx := if h : B.Nonempty then B.sup' h (fun i => ω (i : ℕ)) else C.theta j
    let y := if B.card = 0 then 1 else
      min 1 ((B.card : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ)/(2*(C.t:ℝ))) *
        (C.c + C.theta j - mx))
    C.N j ≤ B.card ∧ (1/2 : ℝ) ≤ y ∧ y ≤ 1

lemma omega_iff_source (C : LocationConfig) (n : ℕ) (ω : ℕ → ℝ) :
    dpOmega C.c C.theta C.N n ω ↔ sourceOmega C n ω := by
  classical
  unfold dpOmega sourceOmega
  apply forall_congr'
  intro j
  dsimp only
  by_cases hne : (dpBlock C.c C.theta n ω j).Nonempty
  · have hcard : (dpBlock C.c C.theta n ω j).card ≠ 0 := Finset.card_ne_zero.mpr hne
    have hmax : dpMaxStat C.c C.theta n ω j =
        (dpBlock C.c C.theta n ω j).sup' hne (fun i => ω (i : ℕ)) := by
      simp only [dpMaxStat, dif_pos hne, Finset.max'_eq_sup', Finset.sup'_image]
      rfl
    simp only [dpY, hmax, dif_pos hne, if_neg hcard]
  · have hcard : (dpBlock C.c C.theta n ω j).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hbad : ¬ C.N j ≤ (dpBlock C.c C.theta n ω j).card := by
      have h := C.hN j
      omega
    simp only [hbad, false_and]

/-- Actual dpOmega under the actual infinite iid true-mixture law has probability
one asymptotically. No arbitrary event convergence is assumed. -/
theorem good_omega_probability (C : LocationConfig) (p : Fin C.t → ℝ)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) :
    Tendsto (fun n : ℕ => dpPinf C.g C.theta p
      {ω : ℕ → ℝ | dpOmega C.c C.theta C.N n ω}) atTop (𝓝 1) := by
  haveI : ∀ j : Fin C.t, IsProbabilityMeasure (dpRmeasure C.g C.theta j) := C.hRprob
  haveI : IsProbabilityMeasure (dpPlaw C.g C.theta p) := ⟨by
    simp only [dpPlaw, Measure.finset_sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hp j).le), hp1, ENNReal.ofReal_one]⟩
  have hgdens : ∫⁻ x, ENNReal.ofReal (C.g x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one C.hgnorm)
      (Eventually.of_forall C.hg0), C.hgnorm, ENNReal.ofReal_one]
  have hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ x ∈ Set.Icc (-C.c) C.c, m ≤ C.g x ∧ C.g x ≤ M := by
    refine ⟨C.m,C.M,C.hm,?_, fun x hx => ⟨C.hglo x hx,C.hgM x⟩⟩
    exact (C.hglo 0 ⟨by linarith [C.hc],C.hc.le⟩).trans (C.hgM 0)
  have hsource := statopia_math_node_1466837249_dca9d403 C.g C.q0 C.c C.t C.hc C.ht
    C.hg C.hg0 C.hgzero hgdens C.hq C.hq0 hT1 (dpPlaw C.g C.theta p) p hp hp1 C.theta C.hsep
    (dpRmeasure C.g C.theta) C.hRprob (fun _ => rfl) rfl C.N
  have hevent : ∀ n : ℕ, {ω : ℕ → ℝ | dpOmega C.c C.theta C.N n ω} =
      {ω : ℕ → ℝ | sourceOmega C n ω} := fun n => Set.ext (fun ω => omega_iff_source C n ω)
  simp_rw [hevent]
  exact hsource

end OfflineDPRootGoodOmega
end
end DPCompletedProof
