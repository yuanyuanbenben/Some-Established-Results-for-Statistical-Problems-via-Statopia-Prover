import ProverJobs.manual_dp_cons_finish_20261031.PosteriorRatio
import ProverJobs.manual_dp_root_finish_20261031.PartitionPrior
import ProverJobs.manual_dp_root_finish_20261031.ConsMeasurability
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace OfflineDPActualNormalization
open Statlib.Imported ManualDPCons

lemma finite_normalized_control (P : ℕ → ℝ) (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (hP : ∀ k, 0 ≤ P k) (hPt : 0 < P t) (hsum : ∑ k ∈ Finset.Icc 1 n, P k = 1) :
    |P t-1| ≤ (∑ k ∈ Finset.Icc 1 (t-1), P k) +
      ∑ s ∈ Finset.Icc 1 (n-t), P (t+s) / P t := by
  have hsplit : (∑ k ∈ Finset.Icc 1 t, P k) + (∑ k ∈ Finset.Icc (t+1) n, P k) =
      ∑ k ∈ Finset.Icc 1 n, P k := by
    simpa only [Finset.Ico_add_one_right_eq_Icc] using
      (Finset.sum_Ico_consecutive P (show 1 ≤ t+1 by omega) (show t+1 ≤ n+1 by omega))
  have hlow : (∑ k ∈ Finset.Icc 1 t, P k) = (∑ k ∈ Finset.Icc 1 (t-1), P k) + P t := by
    have h := Finset.sum_Icc_succ_top (a := 1) (b := t-1) (show 1 ≤ (t-1)+1 by omega) P
    simpa only [Nat.sub_add_cancel ht] using h
  have hhigh : (∑ s ∈ Finset.Icc 1 (n-t), P (t+s)) = ∑ k ∈ Finset.Icc (t+1) n, P k := by
    refine Finset.sum_bij (fun s _ => t+s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    · intro a ha b hb heq
      dsimp only at heq
      omega
    · intro k hk
      refine ⟨k-t, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        omega
      · change t + (k-t) = k
        have := (Finset.mem_Icc.mp hk).1
        omega
    · intro s hs
      rfl
  rw [hlow, ← hhigh, hsum] at hsplit
  have hl0 : 0 ≤ ∑ k ∈ Finset.Icc 1 (t-1), P k := Finset.sum_nonneg (fun k _ => hP k)
  have hh0 : 0 ≤ ∑ s ∈ Finset.Icc 1 (n-t), P (t+s) := Finset.sum_nonneg (fun s _ => hP _)
  have hPt1 : P t ≤ 1 := by linarith
  have hquot : (∑ s ∈ Finset.Icc 1 (n-t), P (t+s)) ≤
      ∑ s ∈ Finset.Icc 1 (n-t), P (t+s)/P t := by
    apply Finset.sum_le_sum
    intro s hs
    apply (le_div_iff₀ hPt).mpr
    exact mul_le_of_le_one_right (hP _) hPt1
  rw [abs_of_nonpos (by linarith : P t-1 ≤ 0)]
  linarith

lemma dpNpost_nonneg (C : LocationConfig) (prior : ConcentrationPrior)
    (n k : ℕ) (x : Fin n → ℝ) : 0 ≤ dpNpost C.g C.q0 prior.dens n k x := by
  classical
  unfold dpNpost
  apply integral_nonneg
  intro a
  change 0 ≤ (∑ A ∈ dpTau n k, dpPartPrior a n A * ∏ B ∈ A, dpMargLik C.g C.q0 x B) * prior.dens a
  by_cases ha : 0 < a
  · apply mul_nonneg _ (prior.nonneg a ha)
    apply Finset.sum_nonneg
    intro A hA
    apply mul_nonneg
    · unfold dpPartPrior dpRisingFactorial
      positivity
    · exact Finset.prod_nonneg (fun B _ => ManualDPCons.marginal_nonneg C.g C.q0 C.hg0 C.hq0 x B)
  · rw [prior.zero a (not_lt.mp ha), mul_zero]

/-- Actual dpPostProb normalization follows from source prior/kernel positivity and Omega.
There is no normalization or posterior-probability hypothesis in this statement. -/
theorem actual_posterior_control (C : LocationConfig) (prior : ConcentrationPrior)
    (n : ℕ) (hn : 3 ≤ n) (htn : C.t+1 ≤ n) (omega : ℕ → ℝ)
    (hOmega : dpOmega C.c C.theta C.N n omega)
    (hcover : ∀ i : Fin n, ∃ j, omega (i:ℕ) ∈ Set.Icc (C.theta j-C.c) (C.theta j+C.c))
    (hinterior : ∀ j i, i ∈ dpBlock C.c C.theta n omega j → -C.c < omega (i:ℕ)-C.theta j) :
    |dpPostProb C.g C.q0 prior.dens n C.t omega - 1| ≤
      (∑ k ∈ Finset.Icc 1 (C.t-1), dpPostProb C.g C.q0 prior.dens n k omega) +
      ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s omega := by
  classical
  let x := dpXseq n omega
  have hDpos := (omega_denominator_log_inverse C.c C.R C.L C.r
    ((Real.log (n:ℝ))^((1:ℝ)/(2*(C.t:ℝ)))) C.theta C.N omega C.g C.q0
    C.hg C.hg0 C.hgpos C.hgdiff C.hgderiv ⟨C.M,C.hM,C.hgM⟩ C.hq C.hq0 C.hqint C.hR C.hL C.hr
    (logroot_one_le C.t n hn) C.hT4 C.hN hOmega rfl hinterior C.hsep hcover C.ht
    (by exact_mod_cast (show 1<n by omega))).1
  have hspec := source_concentration_spec C prior n 1 (by omega) (by omega) htn C.t C.ht (by omega)
  have hCF : OfflineDPPartitionPrior.concentrationFactor prior.dens n C.t =
      concentrationIntegral prior.dens n C.t := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall (fun a ha => by rw [prior.zero a (not_lt.mp ha), mul_zero])
  have hNpos : 0 < dpNpost C.g C.q0 prior.dens n C.t x := by
    rw [OfflineDPPartitionPrior.dpNpost_factor, hCF]
    exact mul_pos hspec.2 hDpos
  have hZpos : 0 < dpZpost C.g C.q0 prior.dens n x := by
    apply hNpos.trans_le
    unfold dpZpost
    exact Finset.single_le_sum (fun k _ => dpNpost_nonneg C prior n k x)
      (Finset.mem_Icc.mpr ⟨C.ht,by omega⟩)
  have hZne : dpZpost C.g C.q0 prior.dens n x ≠ 0 := hZpos.ne'
  have hZne0 : dpZpost C.g C.q0 prior.dens n (dpXseq n omega) ≠ 0 := hZne
  let P := fun k => dpPostProb C.g C.q0 prior.dens n k omega
  have hP : ∀ k, 0 ≤ P k := by
    intro k
    dsimp only [P, dpPostProb, dpPostK]
    rw [if_neg hZne]
    exact div_nonneg (dpNpost_nonneg C prior n k x) hZpos.le
  have hPt : 0 < P C.t := by
    dsimp only [P, dpPostProb, dpPostK]
    rw [if_neg hZne]
    exact div_pos hNpos hZpos
  have hsum : ∑ k ∈ Finset.Icc 1 n, P k = 1 := by
    simp only [P, dpPostProb, dpPostK, if_neg hZne0]
    rw [← Finset.sum_div]
    exact div_self hZne
  have h := finite_normalized_control P n C.t C.ht (by omega) hP hPt hsum
  convert h using 1
  apply congrArg (fun y => (∑ k ∈ Finset.Icc 1 (C.t-1), P k) + y)
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only [dpRatio]
  rw [if_neg hPt.ne']

/-- Under the actual infinite mixture law the support/interior side conditions
hold almost surely, so Omega alone controls the posterior discrepancy. -/
theorem actual_posterior_control_ae (C : LocationConfig) (prior : ConcentrationPrior)
    (p : Fin C.t → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (n : ℕ) (hn : 3 ≤ n) (htn : C.t+1 ≤ n) :
    ∀ᵐ omega ∂dpPinf C.g C.theta p,
      dpOmega C.c C.theta C.N n omega →
      |dpPostProb C.g C.q0 prior.dens n C.t omega - 1| ≤
        (∑ k ∈ Finset.Icc 1 (C.t-1), dpPostProb C.g C.q0 prior.dens n k omega) +
        ∑ s ∈ Finset.Icc 1 (n-C.t), dpRatio C.g C.q0 prior.dens C.t n s omega := by
  haveI := trueLaw_probability C p hp hp1
  have hmp : MeasurePreserving (dpXseq n) (dpPinf C.g C.theta p)
      (Measure.pi (fun _ : Fin n => dpPlaw C.g C.theta p)) :=
    ⟨by unfold dpXseq; fun_prop, OfflineDPConsMeas.prefix_law _ n⟩
  have hgood := hmp.quasiMeasurePreserving.ae (trueLaw_ae_goodPrefix C p hp hp1 n)
  filter_upwards [hgood] with omega hgood hOmega
  apply actual_posterior_control C prior n hn htn omega hOmega
  · simpa only [dpXseq] using hgood.1
  · simpa only [dpBlock, dpXseq, prefixPath_apply] using hgood.2

#print axioms actual_posterior_control_ae
#print axioms actual_posterior_control
end OfflineDPActualNormalization
