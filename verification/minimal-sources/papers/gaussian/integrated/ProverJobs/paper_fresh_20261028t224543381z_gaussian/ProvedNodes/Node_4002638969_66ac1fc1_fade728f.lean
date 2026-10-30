import Statlib.StatFoundation.RandomVariable.Gaussian.Slepian
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_gaussian.Base

namespace PaperProofTasks.paper_fresh_20261028t224543381z_gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open _root_.PaperProofTasks.paper_fresh_20261028t224543381z_gaussian.Statlib.Imported

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_4002638969_66ac1fc1 : ∀ (m : ℕ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosSemidef)
    (nu : Measure (Fin m → ℝ))
    (hprob : MeasureTheory.IsProbabilityMeasure nu)
    (hgauss : ProbabilityTheory.IsGaussian nu)
    (hint1 : ∀ j : Fin m, MeasureTheory.Integrable (fun s : Fin m → ℝ => s j) nu)
    (hmean : ∀ j : Fin m, (∫ s : Fin m → ℝ, s j ∂nu) = 0)
    (hint2 : ∀ k l : Fin m,
      MeasureTheory.Integrable (fun s : Fin m → ℝ => s k * s l) nu)
    (hcov : ∀ k l : Fin m, (∫ s : Fin m → ℝ, s k * s l ∂nu) = Sigma k l),
    Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector
      nu (fun s : Fin m → ℝ => s) Sigma := by
  /- @proof-region region.target-node.session.db77c9e50fa2cd7d begin -/
  intro m Sigma hSigma nu hprob hgauss hint1 hmean hint2 hcov
  refine ⟨measurable_id, ?_, ?_⟩
  · intro u
    obtain ⟨C, hCpos, hCint⟩ :=
      ProbabilityTheory.IsGaussian.exists_integrable_exp_sq nu
    have hcont : Continuous (fun ω : Fin m → ℝ => ∑ j, u j * ω j) := by
      fun_prop
    have hmeas : AEStronglyMeasurable (fun ω : Fin m → ℝ => Real.exp (∑ j, u j * ω j)) nu :=
      (Real.continuous_exp.comp hcont).aestronglyMeasurable
    set A : ℝ := ∑ j, |u j| with hAdef
    have hbound : ∀ ω : Fin m → ℝ, ∑ j, u j * ω j ≤ A * ‖ω‖ := by
      intro ω
      have h1 : ∑ j, u j * ω j ≤ ∑ j, |u j| * ‖ω‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        calc u j * ω j ≤ |u j * ω j| := le_abs_self _
          _ = |u j| * |ω j| := by rw [abs_mul]
          _ ≤ |u j| * ‖ω‖ := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              simpa using norm_le_pi_norm ω j
      calc ∑ j, u j * ω j ≤ ∑ j, |u j| * ‖ω‖ := h1
        _ = A * ‖ω‖ := by rw [hAdef, Finset.sum_mul]
    refine Integrable.mono' (hCint.const_mul (Real.exp (A ^ 2 / (4 * C)))) hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (∑ j, u j * ω j) ≤ Real.exp (A * ‖ω‖) := Real.exp_le_exp.mpr (hbound ω)
      _ ≤ Real.exp (A ^ 2 / (4 * C) + C * ‖ω‖ ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have hp : (0:ℝ) < 4 * C := by linarith
          rw [← sub_le_iff_le_add, le_div_iff₀ hp]
          nlinarith [sq_nonneg (2 * C * ‖ω‖ - A)]
      _ = Real.exp (A ^ 2 / (4 * C)) * Real.exp (C * ‖ω‖ ^ 2) := Real.exp_add _ _
  · intro u
    let Lm : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun ω => ∑ j, u j * ω j
        map_add' := by
          intro a b
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring) }
    let L : (Fin m → ℝ) →L[ℝ] ℝ := Lm.toContinuousLinearMap
    have hL_apply : ∀ ω : Fin m → ℝ, L ω = ∑ j, u j * ω j := fun ω => rfl
    have hmeanL : ∫ x : Fin m → ℝ, L x ∂nu = 0 := by
      have h1 : ∫ x : Fin m → ℝ, L x ∂nu = ∑ j, u j * ∫ x : Fin m → ℝ, x j ∂nu := by
        rw [show (fun x : Fin m → ℝ => L x) = fun x => ∑ j, u j * x j from funext hL_apply]
        rw [integral_finset_sum Finset.univ (fun j _ => (hint1 j).const_mul (u j))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_const_mul]
      rw [h1]
      simp [hmean]
    have hsq : ∀ x : Fin m → ℝ, L x * L x = ∑ i, ∑ j, (u i * u j) * (x i * x j) := by
      intro x
      rw [hL_apply, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    have hint_ij : ∀ i j : Fin m,
        Integrable (fun x : Fin m → ℝ => (u i * u j) * (x i * x j)) nu :=
      fun i j => (hint2 i j).const_mul _
    have hinner : ∀ i : Fin m,
        Integrable (fun x : Fin m → ℝ => ∑ j, (u i * u j) * (x i * x j)) nu :=
      fun i => integrable_finset_sum Finset.univ (fun j _ => hint_ij i j)
    have hsecond : ∫ x : Fin m → ℝ, L x * L x ∂nu = ∑ i, ∑ j, (u i * u j) * Sigma i j := by
      rw [show (fun x : Fin m → ℝ => L x * L x)
        = fun x => ∑ i, ∑ j, (u i * u j) * (x i * x j) from funext hsq]
      rw [integral_finset_sum Finset.univ (fun i _ => hinner i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum Finset.univ (fun j _ => hint_ij i j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, hcov]
    have hsum_eq : (∑ i, ∑ j, (u i * u j) * Sigma i j) = ∑ i, ∑ j, u i * Sigma i j * u j := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    have hvv_nonneg : 0 ≤ ∑ i, ∑ j, u i * Sigma i j * u j := by
      rw [← hsum_eq, ← hsecond]
      exact integral_nonneg (fun x => mul_self_nonneg (L x))
    have hcovL' : ∀ t : ℝ, ((covarianceBilinDual nu) (t • L)) (t • L)
        = t ^ 2 * ∑ i, ∑ j, (u i * u j) * Sigma i j := by
      intro t
      rw [covarianceBilinDual_apply (IsGaussian.memLp_id nu 2 (by norm_num)) (t • L) (t • L)]
      have hzero : ∫ x : Fin m → ℝ, (t • L) x ∂nu = 0 := by
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [integral_const_mul, hmeanL, mul_zero]
      simp only [hzero, sub_zero]
      rw [show (fun x : Fin m → ℝ => (t • L) x * (t • L) x) = fun x => t ^ 2 * (L x * L x) from
        funext (fun x => by simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)]
      rw [integral_const_mul, hsecond]
    have hLmean : L (∫ x : Fin m → ℝ, x ∂nu) = 0 := by
      rw [← ContinuousLinearMap.integral_comp_comm L (φ := fun x : Fin m → ℝ => x)
        hgauss.integrable_fun_id]
      exact hmeanL
    have hmap : Measure.map (fun ω : Fin m → ℝ => L ω) nu
        = gaussianReal 0 ⟨∑ i, ∑ j, u i * Sigma i j * u j, hvv_nonneg⟩ := by
      have hLHS : ∀ t : ℝ,
          ∫ x : Fin m → ℝ, Complex.exp (↑t * ↑(L x) * Complex.I) ∂nu
            = Complex.exp (-(↑(t ^ 2 * ∑ i, ∑ j, u i * Sigma i j * u j)) / 2) := by
        intro t
        have h1 : charFunDual nu (t • L)
            = ∫ x : Fin m → ℝ, Complex.exp (↑t * ↑(L x) * Complex.I) ∂nu := by
          simp only [charFunDual, BoundedContinuousFunction.probCharDual_apply,
            ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        rw [← h1, IsGaussian.charFunDual_eq' (μ := nu) (t • L), hcovL' t]
        have hLmean' : L (∫ x : Fin m → ℝ, id x ∂nu) = 0 := by simpa using hLmean
        have hzero : (t • L) (∫ x : Fin m → ℝ, id x ∂nu) = 0 := by
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hLmean', mul_zero]
        simp only [hzero, hsum_eq, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
      have hchar : charFun (Measure.map (fun ω : Fin m → ℝ => L ω) nu)
          = charFun (gaussianReal 0 ⟨∑ i, ∑ j, u i * Sigma i j * u j, hvv_nonneg⟩) := by
        funext t
        rw [MeasureTheory.charFun_apply_real, ProbabilityTheory.charFun_gaussianReal]
        rw [integral_map L.continuous.aemeasurable
          (f := fun y : ℝ => Complex.exp (↑t * ↑y * Complex.I))
          ((by fun_prop : Continuous fun y : ℝ => Complex.exp (↑t * ↑y * Complex.I)).aestronglyMeasurable)]
        rw [hLHS t]
        congr 1
        push_cast
        ring
      exact MeasureTheory.Measure.ext_of_charFun hchar
    have hfinal : ∫ ω : Fin m → ℝ, Real.exp (L ω) ∂nu
        = Real.exp ((∑ i, ∑ j, u i * Sigma i j * u j) / 2) := by
      have hAEM : AEMeasurable (fun ω : Fin m → ℝ => L ω) nu := L.continuous.aemeasurable
      have hAE : AEStronglyMeasurable (fun y : ℝ => Real.exp y)
          (Measure.map (fun ω : Fin m → ℝ => L ω) nu) := Real.continuous_exp.aestronglyMeasurable
      have h1 : ∫ y : ℝ, Real.exp y ∂(Measure.map (fun ω : Fin m → ℝ => L ω) nu)
          = ∫ ω : Fin m → ℝ, Real.exp (L ω) ∂nu := integral_map hAEM hAE
      have h2 : ∫ y : ℝ, Real.exp y
            ∂(gaussianReal 0 ⟨∑ i, ∑ j, u i * Sigma i j * u j, hvv_nonneg⟩)
          = Real.exp ((∑ i, ∑ j, u i * Sigma i j * u j) / 2) := by
        have h3 := Statlib.StatFoundation.Statistics.Asymptotic.gaussianReal_integral_exp 1
          (∑ i, ∑ j, u i * Sigma i j * u j) hvv_nonneg
        have h4 : (1 : ℝ) ^ 2 * (∑ i, ∑ j, u i * Sigma i j * u j) / 2
            = (∑ i, ∑ j, u i * Sigma i j * u j) / 2 := by norm_num
        rw [h4] at h3
        simpa using h3
      rw [← h1, hmap, h2]
    rw [show (∫ ω : Fin m → ℝ, Real.exp (∑ j, u j * ω j) ∂nu)
        = ∫ ω : Fin m → ℝ, Real.exp (L ω) ∂nu from by simp only [← hL_apply]]
    exact hfinal
  /- @proof-region region.target-node.session.db77c9e50fa2cd7d end -/

end Statlib.Imported
end

