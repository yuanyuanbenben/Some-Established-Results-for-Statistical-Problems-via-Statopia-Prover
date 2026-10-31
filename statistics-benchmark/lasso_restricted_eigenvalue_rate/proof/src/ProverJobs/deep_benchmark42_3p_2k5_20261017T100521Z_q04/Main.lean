import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q04.Base

open MeasureTheory ProbabilityTheory
namespace Msc62GroundTruth

theorem lasso_restricted_eigenvalue_rate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset (Fin n))
    (x : Fin m → Fin n → ℝ)
    (X : Fin m → Fin n → ℝ)
    (hX : ∀ i j, X i j = x i j)
    (sigmaHat : Matrix (Fin n) (Fin n) ℝ)
    (hSigmaHat : ∀ j k,
      sigmaHat j k = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * X i k)
    (kappa Lambda B sigma lambda : ℝ)
    (hkappa : 0 < kappa) (hLambda : 0 < Lambda) (hB : 0 < B)
    (hsigma : 0 < sigma) (hlambda : 0 < lambda)
    (hRE : ∀ v : Fin n → ℝ,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |v j|) ≤
        3 * (∑ j ∈ S, |v j|) →
      kappa ^ 2 * (∑ j : Fin n, (v j) ^ 2) ≤
        ∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k)
    (hUpper : ∀ v : Fin n → ℝ,
      (∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k) ≤
        Lambda * ∑ j : Fin n, (v j) ^ 2)
    (hscale : (m : ℝ) * Lambda ≤ B ^ 2)
    (epsilon : Fin m → Omega → ℝ)
    (h_epsilon_meas : ∀ i, Measurable (epsilon i))
    (h_epsilon_integrable : ∀ i, Integrable (epsilon i) P)
    (h_epsilon_indep : iIndepFun (β := fun _ : Fin m => ℝ) epsilon P)
    (h_epsilon_centered : ∀ i, ∫ omega, epsilon i omega ∂P = 0)
    (h_epsilon_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_epsilon_subGaussian : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤
        Real.exp (sigma * t ^ 2 / 2))
    (betaStar : Fin n → ℝ)
    (h_support : ∀ j, j ∉ S → betaStar j = 0) :
    let score (omega : Omega) : Prop :=
      ∀ j : Fin n, |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2
    let response (omega : Omega) (i : Fin m) : ℝ :=
      (∑ j : Fin n, X i j * betaStar j) + epsilon i omega
    let objective (omega : Omega) (beta : Fin n → ℝ) : ℝ :=
      (1 / (2 * (m : ℝ))) *
          ∑ i : Fin m, (response omega i - ∑ j : Fin n, X i j * beta j) ^ 2 +
        lambda * ∑ j : Fin n, |beta j|
    let lassoSolution (omega : Omega) (beta : Fin n → ℝ) : Prop :=
      ∀ gamma : Fin n → ℝ, objective omega beta ≤ objective omega gamma
    let oracleBounds (betaHat : Fin n → ℝ) : Prop :=
        (1 / (m : ℝ)) * ∑ i : Fin m,
            (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 2 ∧
        (∑ j : Fin n, |betaHat j - betaStar j|) ≤
              8 * lambda * (S.card : ℝ) / kappa ^ 2 ∧
        ∑ j : Fin n, (betaHat j - betaStar j) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 4
    (P {omega | score omega}).toReal ≥
        1 - 2 * (n : ℝ) * Real.exp (-((m : ℝ) ^ 2 * (lambda / 2) ^ 2) /
          (2 * sigma * B ^ 2)) ∧
      ∀ omega, score omega → ∀ betaHat : Fin n → ℝ,
        lassoSolution omega betaHat → oracleBounds betaHat
:= by
  /- @proof-region region.root.250ebd472632 begin -/
  dsimp only
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  constructor
  · have hcol : ∀ j : Fin n, ∑ i : Fin m, (X i j) ^ 2 ≤ B ^ 2 := by
      intro j
      have hLam : sigmaHat j j ≤ Lambda := by
        have h := hUpper (fun k : Fin n => if k = j then (1 : ℝ) else 0)
        have h1 : (∑ k : Fin n, ∑ l : Fin n,
            (if k = j then (1 : ℝ) else 0) * sigmaHat k l * (if l = j then (1 : ℝ) else 0))
            = sigmaHat j j := by
          rw [Finset.sum_eq_single j (fun b _ hk => by simp [hk])
            (fun hj => by exact absurd (Finset.mem_univ j) hj)]
          rw [Finset.sum_eq_single j (fun l _ hl => by simp [hl])
            (fun hj => by exact absurd (Finset.mem_univ j) hj)]
          simp
        have h2 : (∑ k : Fin n, ((if k = j then (1 : ℝ) else 0)) ^ 2) = 1 := by
          rw [Finset.sum_eq_single j (fun b _ hk => by simp [hk])
            (fun hj => by exact absurd (Finset.mem_univ j) hj)]
          simp
        simp only [h1, h2, mul_one] at h
        exact h
      have hdiag : sigmaHat j j = (1 / (m : ℝ)) * ∑ i : Fin m, (X i j) ^ 2 := by
        rw [hSigmaHat j j]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hstep : (1 / (m : ℝ)) * (∑ i : Fin m, (X i j) ^ 2) ≤ Lambda := by
        rw [← hdiag]; exact hLam
      have hcancel : (m : ℝ) * ((1 / (m : ℝ)) * (∑ i : Fin m, (X i j) ^ 2))
          = ∑ i : Fin m, (X i j) ^ 2 := by
        rw [one_div, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmpos), one_mul]
      have hmul : (m : ℝ) * ((1 / (m : ℝ)) * (∑ i : Fin m, (X i j) ^ 2))
          ≤ (m : ℝ) * Lambda := mul_le_mul_of_nonneg_left hstep hmpos.le
      rw [hcancel] at hmul
      exact le_trans hmul hscale
    exact statopia_math_node_3915940999_868aa0ce P m n hm hn X epsilon h_epsilon_meas
      h_epsilon_indep sigma B lambda hsigma hB hlambda h_epsilon_exp_integrable
      h_epsilon_subGaussian hcol
  · intro omega hscore betaHat hmin
    have key : ∀ i : Fin m,
        (∑ j : Fin n, X i j * betaStar j) + epsilon i omega - ∑ j : Fin n, X i j * betaHat j
          = epsilon i omega + ∑ j : Fin n, X i j * (betaStar j - betaHat j) := by
      intro i
      have h1 : (∑ j : Fin n, X i j * (betaStar j - betaHat j))
          = (∑ j : Fin n, X i j * betaStar j) - ∑ j : Fin n, X i j * betaHat j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [h1]
      ring
    have hmin' : ∀ gamma : Fin n → ℝ,
        (1 / (2 * (m : ℝ))) * ∑ i : Fin m,
            (epsilon i omega + ∑ j : Fin n, X i j * (betaStar j - betaHat j)) ^ 2
          + lambda * ∑ j : Fin n, |betaHat j|
        ≤ (1 / (2 * (m : ℝ))) * ∑ i : Fin m,
            (epsilon i omega + ∑ j : Fin n, X i j * (betaStar j - gamma j)) ^ 2
          + lambda * ∑ j : Fin n, |gamma j| := by
      intro gamma
      have keyγ : ∀ i : Fin m,
          (∑ j : Fin n, X i j * betaStar j) + epsilon i omega - ∑ j : Fin n, X i j * gamma j
            = epsilon i omega + ∑ j : Fin n, X i j * (betaStar j - gamma j) := by
        intro i
        have h1 : (∑ j : Fin n, X i j * (betaStar j - gamma j))
            = (∑ j : Fin n, X i j * betaStar j) - ∑ j : Fin n, X i j * gamma j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h1]
        ring
      have hg := hmin gamma
      simp only [key, keyγ] at hg
      exact hg
    have hbasic := statopia_math_node_4187378725_a4837b16 m n hm X S betaStar h_support
      lambda hlambda (fun i => epsilon i omega) hscore betaHat hmin'
    have hcone := statopia_math_node_2772392877_7f100d52 m n hm X sigmaHat hSigmaHat S kappa
      hkappa hRE (fun j => betaHat j - betaStar j) hbasic.2
    have hQ : 0 ≤ (1 / (m : ℝ)) * ∑ i : Fin m,
        (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2 := by
      apply mul_nonneg
      · exact div_nonneg zero_le_one hmpos.le
      · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    exact statopia_math_node_1762459067_67761fda n S (fun j => betaHat j - betaStar j)
      kappa lambda ((1 / (m : ℝ)) * ∑ i : Fin m,
        (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2)
      hkappa hlambda hQ hbasic.1 hcone
  /- @proof-region region.root.250ebd472632 end -/

end Msc62GroundTruth
