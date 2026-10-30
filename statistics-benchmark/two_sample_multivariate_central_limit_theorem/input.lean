-- BLOCKER: the source theorem uses R^d and N_d(0, Sigma) without binding d; this file explicitly binds d >= 1.
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem two_sample_multivariate_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : Ω → EuclideanSpace ℝ (Fin d))
    (cov : Matrix (Fin d) (Fin d) ℝ)
    (m n : ℕ → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hXY_indep :
      IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY_ident : IdentDistrib (X 0) (Y 0) P P)
    (hX_second : Integrable (fun ω ↦ ‖X 0 ω‖ ^ 2) P)
    (hX_cov : ∀ j k,
      ∫ ω,
          (X 0 ω j - (∫ ω, X 0 ω ∂P) j) *
            (X 0 ω k - (∫ ω, X 0 ω ∂P) k) ∂P =
        cov j k)
    (hG_meas : Measurable G)
    (hG_gaussian : IsGaussian (P.map G))
    (hG_mean : ∫ ω, G ω ∂P = 0)
    (hG_cov : ∀ j k, ∫ ω, G ω j * G ω k ∂P = cov j k)
    (hm_pos : ∀ r, 0 < m r)
    (hn_pos : ∀ r, 0 < n r)
    (hm_lim : Tendsto m atTop atTop)
    (hn_lim : Tendsto n atTop atTop) :
    TendstoInDistribution
      (fun r ω ↦
        Real.sqrt
            (((m r : ℝ) * (n r : ℝ)) /
              ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (m r), X i ω -
            ((n r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (n r), Y i ω))
      atTop G P := by
  sorry
