import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Base

open MeasureTheory ProbabilityTheory
open Filter

open MeasureTheory ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_2199421144_3cbe5eb0 : ∀ {𝓧 : Type*} [Fintype 𝓧]
    (F : 𝓧 → ℝ) (mu : 𝓧) (delta : ℝ)
    (hdelta_pos : 0 < delta)
    (hgap : ∀ z : 𝓧, z ≠ mu → delta ≤ F z - F mu)
    (A : ℕ → 𝓧 → ℝ) (mHat : ℕ → 𝓧)
    (hconv : ∀ z : 𝓧, Tendsto (fun n : ℕ => A n z / (n : ℝ)) atTop (nhds (F z)))
    (hmin : ∀ n : ℕ, 1 ≤ n → ∀ z : 𝓧, A n (mHat n) ≤ A n z),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → mHat n = mu := by
  /- @proof-region region.target-node.session.ed842dfa6aa4c8a6 begin -/
  intro 𝓧 _ F mu delta hdelta_pos hgap A mHat hconv hmin
  have hε : 0 < delta / 2 := by linarith
  have hev : ∀ z : 𝓧, ∀ᶠ n : ℕ in atTop, |A n z / (n : ℝ) - F z| < delta / 2 := by
    intro z
    have hmem : Metric.ball (F z) (delta / 2) ∈ nhds (F z) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    have h := (hconv z).eventually hmem
    filter_upwards [h] with n hn
    simpa [Real.dist_eq] using hn
  have hall : ∀ᶠ n : ℕ in atTop, ∀ z : 𝓧, |A n z / (n : ℝ) - F z| < delta / 2 :=
    Filter.eventually_all.mpr hev
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hstrict : ∀ z : 𝓧, z ≠ mu → A n mu < A n z := by
    intro z hzmu
    have hbmu := hN0 n hn0 mu
    have hbz := hN0 n hn0 z
    have hzgt : F z - delta / 2 < A n z / (n : ℝ) := by
      have h := (abs_lt.mp hbz).1
      linarith
    have hmult : A n mu / (n : ℝ) < F mu + delta / 2 := by
      have h := (abs_lt.mp hbmu).2
      linarith
    have hgapz : F mu + delta ≤ F z := by
      have h := hgap z hzmu
      linarith
    have hfrac : A n mu / (n : ℝ) < A n z / (n : ℝ) := by linarith
    have hmul2 := mul_lt_mul_of_pos_right hfrac hnpos
    have h1 : A n mu / (n : ℝ) * (n : ℝ) = A n mu := div_mul_cancel₀ _ hnne
    have h2 : A n z / (n : ℝ) * (n : ℝ) = A n z := div_mul_cancel₀ _ hnne
    rw [h1, h2] at hmul2
    exact hmul2
  by_contra hne
  have hlt := hstrict (mHat n) hne
  have hminn := hmin n hn1 mu
  linarith
  /- @proof-region region.target-node.session.ed842dfa6aa4c8a6 end -/
