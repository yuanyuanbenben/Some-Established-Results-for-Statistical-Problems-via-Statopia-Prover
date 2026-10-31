import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_1420316284_290236b8 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (y : Fin n → ℝ)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (thetaHat : Fin d → ℝ)
    (hmin : ∀ eta : Fin d → ℝ,
      (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ)) +
          lambda * (∑ j : Fin d, |thetaHat j|) ≤
        (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ)) +
          lambda * (∑ j : Fin d, |eta j|)),
    (∀ j : Fin d,
        |(1 / (n : ℝ)) * (X.transpose *ᵥ (y - X *ᵥ thetaHat)) j| ≤ lambda) ∧
      (⨆ j : Fin d, |(1 / (n : ℝ)) * (X.transpose *ᵥ (y - X *ᵥ thetaHat)) j| ≤ lambda) := by
  /- @proof-region region.target-node.session.76f2d32f8a00944b begin -/
  intro n d hn hd X y lambda hlambda thetaHat hmin
  have hcoord : ∀ j : Fin d,
      |(1 / (n : ℝ)) * (X.transpose *ᵥ (y - X *ᵥ thetaHat)) j| ≤ lambda := by
    intro j
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have htwon : (0 : ℝ) < 2 * (n : ℝ) := by linarith
    have htwonne : 2 * (n : ℝ) ≠ 0 := ne_of_gt htwon
    set B : ℝ := ∑ i : Fin n, X i j * (y i - (X *ᵥ thetaHat) i) with hB
    set C : ℝ := ∑ i : Fin n, (X i j) ^ 2 with hC
    have hmv_any : ∀ (u : ℝ) (i : Fin n),
        (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i
          = (X *ᵥ thetaHat) i + u * X i j := by
      intro u i
      have h1 : (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i
          = ∑ k : Fin d, X i k * (if k = j then thetaHat j + u else thetaHat k) := by
        simp [Matrix.mulVec, dotProduct]
      have h2 : (X *ᵥ thetaHat) i = ∑ k : Fin d, X i k * thetaHat k := by
        simp [Matrix.mulVec, dotProduct]
      have h3 : (∑ k : Fin d, X i k * (if k = j then thetaHat j + u else thetaHat k))
          = (∑ k : Fin d, X i k * thetaHat k) + u * X i j := by
        have hsplit : (∑ k : Fin d, X i k * (if k = j then thetaHat j + u else thetaHat k))
            - (∑ k : Fin d, X i k * thetaHat k) = u * X i j := by
          rw [← Finset.sum_sub_distrib]
          have heval : (∑ k : Fin d, (X i k * (if k = j then thetaHat j + u else thetaHat k)
                - X i k * thetaHat k))
              = X i j * (if j = j then thetaHat j + u else thetaHat j) - X i j * thetaHat j := by
            refine Finset.sum_eq_single j ?_ ?_
            · intro k _ hk
              rw [if_neg hk]
              ring
            · intro h
              exact absurd (Finset.mem_univ j) h
          rw [heval]
          change X i j * (if j = j then thetaHat j + u else thetaHat j) - X i j * thetaHat j
            = u * X i j
          rw [if_pos rfl]
          ring
        linarith
      rw [h1, h2, h3]
    have hpen_any : ∀ u : ℝ,
        (∑ k : Fin d, |(fun k : Fin d => if k = j then thetaHat j + u else thetaHat k) k|)
          - (∑ k : Fin d, |thetaHat k|) = |thetaHat j + u| - |thetaHat j| := by
      intro u
      rw [← Finset.sum_sub_distrib]
      have heval : (∑ k : Fin d, (|(fun k : Fin d => if k = j then thetaHat j + u else thetaHat k) k|
            - |thetaHat k|))
          = |(fun k : Fin d => if k = j then thetaHat j + u else thetaHat k) j| - |thetaHat j| := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro k _ hk
          change |(if k = j then thetaHat j + u else thetaHat k)| - |thetaHat k| = 0
          rw [if_neg hk]
          ring
        · intro h
          exact absurd (Finset.mem_univ j) h
      rw [heval]
      have hcongr : (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k) j
          = thetaHat j + u := by
        change (if j = j then thetaHat j + u else thetaHat j) = thetaHat j + u
        exact if_pos rfl
      rw [hcongr]
    have hquad_any : ∀ u : ℝ,
        (∑ i : Fin n, (y i - (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i) ^ 2)
          - (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) = -2 * u * B + u ^ 2 * C := by
      intro u
      have hterm : ∀ i : Fin n,
          (y i - (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i) ^ 2
            - (y i - (X *ᵥ thetaHat) i) ^ 2
          = (-2 * u) * (X i j * (y i - (X *ᵥ thetaHat) i)) + u ^ 2 * (X i j) ^ 2 := by
        intro i
        rw [hmv_any u i]
        ring
      calc (∑ i : Fin n, (y i - (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i) ^ 2)
            - (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2)
          = ∑ i : Fin n, ((y i - (X *ᵥ (fun k : Fin d => if k = j then thetaHat j + u else thetaHat k)) i) ^ 2
              - (y i - (X *ᵥ thetaHat) i) ^ 2) := by
            rw [Finset.sum_sub_distrib]
        _ = ∑ i : Fin n, ((-2 * u) * (X i j * (y i - (X *ᵥ thetaHat) i)) + u ^ 2 * (X i j) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
        _ = (-2 * u) * B + u ^ 2 * C := by
            rw [Finset.sum_add_distrib]
            congr 1
            · simp only [hB, Finset.mul_sum]
            · simp only [hC, Finset.mul_sum]
    have hcore : ∀ u : ℝ, u ≠ 0 →
        u * B ≤ |u| * ((n : ℝ) * lambda) + u ^ 2 * (C / 2) := by
      intro u _
      set eta : Fin d → ℝ := fun k : Fin d => if k = j then thetaHat j + u else thetaHat k with heta
      have hq : (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2)
          - (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) = -2 * u * B + u ^ 2 * C := by
        rw [heta]
        exact hquad_any u
      have hp : (∑ k : Fin d, |eta k|) - (∑ k : Fin d, |thetaHat k|)
          = |thetaHat j + u| - |thetaHat j| := by
        rw [heta]
        exact hpen_any u
      have hpabs : |thetaHat j + u| - |thetaHat j| ≤ |u| := by
        have h1 : |thetaHat j + u| ≤ |thetaHat j| + |u| := abs_add_le _ _
        linarith
      have hge := hmin eta
      have hD0 : (0 : ℝ) ≤ (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ))
            + lambda * (∑ k : Fin d, |eta k|)
          - ((∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ))
            + lambda * (∑ k : Fin d, |thetaHat k|)) := by
        linarith
      have hD1 : (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ))
            + lambda * (∑ k : Fin d, |eta k|)
          - ((∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ))
            + lambda * (∑ k : Fin d, |thetaHat k|))
          ≤ (-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ)) + lambda * |u| := by
        have e1 : (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ))
            - (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ))
            = (-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ)) := by
          rw [← sub_div, hq]
        have e2 : lambda * (∑ k : Fin d, |eta k|) - lambda * (∑ k : Fin d, |thetaHat k|)
            = lambda * (|thetaHat j + u| - |thetaHat j|) := by
          rw [← mul_sub, hp]
        have e3 : lambda * (|thetaHat j + u| - |thetaHat j|) ≤ lambda * |u| :=
          mul_le_mul_of_nonneg_left hpabs hlambda
        have hDform : (∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ))
              + lambda * (∑ k : Fin d, |eta k|)
            - ((∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ))
              + lambda * (∑ k : Fin d, |thetaHat k|))
            = ((∑ i : Fin n, (y i - (X *ᵥ eta) i) ^ 2) / (2 * (n : ℝ))
                - (∑ i : Fin n, (y i - (X *ᵥ thetaHat) i) ^ 2) / (2 * (n : ℝ)))
              + (lambda * (∑ k : Fin d, |eta k|) - lambda * (∑ k : Fin d, |thetaHat k|)) := by
          ring
        rw [hDform]
        linarith
      have hmain : (0 : ℝ) ≤ (-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ)) + lambda * |u| :=
        le_trans hD0 hD1
      have h4 : (0 : ℝ) ≤ (-2 * u * B + u ^ 2 * C) + 2 * (n : ℝ) * (lambda * |u|) := by
        have hmul : (0 : ℝ) ≤ 2 * (n : ℝ) * ((-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ)) + lambda * |u|) :=
          mul_nonneg (le_of_lt htwon) hmain
        have heq : 2 * (n : ℝ) * ((-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ)) + lambda * |u|)
            = (-2 * u * B + u ^ 2 * C) + 2 * (n : ℝ) * (lambda * |u|) := by
          rw [mul_add,
            mul_comm (2 * (n : ℝ)) ((-2 * u * B + u ^ 2 * C) / (2 * (n : ℝ))),
            div_mul_cancel₀ _ htwonne]
        rw [heq] at hmul
        exact hmul
      nlinarith [h4]
    have hplus : ∀ s : ℝ, 0 < s → B ≤ (n : ℝ) * lambda + s * (C / 2) := by
      intro s hs
      have hc := hcore s (ne_of_gt hs)
      rw [abs_of_pos hs] at hc
      have h2 : s * B ≤ s * ((n : ℝ) * lambda + s * (C / 2)) := by nlinarith [hc]
      exact le_of_mul_le_mul_left h2 hs
    have hminus : ∀ s : ℝ, 0 < s → -B ≤ (n : ℝ) * lambda + s * (C / 2) := by
      intro s hs
      have hc := hcore (-s) (by simpa using (ne_of_gt hs))
      rw [abs_neg, abs_of_pos hs] at hc
      have h2 : s * (-B) ≤ s * ((n : ℝ) * lambda + s * (C / 2)) := by nlinarith [hc]
      exact le_of_mul_le_mul_left h2 hs
    have hBle : B ≤ (n : ℝ) * lambda := by
      have hCnn : (0 : ℝ) ≤ C := by
        rw [hC]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (X i j))
      by_contra hcon
      push_neg at hcon
      have hdpos : (0 : ℝ) < B - (n : ℝ) * lambda := by linarith
      have hc1 : (0 : ℝ) < C / 2 + 1 := by linarith
      have hs : (0 : ℝ) < (B - (n : ℝ) * lambda) / (C / 2 + 1) := div_pos hdpos hc1
      have hb := hplus _ hs
      have h2 : ((B - (n : ℝ) * lambda) / (C / 2 + 1)) * (C / 2 + 1) = B - (n : ℝ) * lambda :=
        div_mul_cancel₀ _ (ne_of_gt hc1)
      nlinarith [hb, h2, hs]
    have hBge : -B ≤ (n : ℝ) * lambda := by
      have hCnn : (0 : ℝ) ≤ C := by
        rw [hC]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (X i j))
      by_contra hcon
      push_neg at hcon
      have hdpos : (0 : ℝ) < -B - (n : ℝ) * lambda := by linarith
      have hc1 : (0 : ℝ) < C / 2 + 1 := by linarith
      have hs : (0 : ℝ) < (-B - (n : ℝ) * lambda) / (C / 2 + 1) := div_pos hdpos hc1
      have hb := hminus _ hs
      have h2 : ((-B - (n : ℝ) * lambda) / (C / 2 + 1)) * (C / 2 + 1) = -B - (n : ℝ) * lambda :=
        div_mul_cancel₀ _ (ne_of_gt hc1)
      nlinarith [hb, h2, hs]
    have habs : |B| ≤ (n : ℝ) * lambda := abs_le.mpr ⟨by linarith, hBle⟩
    have hfin : |(1 / (n : ℝ)) * B| ≤ lambda := by
      have h1 : (1 / (n : ℝ)) * B = B / (n : ℝ) := by ring
      rw [h1, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
      calc |B| ≤ (n : ℝ) * lambda := habs
        _ = lambda * (n : ℝ) := by ring
    have hentryB : (X.transpose *ᵥ (y - X *ᵥ thetaHat)) j = B := by
      rw [hB]
      simp [Matrix.mulVec, dotProduct, Matrix.transpose]
    rw [hentryB]
    exact hfin
  exact ⟨hcoord, Real.iSup_le hcoord hlambda⟩
  /- @proof-region region.target-node.session.76f2d32f8a00944b end -/
