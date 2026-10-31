import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Vocabulary
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.Base
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.ProvedNodes.Node_537990944_6d0e223c_77c58c9a
import ProverJobs.job_paper_c93669ef201447419b92d6591d8bc1aa.ProvedNodes.Node_834363190_4b893991_cf348327


open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_2396382263_35e06d48 : ∀ (t : ℕ) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 < c)
    (θstar : Fin t → ℝ)
    (g q0 : ℝ → ℝ)
    (Rg : ℝ) (hRg : 0 ≤ Rg)
    (L : ℝ) (hL : 0 < L)
    (δ : Fin t → ℝ)
    {Ω : Type} (X : ℕ → Ω → ℝ)
    (n : ℕ) (hn : 1 ≤ n) (j : Fin t) (ω : Ω)
    (hnj : 1 ≤ windowCount X θstar c n j ω)
    (hdelta : 1 / ((windowCount X θstar c n j ω : ℕ) : ℝ) ≤ δ j)
    (hUj : upperOrderStat X θstar c n j ω ≤ θstar j + c)
    (hint : ∀ i ∈ windowIdx X θstar c n j ω, X i ω - θstar j ∈ Set.Icc (-c) c)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_lb : ∀ θ : ℝ, |θ - θstar j| ≤ δ j → L ≤ q0 θ)
    (hP : ∀ θ ∈ Set.Ioo (θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
            (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))) (θstar j) ∪ {θstar j},
        Real.exp (-Rg) ≤ ∏ i ∈ windowIdx X θstar c n j ω,
          g (X i ω - θ) / g (X i ω - θstar j)),
    ∫⁻ θ : ℝ, ENNReal.ofReal ((∏ i ∈ windowIdx X θstar c n j ω,
        g (X i ω - θ) / g (X i ω - θstar j)) * q0 θ) ∂volume
      ≥ ENNReal.ofReal (Real.exp (-Rg) * L *
          min (c + θstar j - upperOrderStat X θstar c n j ω)
            (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))) := by
  /- @proof-region region.target-node.session.9efe78301b13d1af begin -/
  intro t ht c hc θstar g q0 Rg hRg L hL δ Ω X n hn j ω hnj hdelta hUj hint hg_nonneg hg_pos hq0_nonneg hq0_lb hP
  set S : Set ℝ := Set.Ioo (θstar j - min (c + θstar j - upperOrderStat X θstar c n j ω)
      (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ))) (θstar j) ∪ {θstar j} with hS_def
  set s : ℝ := min (c + θstar j - upperOrderStat X θstar c n j ω)
      (1 / ((windowCount X θstar c n j ω : ℕ) : ℝ)) with hs_def
  have hnjR : (1 : ℝ) ≤ ((windowCount X θstar c n j ω : ℕ) : ℝ) := by exact_mod_cast hnj
  have hinv_pos : (0 : ℝ) < 1 / ((windowCount X θstar c n j ω : ℕ) : ℝ) :=
    div_pos one_pos (lt_of_lt_of_le one_pos hnjR)
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    exact le_min (by linarith) hinv_pos.le
  have hs_le_delta : s ≤ δ j := by
    rw [hs_def]
    exact le_trans (min_le_right _ _) hdelta
  have hdelta_nonneg : 0 ≤ δ j := le_trans hs_nonneg hs_le_delta
  have hprod_nonneg : ∀ θ : ℝ, 0 ≤ ∏ i ∈ windowIdx X θstar c n j ω,
      g (X i ω - θ) / g (X i ω - θstar j) := by
    intro θ
    exact Finset.prod_nonneg (fun i hi =>
      div_nonneg (hg_nonneg (X i ω - θ)) (le_of_lt (hg_pos (X i ω - θstar j) (hint i hi))))
  have habs : ∀ θ ∈ S, |θ - θstar j| ≤ δ j := by
    intro θ hθ
    rw [hS_def] at hθ
    rcases hθ with hθ | hθ
    · rw [Set.mem_Ioo] at hθ
      obtain ⟨h1, h2⟩ := hθ
      have hle : |θ - θstar j| ≤ s := by
        have h3 : θstar j - θ < s := by linarith
        have h4 : |θ - θstar j| = θstar j - θ := by
          rw [abs_of_neg (by linarith : θ - θstar j < 0)]
          ring
        rw [h4]
        linarith
      exact le_trans hle hs_le_delta
    · rw [Set.mem_singleton_iff] at hθ
      rw [hθ, sub_self, abs_zero]
      exact hdelta_nonneg
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-Rg) := (Real.exp_pos (-Rg)).le
  have hcst_nonneg : (0 : ℝ) ≤ Real.exp (-Rg) * L := mul_nonneg hexp_nonneg hL.le
  have hpoint : ∀ θ : ℝ, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-Rg) * L)) θ
      ≤ ENNReal.ofReal ((∏ i ∈ windowIdx X θstar c n j ω,
          g (X i ω - θ) / g (X i ω - θstar j)) * q0 θ) := by
    intro θ
    by_cases hθ : θ ∈ S
    · rw [Set.indicator_of_mem hθ]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul (hP θ hθ) (hq0_lb θ (habs θ hθ)) hL.le (hprod_nonneg θ))
    · rw [Set.indicator_of_notMem hθ]
      exact zero_le _
  have hS_meas : MeasurableSet S := by
    rw [hS_def]
    measurability
  have hmodel : ∫⁻ θ : ℝ, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-Rg) * L)) θ ∂volume
      = ENNReal.ofReal (Real.exp (-Rg) * L) * volume S := by
    rw [MeasureTheory.lintegral_indicator hS_meas]
    exact MeasureTheory.setLIntegral_const S (ENNReal.ofReal (Real.exp (-Rg) * L))
  have hvol_Ioo : volume (Set.Ioo (θstar j - s) (θstar j)) = ENNReal.ofReal s := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hvol_S : volume S = ENNReal.ofReal s := by
    rw [hS_def]
    refine le_antisymm ?_ ?_
    · calc volume (Set.Ioo (θstar j - s) (θstar j) ∪ {θstar j})
          ≤ volume (Set.Ioo (θstar j - s) (θstar j)) + volume ({θstar j} : Set ℝ) :=
            measure_union_le _ _
        _ = ENNReal.ofReal s := by rw [hvol_Ioo, Real.volume_singleton, add_zero]
    · calc ENNReal.ofReal s = volume (Set.Ioo (θstar j - s) (θstar j)) := hvol_Ioo.symm
        _ ≤ volume (Set.Ioo (θstar j - s) (θstar j) ∪ {θstar j}) :=
            measure_mono (Set.subset_union_left)
  have hmono : ∫⁻ θ : ℝ, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-Rg) * L)) θ ∂volume
      ≤ ∫⁻ θ : ℝ, ENNReal.ofReal ((∏ i ∈ windowIdx X θstar c n j ω,
          g (X i ω - θ) / g (X i ω - θstar j)) * q0 θ) ∂volume :=
    MeasureTheory.lintegral_mono hpoint
  have h1 : ENNReal.ofReal (Real.exp (-Rg) * L * s)
      = ENNReal.ofReal (Real.exp (-Rg) * L) * ENNReal.ofReal s :=
    ENNReal.ofReal_mul hcst_nonneg
  have h2 : ENNReal.ofReal (Real.exp (-Rg) * L) * ENNReal.ofReal s
      = ENNReal.ofReal (Real.exp (-Rg) * L) * volume S := by rw [hvol_S]
  have h3 : ENNReal.ofReal (Real.exp (-Rg) * L) * volume S
      = ∫⁻ θ : ℝ, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-Rg) * L)) θ ∂volume :=
    hmodel.symm
  exact h1.trans_le (h2.trans_le (h3.trans_le hmono))
  /- @proof-region region.target-node.session.9efe78301b13d1af end -/

end Statlib.Imported
