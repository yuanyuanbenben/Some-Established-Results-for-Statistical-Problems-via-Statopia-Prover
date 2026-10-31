import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Vocabulary
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4139154565_e514172c : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (θstar : Fin t → ℝ) (M : ℝ) (hM : 0 < M)
    (piDens : ℝ → ℝ)
    (n s : ℕ) (hn : t ≤ n) (hs : 1 ≤ s) (hts : t + s ≤ n)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_pos : ∀ x ∈ Set.Icc (-c) c, 0 < g x)
    (hg_le : ∀ x ∈ Set.Icc (-c) c, g x ≤ M)
    (hg_int : ∫ x : ℝ, g x ∂volume = 1)
    (hg_integrable : Integrable g volume)
    (hq0_meas : Measurable q0)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_int : ∫ θ : ℝ, q0 θ ∂volume = 1)
    (hq0_integrable : Integrable q0 volume)
    (hpi_meas : Measurable piDens)
    (hpi_nonneg : ∀ α : ℝ, 0 < α → 0 ≤ piDens α)
    (hpi_zero : ∀ α : ℝ, α ≤ 0 → piDens α = 0)
    (hpi_int : ∫ α : ℝ, piDens α ∂(volume.restrict (Set.Ioi (0 : ℝ))) = 1)
    (hpi_integrable : Integrable piDens (volume.restrict (Set.Ioi (0 : ℝ))))
    (hA2 : ∃ ε δ β : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < β ∧
      ∀ α : ℝ, 0 < α → α < ε → (1 / δ) * α ^ β ≤ piDens α ∧ piDens α ≤ δ * α ^ β),
    (∀ k : ℕ, 1 ≤ k → k ≤ n →
        Integrable (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α)
          (volume.restrict (Set.Ioi (0 : ℝ))) ∧
        0 < ∫ α : ℝ, (α ^ k / dpRisingFactorial α n) * piDens α
              ∂(volume.restrict (Set.Ioi (0 : ℝ))))
    ∧ (∀ ω : ℕ → ℝ,
        0 < ∑ A ∈ dpTau n t,
              ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B →
        dpPostProb g q0 piDens n t ω > 0 ∧
        dpRatio g q0 piDens t n s ω =
          ((∫ α : ℝ, (α ^ (t + s) / dpRisingFactorial α n) * piDens α
              ∂(volume.restrict (Set.Ioi (0 : ℝ)))) /
           (∫ α : ℝ, (α ^ t / dpRisingFactorial α n) * piDens α
              ∂(volume.restrict (Set.Ioi (0 : ℝ))))) *
          ((∑ A ∈ dpTau n (t + s),
              ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) /
           (∑ A ∈ dpTau n t,
              ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B))) := by
  /- @proof-region region.target-node.session.2a6b49b0b6f67d0c begin -/
  intro t ht c hc g q0 θstar M hM piDens n s hn hs hts hg_meas hg_nonneg hg_zero hg_pos hg_le hg_int hg_integrable
    hq0_meas hq0_nonneg hq0_int hq0_integrable hpi_meas hpi_nonneg hpi_zero hpi_int hpi_integrable hA2
  obtain ⟨eps, delta, beta, heps, hdelta, hbeta, hA2b⟩ := hA2
  have htn : t ≤ n := hn
  have htn : t ≤ n := hn
  have hn1 : 1 ≤ n := le_trans ht hn
  have hRmeas : Measurable fun α : ℝ => dpRisingFactorial α n := by
    unfold dpRisingFactorial
    exact Finset.measurable_prod _ (fun j _ => measurable_id.add_const _)
  have hRpos : ∀ α : ℝ, 0 < α → 0 < dpRisingFactorial α n := by
    intro α hα
    unfold dpRisingFactorial
    exact Finset.prod_pos (fun j _ => by
      have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith)
  have hα_le_R : ∀ α : ℝ, 0 < α → α ≤ dpRisingFactorial α n := by
    intro α hα
    have hsplit : dpRisingFactorial α n
        = α * ∏ j ∈ Finset.range (n - 1), (α + ((j + 1 : ℕ) : ℝ)) := by
      unfold dpRisingFactorial
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [Finset.prod_range_succ', Nat.cast_zero, add_zero, mul_comm]
    have hprod : (1:ℝ) ≤ ∏ j ∈ Finset.range (n - 1), (α + ((j + 1 : ℕ) : ℝ)) := by
      have h := Finset.prod_le_prod (s := Finset.range (n - 1)) (f := fun _ : ℕ => (1:ℝ))
        (g := fun j : ℕ => α + ((j + 1 : ℕ) : ℝ)) (fun i _ => zero_le_one) (fun i _ => by
          show (1:ℝ) ≤ α + ((i + 1 : ℕ) : ℝ)
          have h3 : (1:ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
            have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
            push_cast
            linarith
          linarith)
      simpa using h
    rw [hsplit]
    exact le_mul_of_one_le_right (le_of_lt hα) hprod
  have hpow_le_R : ∀ α : ℝ, 0 < α → α ^ n ≤ dpRisingFactorial α n := by
    intro α hα
    have h := Finset.prod_le_prod (s := Finset.range n) (f := fun _ : ℕ => α)
      (g := fun j : ℕ => α + (j : ℝ)) (fun i _ => le_of_lt hα) (fun i _ => by
        show α ≤ α + (i : ℝ)
        have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
        linarith)
    simpa [dpRisingFactorial, Finset.prod_const] using h
  have hPartA : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      Integrable (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α)
          (volume.restrict (Set.Ioi (0 : ℝ))) ∧
        0 < ∫ α : ℝ, (α ^ k / dpRisingFactorial α n) * piDens α
          ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro k hk1 hkn
    have hratio : ∀ α : ℝ, 0 < α → α ^ k / dpRisingFactorial α n ≤ 1 := by
      intro α hα
      have hR : 0 < dpRisingFactorial α n := hRpos α hα
      rw [div_le_one hR]
      by_cases hα1 : α ≤ 1
      · calc α ^ k = α ^ (k - 1) * α := by rw [← pow_succ, Nat.sub_add_cancel hk1]
          _ ≤ 1 * α := mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt hα) hα1) (le_of_lt hα)
          _ = α := one_mul α
          _ ≤ dpRisingFactorial α n := hα_le_R α hα
      · push_neg at hα1
        exact le_trans (pow_le_pow_right₀ hα1.le hkn) (hpow_le_R α hα)
    have hf_meas : Measurable fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α :=
      ((measurable_id.pow_const k).div hRmeas).mul hpi_meas
    have hnn : ∀ α : ℝ, 0 ≤ (α ^ k / dpRisingFactorial α n) * piDens α := by
      intro α
      by_cases hα : (0:ℝ) < α
      · exact mul_nonneg (div_nonneg (le_of_lt (pow_pos hα k)) (le_of_lt (hRpos α hα)))
          (hpi_nonneg α hα)
      · push_neg at hα
        rw [hpi_zero α hα, mul_zero]
    have hf_le : ∀ α : ℝ, ‖(α ^ k / dpRisingFactorial α n) * piDens α‖ ≤ piDens α := by
      intro α
      rw [Real.norm_of_nonneg (hnn α)]
      by_cases hα : (0:ℝ) < α
      · have h2 : α ^ k / dpRisingFactorial α n ≤ 1 := hratio α hα
        calc (α ^ k / dpRisingFactorial α n) * piDens α ≤ 1 * piDens α :=
              mul_le_mul_of_nonneg_right h2 (hpi_nonneg α hα)
          _ = piDens α := one_mul _
      · push_neg at hα
        rw [hpi_zero α hα, mul_zero]
    have hint : Integrable (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hpi_integrable.mono' hf_meas.aestronglyMeasurable (Filter.Eventually.of_forall hf_le)
    refine ⟨hint, ?_⟩
    obtain ⟨m, hmpos, hmeps, hm1⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ eps ∧ m ≤ 1 :=
      ⟨min eps 1, lt_min heps zero_lt_one, min_le_left _ _, min_le_right _ _⟩
    have hsupp : Set.Ioo (m / 2) m ⊆
        Function.support (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α) := by
      intro α hα
      have hαpos : 0 < α := by linarith [hα.1, hmpos]
      have hαeps : α < eps := by linarith [hα.2, hmeps]
      have hb : 0 < (1 / delta) * α ^ beta := by
        have h1 : 0 < α ^ beta := Real.rpow_pos_of_pos hαpos beta
        have h2 : 0 < 1 / delta := by positivity
        positivity
      have hπ : 0 < piDens α := lt_of_lt_of_le hb (hA2b α hαpos hαeps).1
      have h3 : 0 < α ^ k / dpRisingFactorial α n :=
        div_pos (pow_pos hαpos k) (hRpos α hαpos)
      exact mul_ne_zero (ne_of_gt h3) (ne_of_gt hπ)
    have hmeasure : 0 < volume (Set.Ioo (m / 2) m) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    have hmono : volume (Set.Ioo (m / 2) m) ≤
        volume (Function.support (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α) ∩
          Set.Ioi (0:ℝ)) :=
      measure_mono (fun x hx => ⟨hsupp hx, Set.mem_Ioi.2 (by linarith [hx.1, hmpos])⟩)
    have hnn' : ∀ᵐ α ∂(volume.restrict (Set.Ioi (0:ℝ))),
        0 ≤ (α ^ k / dpRisingFactorial α n) * piDens α :=
      Filter.Eventually.of_forall hnn
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn' hint]
    exact lt_of_lt_of_le hmeasure hmono
  refine ⟨hPartA, ?_⟩
  intro ω hD
  classical
  have hmarg : ∀ A : Finset (Fin n), 0 ≤ dpMargLik g q0 (dpXseq n ω) A := by
    intro A
    unfold dpMargLik
    exact integral_nonneg (fun θ => mul_nonneg (Finset.prod_nonneg fun i _ => hg_nonneg _) (hq0_nonneg θ))
  have hDnn : ∀ k : ℕ,
      0 ≤ ∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B := by
    intro k
    exact Finset.sum_nonneg fun A _ =>
      Finset.prod_nonneg fun B _ => mul_nonneg (Nat.cast_nonneg (B.card - 1).factorial) (hmarg B)
  have hfac : ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ α : ℝ,
      (∑ A ∈ dpTau n k, dpPartPrior α n A * ∏ B ∈ A, dpMargLik g q0 (dpXseq n ω) B)
        = (α ^ k / dpRisingFactorial α n) *
            (∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) := by
    intro k hk1 hkn α
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    simp only [dpTau, dpIsPartition, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    have hAcard : A.card = k := hA.1
    simp only [dpPartPrior, hAcard, Finset.prod_mul_distrib]
    ring
  have hbridge : ∀ f : ℝ → ℝ, (∀ x : ℝ, x ≤ 0 → f x = 0) →
      ∫ x, f x ∂volume = ∫ x in Set.Ioi (0:ℝ), f x := by
    intro f hf
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1
    funext x
    by_cases hx : x ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem hx]
    · have hx' : x ≤ 0 := by simpa using hx
      simp [hx, hf x hx']
  have hN : ∀ k : ℕ, 1 ≤ k → k ≤ n → dpNpost g q0 piDens n k (dpXseq n ω)
      = (∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B)
        * (∫ α in Set.Ioi (0:ℝ), (α ^ k / dpRisingFactorial α n) * piDens α) := by
    intro k hk1 hkn
    have hvan : ∀ x : ℝ, x ≤ 0 → (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α) x = 0 := by
      intro x hx
      show (x ^ k / dpRisingFactorial x n) * piDens x = 0
      rw [hpi_zero x hx, mul_zero]
    have hstep : (∫ α : ℝ, (∑ A ∈ dpTau n k, dpPartPrior α n A * ∏ B ∈ A, dpMargLik g q0 (dpXseq n ω) B) * piDens α ∂volume)
        = ∫ α : ℝ, (∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) * ((α ^ k / dpRisingFactorial α n) * piDens α) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
      show (∑ A ∈ dpTau n k, dpPartPrior α n A * ∏ B ∈ A, dpMargLik g q0 (dpXseq n ω) B) * piDens α
          = (∑ A ∈ dpTau n k, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) * ((α ^ k / dpRisingFactorial α n) * piDens α)
      rw [hfac k hk1 hkn α]
      ring
    simp only [dpNpost]
    rw [hstep, integral_const_mul,
      hbridge (fun α : ℝ => (α ^ k / dpRisingFactorial α n) * piDens α) hvan]
  have hpos : 0 < dpNpost g q0 piDens n t (dpXseq n ω) := by
    rw [hN t ht htn]
    exact mul_pos hD (hPartA t ht htn).2
  have hZ : 0 < dpZpost g q0 piDens n (dpXseq n ω) := by
    have hsum : dpNpost g q0 piDens n t (dpXseq n ω) ≤ dpZpost g q0 piDens n (dpXseq n ω) := by
      simp only [dpZpost]
      refine Finset.single_le_sum (f := fun k => dpNpost g q0 piDens n k (dpXseq n ω)) (fun k hk => ?_) ?_
      · rw [Finset.mem_Icc] at hk
        show 0 ≤ dpNpost g q0 piDens n k (dpXseq n ω)
        rw [hN k hk.1 hk.2]
        exact mul_nonneg (hDnn k) (le_of_lt (hPartA k hk.1 hk.2).2)
      · rw [Finset.mem_Icc]
        exact ⟨ht, htn⟩
    exact lt_of_lt_of_le hpos hsum
  have hZne : dpZpost g q0 piDens n (dpXseq n ω) ≠ 0 := ne_of_gt hZ
  have hprob : ∀ k : ℕ, dpPostProb g q0 piDens n k ω
      = dpNpost g q0 piDens n k (dpXseq n ω) / dpZpost g q0 piDens n (dpXseq n ω) := by
    intro k
    unfold dpPostProb dpPostK
    rw [if_neg hZne]
  refine ⟨?_, ?_⟩
  · rw [hprob t]
    exact div_pos hpos hZ
  · have hts1 : 1 ≤ t + s := by omega
    have hne : dpPostProb g q0 piDens n t ω ≠ 0 := by
      rw [hprob t]
      exact ne_of_gt (div_pos hpos hZ)
    unfold dpRatio
    rw [if_neg hne, hprob (t + s), hprob t, hN (t + s) hts1 hts, hN t ht htn]
    have hDtne : (∑ A ∈ dpTau n t, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) ≠ 0 :=
      ne_of_gt hD
    have hItne : (∫ α in Set.Ioi (0:ℝ), (α ^ t / dpRisingFactorial α n) * piDens α) ≠ 0 :=
      ne_of_gt (hPartA t ht htn).2
    have hNtne : (∑ A ∈ dpTau n t, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) *
        (∫ α in Set.Ioi (0:ℝ), (α ^ t / dpRisingFactorial α n) * piDens α) ≠ 0 :=
      mul_ne_zero hDtne hItne
    have hQne : (∑ A ∈ dpTau n t, ∏ B ∈ A, ((B.card - 1).factorial : ℝ) * dpMargLik g q0 (dpXseq n ω) B) *
        (∫ α in Set.Ioi (0:ℝ), (α ^ t / dpRisingFactorial α n) * piDens α) /
          dpZpost g q0 piDens n (dpXseq n ω) ≠ 0 :=
      div_ne_zero hNtne hZne
    field_simp
  /- @proof-region region.target-node.session.2a6b49b0b6f67d0c end -/

end

end Statlib.Imported
