import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Vocabulary
import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.ProvedNodes
import ProverJobs.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Base

open MeasureTheory ProbabilityTheory
namespace Statlib.Imported
noncomputable section

theorem paper_6093c8cdedac44ebaae3246c2f49ba3b
    (B : ℕ) (hB : 0 < B) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ₀ : ℝ) (θ : Fin B → Ω → ℝ) (hθ : ∀ j, Measurable (θ j)) (hindep : iIndepFun θ μ)
    (hΔ : paperDelta μ θ θ₀ hB ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    μ.real {ω | θ₀ ∉ Set.Icc
        (Finset.univ.inf' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => θ j ω))
        (Finset.univ.sup' ⟨⟨0, hB⟩, Finset.mem_univ _⟩ (fun j => θ j ω))}
      ≤ (1 / 2 - paperDelta μ θ θ₀ hB) ^ B + (1 / 2 + paperDelta μ θ θ₀ hB) ^ B
:= by
  /- @proof-region region.root.fa4067abbf44 begin -/
  let a : Fin B → ℝ := fun j => μ.real {ω | θ j ω < θ₀}
  let b : Fin B → ℝ := fun j => μ.real {ω | θ₀ < θ j ω}
  let p : Fin B → ℝ := fun j => μ.real {ω | θ₀ ≤ θ j ω}
  let q : Fin B → ℝ := fun j => μ.real {ω | θ j ω ≤ θ₀}
  obtain ⟨hΔ0, hΔhalf⟩ := hΔ
  have huniv : μ.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ]
    simp
  have ha : ∀ j : Fin B, a j = 1 - p j := by
    intro j
    have hmeas : MeasurableSet {ω | θ₀ ≤ θ j ω} := measurableSet_le measurable_const (hθ j)
    have h := measureReal_compl (μ := μ) (s := {ω | θ₀ ≤ θ j ω}) hmeas
    have hset : {ω | θ₀ ≤ θ j ω}ᶜ = {ω | θ j ω < θ₀} := by
      ext ω
      simp [not_le]
    rw [hset] at h
    show μ.real {ω | θ j ω < θ₀} = 1 - μ.real {ω | θ₀ ≤ θ j ω}
    linarith [h, huniv]
  have hb : ∀ j : Fin B, b j = 1 - q j := by
    intro j
    have hmeas : MeasurableSet {ω | θ j ω ≤ θ₀} := measurableSet_le (hθ j) measurable_const
    have h := measureReal_compl (μ := μ) (s := {ω | θ j ω ≤ θ₀}) hmeas
    have hset : {ω | θ j ω ≤ θ₀}ᶜ = {ω | θ₀ < θ j ω} := by
      ext ω
      simp [not_le]
    rw [hset] at h
    show μ.real {ω | θ₀ < θ j ω} = 1 - μ.real {ω | θ j ω ≤ θ₀}
    linarith [h, huniv]
  have hst : (1 / 2 - paperDelta μ θ θ₀ hB) = 1 - (1 / 2 + paperDelta μ θ θ₀ hB) := by ring
  have hs_lower : (1 / 2 : ℝ) ≤ 1 / 2 + paperDelta μ θ θ₀ hB := by linarith
  have hs_upper : 1 / 2 + paperDelta μ θ θ₀ hB ≤ 1 := by linarith
  have hx0 : ∀ j : Fin B, 0 ≤ a j := fun j => measureReal_nonneg
  have hy0 : ∀ j : Fin B, 0 ≤ b j := fun j => measureReal_nonneg
  have hmed : ∀ j : Fin B, medBias μ (θ j) θ₀ ≤ paperDelta μ θ θ₀ hB := by
    intro j
    exact Finset.le_sup' (fun j => medBias μ (θ j) θ₀) (Finset.mem_univ j)
  have hmin : ∀ j : Fin B, (1 / 2 : ℝ) - paperDelta μ θ θ₀ hB ≤ min (p j) (q j) := by
    intro j
    have h1 : (1 / 2 : ℝ) - min (p j) (q j) ≤ max ((1 / 2 : ℝ) - min (p j) (q j)) 0 :=
      le_max_left _ _
    have h2 : (1 / 2 : ℝ) - min (p j) (q j) ≤ paperDelta μ θ θ₀ hB := le_trans h1 (hmed j)
    linarith
  have hx1 : ∀ j : Fin B, a j ≤ 1 / 2 + paperDelta μ θ θ₀ hB := by
    intro j
    have h4 : (1 / 2 : ℝ) - paperDelta μ θ θ₀ hB ≤ p j := le_trans (hmin j) (min_le_left _ _)
    linarith [ha j, h4]
  have hy1 : ∀ j : Fin B, b j ≤ 1 / 2 + paperDelta μ θ θ₀ hB := by
    intro j
    have h4 : (1 / 2 : ℝ) - paperDelta μ θ θ₀ hB ≤ q j := le_trans (hmin j) (min_le_right _ _)
    linarith [hb j, h4]
  have hxy : ∀ j : Fin B, a j + b j ≤ 1 := by
    intro j
    have hmono : b j ≤ p j := by
      refine measureReal_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    linarith [ha j, hmono]
  have hid := statopia_math_node_3135439720_9bebc028 B hB μ θ₀ θ hθ hindep
  have key := statopia_math_node_1024464762_c87d6fc0 (1 / 2 + paperDelta μ θ θ₀ hB)
    (1 / 2 - paperDelta μ θ θ₀ hB) B a b hs_lower hs_upper hst hx0 hx1 hy0 hy1 hxy
  exact le_trans (le_of_eq hid) (le_trans key (le_of_eq (add_comm _ _)))
  /- @proof-region region.root.fa4067abbf44 end -/

end

end Statlib.Imported
