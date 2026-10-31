import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2110233091_1dad31d5_04263b23
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.ProvedNodes.Node_2642199537_30588a87_02d4db59

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_341907188_a9df01ea : ∀ {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (P : Measure X) [IsProbabilityMeasure P]
    (nu : Measure H) [IsProbabilityMeasure nu]
    (g : H → X → ℝ) (hg : Measurable (Function.uncurry g))
    (delta1 eps : ℝ) (heps : 0 < eps)
    (h_int : ∀ᵐ h ∂nu, MeasureTheory.Integrable (g h) P)
    (h_le_zero : ∀ᵐ h ∂nu, ∫ x, g h x ∂P ≤ 0)
    (h_lower : ∀ᵐ h ∂nu, -delta1 ≤ ∫ x, g h x ∂P)
    (h_pos_bound : ∀ᵐ h ∂nu, ∫⁻ x, ENNReal.ofReal (max (g h x) 0) ∂P ≤ (1 : ℝ≥0∞))
    (h_neg_bound : ∀ᵐ h ∂nu,
      ∫⁻ x, ENNReal.ofReal (max (-(g h x)) 0) ∂P ≤ ENNReal.ofReal (delta1 + 1))
    (h_neg_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (-(g h x)) 0) ∂nu < ⊤)
    (h_pos_fin : ∀ᵐ x ∂P, ∫⁻ h, ENNReal.ofReal (max (g h x) 0) ∂nu < ⊤),
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (delta1 + eps))) ≤
        ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂nu := by
  /- @proof-region region.target-node.session.01e719a297e1c154 begin -/
  intro X H _ _ P _ ν _ g hg δ1 ε hε hInt hUpper hLower hPos hNeg hNegFin hPosFin
  classical
  set gbar : X → ℝ := fun x => ∫ h, g h x ∂ν with hgbar
  have hSLLN_aux (hMeas : Measurable gbar) (hInt_bar : Integrable gbar P) :
      ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ)) atTop
          (nhds (∫ x, gbar x ∂P)) := by
    have hmap0 : Measure.map (fun x : ℕ → X => x 0) (Measure.infinitePi (fun _ : ℕ => P)) = P :=
      Measure.infinitePi_map_eval (fun _ : ℕ => P) 0
    have hInt0 : Integrable (fun x : ℕ → X => gbar (x 0)) (Measure.infinitePi (fun _ : ℕ => P)) := by
      have hI : Integrable gbar
          (Measure.map (fun x : ℕ → X => x 0) (Measure.infinitePi (fun _ : ℕ => P))) := by
        rw [hmap0]
        exact hInt_bar
      have h2 := hI.comp_measurable (f := fun x : ℕ → X => x 0) (measurable_pi_apply 0)
      simpa [Function.comp] using h2
    have hfam : iIndepFun (fun i (ω : ℕ → X) => gbar (ω i))
        (Measure.infinitePi (fun _ : ℕ => P)) :=
      iIndepFun_infinitePi (fun _ => hMeas)
    have hindep : Pairwise (Function.onFun
        (fun x1 x2 => x1 ⟂ᵢ[Measure.infinitePi (fun _ : ℕ => P)] x2)
        (fun i (x : ℕ → X) => gbar (x i))) := by
      intro i j hij
      exact hfam.indepFun hij
    have hident : ∀ i : ℕ, IdentDistrib (fun x : ℕ → X => gbar (x i))
        (fun x : ℕ → X => gbar (x 0)) (Measure.infinitePi (fun _ : ℕ => P))
        (Measure.infinitePi (fun _ : ℕ => P)) := by
      intro i
      have hi : Measure.map (fun x : ℕ → X => gbar (x i))
          (Measure.infinitePi (fun _ : ℕ => P)) = Measure.map gbar P := by
        have h := Measure.map_map (μ := Measure.infinitePi (fun _ : ℕ => P))
          (f := fun x : ℕ → X => x i) hMeas (measurable_pi_apply i)
        rw [Measure.infinitePi_map_eval (fun _ : ℕ => P) i] at h
        exact h.symm
      have h0 : Measure.map (fun x : ℕ → X => gbar (x 0))
          (Measure.infinitePi (fun _ : ℕ => P)) = Measure.map gbar P := by
        have h := Measure.map_map (μ := Measure.infinitePi (fun _ : ℕ => P))
          (f := fun x : ℕ → X => x 0) hMeas (measurable_pi_apply 0)
        rw [Measure.infinitePi_map_eval (fun _ : ℕ => P) 0] at h
        exact h.symm
      refine ⟨?_, ?_, ?_⟩
      all_goals
        first
          | exact (hMeas.comp (measurable_pi_apply i)).aemeasurable
          | exact (hMeas.comp (measurable_pi_apply 0)).aemeasurable
          | exact hi.trans h0.symm
    have hsw : ∫ x : ℕ → X, gbar (x 0) ∂(Measure.infinitePi (fun _ : ℕ => P)) = ∫ x, gbar x ∂P := by
      have key : ∫ x : ℕ → X, gbar (x 0) ∂(Measure.infinitePi (fun _ : ℕ => P))
          = ∫ x, gbar x ∂(Measure.map (fun x : ℕ → X => x 0)
              (Measure.infinitePi (fun _ : ℕ => P))) :=
        (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable hMeas.aestronglyMeasurable).symm
      rw [key, hmap0]
    have hmain := ProbabilityTheory.strong_law_ae_real (fun i (x : ℕ → X) => gbar (x i))
      hInt0 hindep hident
    rwa [hsw] at hmain
  obtain ⟨hMeas0, hInt0bar, hL0⟩ :=
    statopia_math_node_2642199537_30588a87 P ν g hg δ1 hInt hLower hPos hNeg
  have hSLLN : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ)) atTop
        (nhds (∫ x, gbar x ∂P)) :=
    hSLLN_aux (by simpa [hgbar] using hMeas0) (by simpa [hgbar] using hInt0bar)
  have hL : -δ1 ≤ ∫ x, gbar x ∂P := by
    simpa [hgbar] using hL0
  have hbig : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -((n : ℝ) * (δ1 + ε)) ≤ ∑ i ∈ Finset.range n, gbar (x i) := by
    filter_upwards [hSLLN] with x hx
    have hev : ∀ᶠ n : ℕ in atTop, -(δ1 + ε) < (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) :=
      hx.eventually (by
        filter_upwards [isOpen_Ioi.mem_nhds (show -(δ1 + ε) < ∫ y, gbar y ∂P by linarith)] with y hy
        exact hy)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlt := hN n (le_trans (le_max_left N 1) hn)
    have hmul : -(δ1 + ε) * (n : ℝ) <
        (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) * (n : ℝ) :=
      mul_lt_mul_of_pos_right hlt hpos
    have hsimp : (∑ i ∈ Finset.range n, gbar (x i)) / (n : ℝ) * (n : ℝ)
        = ∑ i ∈ Finset.range n, gbar (x i) := by
      field_simp
    rw [hsimp] at hmul
    nlinarith
  have hJensen : ∀ᵐ x ∂(Measure.infinitePi (fun _ : ℕ => P)),
      ∀ n : ℕ, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, gbar (x i))) ≤
        ∫⁻ h, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range n, g h (x i))) ∂ν := by
    have h := statopia_math_node_2110233091_1dad31d5 P ν g hg hNegFin hPosFin
    simpa [hgbar] using h
  filter_upwards [hbig, hJensen] with x hx1 hx2
  obtain ⟨N, hN⟩ := hx1
  refine ⟨N, fun n hn => le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) (hx2 n)⟩
  nlinarith [hN n hn]
  /- @proof-region region.target-node.session.01e719a297e1c154 end -/

end Statlib.Imported
