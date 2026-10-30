import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Vocabulary
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.Base
import ProverJobs.paper_fresh_20261030t143835550708z_hulc.ExternalNodes.Node_797c756d42274b989c69

namespace PaperProofTasks.paper_fresh_20261030t143835550708z_hulc

open _root_.PaperProofTasks.paper_fresh_20261030t143835550708z_hulc.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported
open _root_.Statlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1727152864_9ef8801e : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (theta0 : ℝ) (Delta : ℝ) (hDelta_nonneg : 0 ≤ Delta) (hDelta_lt_half : Delta < 1 / 2)
    (Balpha : ℕ) (hBalpha_ge_one : 1 ≤ Balpha)
    (thetaHat : ℕ → Ω → ℝ) (hthetaHat_meas : ∀ j, Measurable (thetaHat j))
    (hthetaHat_indep : iIndepFun (fun j : Fin Balpha => thetaHat ((j : ℕ) + 1)) P)
    (hmedBias_le : ∀ j : Fin Balpha, medBias P theta0 (thetaHat ((j : ℕ) + 1)) ≤ Delta)
    (k : ℕ) (hk_ge_one : 1 ≤ k) (hk_le_Balpha : k ≤ Balpha),
    P {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} ≤ ENNReal.ofReal (Pmis Delta k) := by
  /- @proof-region region.target-node.session.1256ca88cc9c8244 begin -/
  intro Ω _ P _ theta0 Delta hDelta_nonneg hDelta_lt_half Balpha hBalpha_ge_one thetaHat hthetaHat_meas hthetaHat_indep hmedBias_le k hk_ge_one hk_le_Balpha
  have hbeq : ∀ (g : Ω → ℝ), PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.medBias P g theta0 = medBias P theta0 g := by
    intro g
    rfl
  have hbias_range : ∀ g : Ω → ℝ, medBias P theta0 g ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    intro g
    refine ⟨?_, ?_⟩
    · unfold medBias
      exact le_max_right _ _
    · unfold medBias
      refine max_le ?_ (by norm_num)
      have hp : (0 : ℝ) ≤ min (P {ω | theta0 ≤ g ω}).toReal (P {ω | g ω ≤ theta0}).toReal := by
        rcases le_total (P {ω | theta0 ≤ g ω}).toReal (P {ω | g ω ≤ theta0}).toReal with h | h
        · rw [min_eq_left h]; exact ENNReal.toReal_nonneg
        · rw [min_eq_right h]; exact ENNReal.toReal_nonneg
      linarith
  have hmem : PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.paperDelta P (fun j : Fin k => thetaHat ((j : ℕ) + 1)) theta0 (by omega) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    unfold PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.paperDelta
    simp only [hbeq]
    refine ⟨?_, ?_⟩
    · exact le_trans (hbias_range _).1 (Finset.le_sup' (f := fun j : Fin k => medBias P theta0 (thetaHat ((j : ℕ) + 1))) (Finset.mem_univ (⟨0, by omega⟩ : Fin k)))
    · exact (Finset.sup'_le_iff _ _).mpr (fun j _ => (hbias_range _).2)
  have hle : PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.paperDelta P (fun j : Fin k => thetaHat ((j : ℕ) + 1)) theta0 (by omega) ≤ Delta := by
    unfold PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.paperDelta
    simp only [hbeq]
    exact (Finset.sup'_le_iff _ _).mpr (fun j _ => by simpa using hmedBias_le (Fin.castLE hk_le_Balpha j))
  have hmeas : ∀ j : Fin k, Measurable (fun ω => thetaHat ((j : ℕ) + 1) ω) := fun j => hthetaHat_meas _
  have hindep : iIndepFun (fun j : Fin k => (fun ω => thetaHat ((j : ℕ) + 1) ω)) P := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul] at hthetaHat_indep ⊢
    intro S sets hsets
    let e : Fin k → Fin Balpha := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk_le_Balpha⟩
    have he : Function.Injective e := fun a b h => Fin.ext (by simpa [e] using congrArg Fin.val h)
    let sets' : Fin Balpha → Set ℝ := fun j => if h : ∃ i ∈ S, e i = j then sets h.choose else Set.univ
    have hsets_e : ∀ i ∈ S, sets' (e i) = sets i := by
      intro i hi
      have hmem : ∃ i' ∈ S, e i' = e i := ⟨i, hi, rfl⟩
      change (if h : ∃ i' ∈ S, e i' = e i then sets h.choose else Set.univ) = sets i
      rw [dif_pos hmem]
      congr 1
      exact he (Classical.choose_spec hmem).2
    have hmeas' : ∀ j ∈ S.image e, MeasurableSet (sets' j) := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [hsets_e i hi]
      exact hsets i hi
    have key1 : (⋂ i ∈ S, thetaHat ((i : ℕ) + 1) ⁻¹' sets i)
        = (⋂ j ∈ S.image e, thetaHat ((j : ℕ) + 1) ⁻¹' sets' j) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h j hj
        rw [Finset.mem_image] at hj
        obtain ⟨i, hi, rfl⟩ := hj
        rw [hsets_e i hi]
        simpa using h i hi
      · intro h i hi
        have := h (e i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        rw [hsets_e i hi] at this
        simpa using this
    have key2 : (∏ i ∈ S, P (thetaHat ((i : ℕ) + 1) ⁻¹' sets i))
        = (∏ j ∈ S.image e, P (thetaHat ((j : ℕ) + 1) ⁻¹' sets' j)) := by
      rw [Finset.prod_image (s := S) (g := e) (f := fun j : Fin Balpha => P (thetaHat ((j : ℕ) + 1) ⁻¹' sets' j)) (fun a _ b _ h => he h)]
      exact Finset.prod_congr rfl (fun i hi => by rw [hsets_e i hi])
    have hres := hthetaHat_indep (S.image e) (sets := sets') hmeas'
    rw [key1, key2]
    exact hres
  have hmain := PaperProofTasks.job_paper_6093c8cdedac44ebaae3246c2f49ba3b.Statlib.Imported.paper_6093c8cdedac44ebaae3246c2f49ba3b k (by omega) P theta0 (fun j : Fin k => (fun ω => thetaHat ((j : ℕ) + 1) ω)) hmeas hindep hmem
  have hset : {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω}
      = {ω | theta0 ∉ Set.Icc (Finset.univ.inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun j : Fin k => (fun j ω => thetaHat ((j : ℕ) + 1) ω) j ω)) (Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun j : Fin k => (fun j ω => thetaHat ((j : ℕ) + 1) ω) j ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hshift : ∀ (Pp : ℕ → Prop), (∀ i ∈ Finset.Icc 1 k, Pp i) ↔ ∀ j : Fin k, Pp ((j : ℕ) + 1) := by
      intro Pp
      constructor
      · intro hh j
        exact hh ((j : ℕ) + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)
      · intro hh i hi
        rw [Finset.mem_Icc] at hi
        obtain ⟨h1, h2⟩ := hi
        have hlt : i - 1 < k := by omega
        have h' := hh ⟨i - 1, hlt⟩
        have hsub : i - 1 + 1 = i := by omega
        simpa [hsub] using h'
    have hL : (¬ inCI theta0 thetaHat (fun _ => k) ω) ↔ (∀ i ∈ Finset.Icc 1 k, theta0 < thetaHat i ω) ∨ (∀ i ∈ Finset.Icc 1 k, thetaHat i ω < theta0) := by
      unfold inCI
      simp only []
      rw [not_and_or]
      have hA : ¬(∃ j ∈ Finset.Icc 1 k, thetaHat j ω ≤ theta0) ↔ (∀ i ∈ Finset.Icc 1 k, theta0 < thetaHat i ω) := by
        simp only [not_exists, not_and, not_le]
      have hB : ¬(∃ j ∈ Finset.Icc 1 k, theta0 ≤ thetaHat j ω) ↔ (∀ i ∈ Finset.Icc 1 k, thetaHat i ω < theta0) := by
        simp only [not_exists, not_and, not_le]
      rw [hA, hB]
    have hR : (theta0 ∉ Set.Icc (Finset.univ.inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun j : Fin k => (fun j ω => thetaHat ((j : ℕ) + 1) ω) j ω)) (Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun j : Fin k => (fun j ω => thetaHat ((j : ℕ) + 1) ω) j ω))) ↔ (∀ i ∈ Finset.Icc 1 k, theta0 < thetaHat i ω) ∨ (∀ i ∈ Finset.Icc 1 k, thetaHat i ω < theta0) := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le, Finset.lt_inf'_iff, Finset.sup'_lt_iff]
      simp only [Finset.mem_univ, true_implies, hshift (fun i => theta0 < thetaHat i ω), hshift (fun i => thetaHat i ω < theta0)]
    rw [hL, hR]
  have hpms : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 / 2 → (1 / 2 - a) ^ k + (1 / 2 + a) ^ k ≤ (1 / 2 - b) ^ k + (1 / 2 + b) ^ k := by
    have hmono : MonotoneOn (fun δ : ℝ => (1 / 2 - δ) ^ k + (1 / 2 + δ) ^ k) (Set.Icc 0 (1 / 2)) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc 0 (1 / 2)) (f' := fun x : ℝ => k * ((1 / 2 + x) ^ (k - 1) - (1 / 2 - x) ^ (k - 1))) (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
      · fun_prop
      · intro x hx
        show HasDerivWithinAt (fun δ : ℝ => (1 / 2 - δ) ^ k + (1 / 2 + δ) ^ k) (k * ((1 / 2 + x) ^ (k - 1) - (1 / 2 - x) ^ (k - 1))) (interior (Set.Icc 0 (1 / 2))) x
        have h1 : HasDerivAt (fun δ : ℝ => (1 / 2 - δ) ^ k) (k * (1 / 2 - x) ^ (k - 1) * (-1)) x := by
          have h := (HasDerivAt.const_sub (1 / 2) (hasDerivAt_id x)).pow k
          simpa using h
        have h2 : HasDerivAt (fun δ : ℝ => (1 / 2 + δ) ^ k) (k * (1 / 2 + x) ^ (k - 1) * 1) x := by
          have h := (HasDerivAt.const_add (1 / 2) (hasDerivAt_id x)).pow k
          simpa using h
        have hd := h1.add h2
        have hconv : k * (1 / 2 - x) ^ (k - 1) * (-1) + k * (1 / 2 + x) ^ (k - 1) * 1 = k * ((1 / 2 + x) ^ (k - 1) - (1 / 2 - x) ^ (k - 1)) := by ring
        rw [hconv] at hd
        exact hd.hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        obtain ⟨hx0, hx1⟩ := hx
        show (0 : ℝ) ≤ k * ((1 / 2 + x) ^ (k - 1) - (1 / 2 - x) ^ (k - 1))
        have hpow : (1 / 2 - x) ^ (k - 1) ≤ (1 / 2 + x) ^ (k - 1) := by
          gcongr <;> linarith
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hkk : (k : ℝ) * (1 / 2 - x) ^ (k - 1) ≤ (k : ℝ) * (1 / 2 + x) ^ (k - 1) := mul_le_mul_of_nonneg_left hpow hk
        have hrw : k * ((1 / 2 + x) ^ (k - 1) - (1 / 2 - x) ^ (k - 1)) = (k : ℝ) * (1 / 2 + x) ^ (k - 1) - (k : ℝ) * (1 / 2 - x) ^ (k - 1) := by ring
        rw [hrw]
        linarith [hkk]
    intro a b ha hab hb
    exact hmono ⟨ha, le_trans hab hb⟩ ⟨le_trans ha hab, hb⟩ hab
  have hreal : P.real {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} ≤ Pmis Delta k := by
    rw [hset]
    refine le_trans hmain ?_
    exact hpms _ Delta hmem.1 hle (le_of_lt hDelta_lt_half)
  exact Statlib.StatFoundation.BasicAnalysis.measure_le_ofReal_of_measureReal_le P {ω | ¬ inCI theta0 thetaHat (fun _ => k) ω} hreal
  /- @proof-region region.target-node.session.1256ca88cc9c8244 end -/

end

end Statlib.Imported

