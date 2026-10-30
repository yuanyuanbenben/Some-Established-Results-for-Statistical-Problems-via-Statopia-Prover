import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_4287235009_e1acef55 : ∀ {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (p : ℕ) (hp : 1 ≤ p)
    (J0 : Finset (Fin p)) (hJ0 : J0.Nonempty) (hJ0c : (Finset.univ \ J0).Nonempty)
    (Y : Omega → Fin p → ℝ) (hY : ∀ j : Fin p, Measurable (fun omega => Y omega j))
    (sigma : Fin p → ℝ) (hsigma : ∀ j : Fin p, 0 < sigma j)
    (tau t1 t2 : ℝ) (ht : t1 ≤ t2),
    dK (P.map (fun omega => fmax Finset.univ (fun j : Fin p => Y omega j / (sigma j) ^ tau)))
       (P.map (fun omega => fmax J0 (fun j : Fin p => Y omega j / (sigma j) ^ tau)))
      ≤ (P {omega | fmax J0 (fun j : Fin p => Y omega j / (sigma j) ^ tau) ≤ t2}).toReal
        + (P {omega |
            fmax (Finset.univ \ J0) (fun j : Fin p => Y omega j / (sigma j) ^ tau) > t1}).toReal := by
  /- @proof-region region.target-node.session.51538944f49689d8 begin -/
  intro Ω' instΩ P instP p hp J0 hJ0 hJ0c Y hY sd _hsd tau t1 t2 ht
  let F : Ω' → Fin p → ℝ := fun ω j => Y ω j / sd j ^ tau
  change dK (P.map (fun ω => fmax Finset.univ (F ω))) (P.map (fun ω => fmax J0 (F ω)))
      ≤ (P {ω | fmax J0 (F ω) ≤ t2}).toReal
        + (P {ω | fmax (Finset.univ \ J0) (F ω) > t1}).toReal
  have huniv : (Finset.univ : Finset (Fin p)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hF : ∀ j : Fin p, Measurable (fun ω => F ω j) :=
    fun j => (hY j).div_const (sd j ^ tau)
  have fmax_le : ∀ (s : Finset (Fin p)) (hs : s.Nonempty) (ω : Ω') (a : ℝ),
      (∀ j ∈ s, F ω j ≤ a) → fmax s (F ω) ≤ a := by
    intro s hs ω a h
    show sSup ((F ω) '' (s : Set (Fin p))) ≤ a
    apply csSup_le
    · obtain ⟨j, hj⟩ := hs; exact ⟨F ω j, ⟨j, hj, rfl⟩⟩
    · rintro _ ⟨j, hj, rfl⟩; exact h j hj
  have le_fmax : ∀ (s : Finset (Fin p)) (hs : s.Nonempty) (ω : Ω') (j : Fin p),
      j ∈ s → F ω j ≤ fmax s (F ω) := by
    intro s hs ω j hj
    have hfin : ((F ω) '' (s : Set (Fin p))).Finite :=
      (Finset.finite_toSet s).image (F ω)
    show F ω j ≤ sSup ((F ω) '' (s : Set (Fin p)))
    exact le_csSup hfin.bddAbove ⟨j, hj, rfl⟩
  have hfmax_sup' : ∀ (s : Finset (Fin p)) (hs : s.Nonempty) (ω : Ω'),
      fmax s (F ω) = s.sup' hs (fun j => F ω j) := by
    intro s hs ω
    apply le_antisymm
    · refine fmax_le s hs ω (s.sup' hs (fun j => F ω j)) ?_
      intro j hj
      exact Finset.le_sup' (fun j => F ω j) hj
    · rw [Finset.sup'_le_iff hs (fun j => F ω j)]
      intro j hj
      exact le_fmax s hs ω j hj
  have hmeas_fmax : ∀ (s : Finset (Fin p)) (hs : s.Nonempty), Measurable (fun ω => fmax s (F ω)) := by
    intro s hs
    have hfun : (fun ω => fmax s (F ω)) = s.sup' hs (fun j ω => F ω j) := by
      funext ω
      rw [hfmax_sup' s hs ω, Finset.sup'_apply]
    rw [hfun]
    exact Finset.measurable_sup' hs (f := fun j ω => F ω j) (fun j _ => hF j)
  have hfmax_max : ∀ ω : Ω',
      fmax Finset.univ (F ω) = max (fmax J0 (F ω)) (fmax (Finset.univ \ J0) (F ω)) := by
    intro ω
    apply le_antisymm
    · refine fmax_le Finset.univ huniv ω (max (fmax J0 (F ω)) (fmax (Finset.univ \ J0) (F ω))) ?_
      intro j hj
      by_cases hjj : j ∈ J0
      · exact le_trans (le_fmax J0 hJ0 ω j hjj) (le_max_left _ _)
      · exact le_trans (le_fmax (Finset.univ \ J0) hJ0c ω j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjj⟩)) (le_max_right _ _)
    · apply max_le
      · refine fmax_le J0 hJ0 ω (fmax Finset.univ (F ω)) ?_
        intro j hj; exact le_fmax Finset.univ huniv ω j (Finset.mem_univ j)
      · refine fmax_le (Finset.univ \ J0) hJ0c ω (fmax Finset.univ (F ω)) ?_
        intro j hj; exact le_fmax Finset.univ huniv ω j (Finset.mem_univ j)
  have hleaf : ∀ t : ℝ,
      |(P.map (fun ω => fmax Finset.univ (F ω)) (Set.Iic t)).toReal
        - (P.map (fun ω => fmax J0 (F ω)) (Set.Iic t)).toReal|
      ≤ (P {ω | fmax J0 (F ω) ≤ t2}).toReal
        + (P {ω | fmax (Finset.univ \ J0) (F ω) > t1}).toReal := by
    intro t
    have hmeasU : Measurable (fun ω => fmax Finset.univ (F ω)) := hmeas_fmax Finset.univ huniv
    have hmeasA : Measurable (fun ω => fmax J0 (F ω)) := hmeas_fmax J0 hJ0
    rw [Measure.map_apply hmeasU measurableSet_Iic, Measure.map_apply hmeasA measurableSet_Iic]
    show |(P {ω | fmax Finset.univ (F ω) ≤ t}).toReal
        - (P {ω | fmax J0 (F ω) ≤ t}).toReal|
      ≤ (P {ω | fmax J0 (F ω) ≤ t2}).toReal
        + (P {ω | fmax (Finset.univ \ J0) (F ω) > t1}).toReal
    set U : Set Ω' := {ω | fmax Finset.univ (F ω) ≤ t} with hU
    set A : Set Ω' := {ω | fmax J0 (F ω) ≤ t} with hA
    set A2 : Set Ω' := {ω | fmax J0 (F ω) ≤ t2} with hA2
    set B1 : Set Ω' := {ω | fmax (Finset.univ \ J0) (F ω) > t1} with hB1
    have hmemU : ∀ ω, ω ∈ U ↔ fmax Finset.univ (F ω) ≤ t := by intro ω; simp [hU]
    have hmemA : ∀ ω, ω ∈ A ↔ fmax J0 (F ω) ≤ t := by intro ω; simp [hA]
    have hUA : U ⊆ A := by
      intro ω hω
      rw [hmemU ω] at hω
      rw [hmemA ω]
      rw [hfmax_max ω] at hω
      exact le_trans (le_max_left _ _) hω
    have hun : U ∪ (A \ U) = A := by
      ext x
      simp only [Set.mem_union, Set.mem_diff]
      constructor
      · rintro (hx | ⟨hxA, _⟩)
        · exact hUA hx
        · exact hxA
      · intro hxA
        by_cases hxU : x ∈ U
        · exact Or.inl hxU
        · exact Or.inr ⟨hxA, hxU⟩
    have hUnionEq : P A ≤ P U + P (A \ U) := by
      calc P A = P (U ∪ (A \ U)) := by rw [hun]
        _ ≤ P U + P (A \ U) := measure_union_le U (A \ U)
    have hUnionFin : P U + P (A \ U) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top P U, measure_ne_top P (A \ U)⟩
    have hAtoReal : (P A).toReal ≤ (P U).toReal + (P (A \ U)).toReal := by
      calc (P A).toReal ≤ (P U + P (A \ U)).toReal := ENNReal.toReal_mono hUnionFin hUnionEq
        _ = (P U).toReal + (P (A \ U)).toReal :=
            ENNReal.toReal_add (measure_ne_top P U) (measure_ne_top P (A \ U))
    have hUAle : (P U).toReal ≤ (P A).toReal :=
      ENNReal.toReal_mono (measure_ne_top P A) (measure_mono hUA)
    have habs : |(P U).toReal - (P A).toReal| = (P A).toReal - (P U).toReal := by
      rw [abs_of_nonpos (sub_nonpos.mpr hUAle)]
      ring
    have hsub : A \ U ⊆ A2 ∪ B1 := by
      intro ω hω
      rw [Set.mem_diff] at hω
      obtain ⟨hωA, hωU⟩ := hω
      rw [hmemA ω] at hωA
      rw [hmemU ω] at hωU
      rw [Set.mem_union]
      by_cases h2 : ω ∈ A2
      · exact Or.inl h2
      · right
        have hωA2 : ¬ (fmax J0 (F ω) ≤ t2) := by simpa [hA2] using h2
        have hJ0gt : t2 < fmax J0 (F ω) := not_le.mp hωA2
        have hUgt : t < fmax Finset.univ (F ω) := not_le.mp hωU
        have ht2t : t2 < t := lt_of_lt_of_le hJ0gt hωA
        have hBgt : t < fmax (Finset.univ \ J0) (F ω) := by
          rw [hfmax_max ω] at hUgt
          by_cases hle : fmax (Finset.univ \ J0) (F ω) ≤ t
          · exact absurd hUgt (not_lt.mpr (max_le hωA hle))
          · exact not_le.mp hle
        rw [hB1]
        exact lt_trans (lt_of_le_of_lt ht ht2t) hBgt
    have hPsub : P (A \ U) ≤ P (A2 ∪ B1) := measure_mono hsub
    have hPun : P (A2 ∪ B1) ≤ P A2 + P B1 := measure_union_le A2 B1
    have hfin : P A2 + P B1 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top P A2, measure_ne_top P B1⟩
    have h2le : (P (A \ U)).toReal ≤ (P A2).toReal + (P B1).toReal := by
      have hmono : (P (A \ U)).toReal ≤ (P A2 + P B1).toReal :=
        ENNReal.toReal_mono hfin (le_trans hPsub hPun)
      rw [ENNReal.toReal_add (measure_ne_top P A2) (measure_ne_top P B1)] at hmono
      exact hmono
    rw [habs]
    have h1 : (P A).toReal - (P U).toReal ≤ (P (A \ U)).toReal := by linarith [hAtoReal]
    calc (P A).toReal - (P U).toReal ≤ (P (A \ U)).toReal := h1
      _ ≤ (P A2).toReal + (P B1).toReal := h2le

  unfold dK
  apply Real.sSup_le
  · rintro x ⟨t, rfl⟩
    exact hleaf t
  · exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  /- @proof-region region.target-node.session.51538944f49689d8 end -/

end
end Statlib.Imported

