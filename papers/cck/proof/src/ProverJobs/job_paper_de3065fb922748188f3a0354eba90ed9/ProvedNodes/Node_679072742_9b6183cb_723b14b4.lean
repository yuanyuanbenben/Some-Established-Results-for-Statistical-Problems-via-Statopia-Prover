import Statlib.StatFoundation.Statistics.Asymptotic.ScoreCLT
import Statlib.StatFoundation.Convergence.Resampling.GaussianMaxComparison
import Statlib.StatFoundation.Convergence.AnalysisTools.GaussianMaxAnticoncentration
import Statlib.StatFoundation.Statistics.Asymptotic.LAN
import Statlib.StatFoundation.Convergence.AnalysisTools.SmoothMax
import Statlib.StatFoundation.Convergence.AnalysisTools.Nazarov
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Vocabulary
import ProverJobs.job_paper_de3065fb922748188f3a0354eba90ed9.Base

namespace PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9

open _root_.PaperProofTasks.job_paper_de3065fb922748188f3a0354eba90ed9.Statlib.Imported
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Statlib.Imported

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

set_option autoImplicit false in
theorem statopia_math_node_679072742_9b6183cb : ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p) (u : Ω → Fin p → ℝ) (ms : Fin p → ℝ)
    (hL2 : ∀ j : Fin p, MemLp (fun ω => u ω j) 2 μ)
    (hUnit : ∀ j : Fin p, ∫ ω, (u ω j) ^ 2 ∂μ = 1),
    ∃ S : Finset (Fin p), S.Nonempty ∧
      (∀ j ∈ S, ∀ k ∈ S, j ≠ k → ∫ ω, u ω j * u ω k ∂μ < 1) ∧
      (μ {ω | (⨆ j : ↥S, (u ω (j : Fin p) + ms (j : Fin p))) =
            (⨆ j : Fin p, (u ω j + ms j))} = 1) ∧
      (μ {ω | (⨆ j : ↥S, u ω (j : Fin p)) = (⨆ j : Fin p, u ω j)} = 1) := by
  /- @proof-region region.target-node.session.c58b77a1f63415b1 begin -/
  intro Ω _ μ _ p hp u ms hL2 hUnit
  classical
  haveI hpne : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have measure_one_of_ae : ∀ {P : Ω → Prop}, (∀ᵐ ω ∂μ, P ω) → μ {ω | P ω} = 1 := by
    intro P hP
    have hcompl : μ ({ω | P ω}ᶜ) = 0 := by
      have h := MeasureTheory.ae_iff.mp hP
      have hset : {ω | ¬ P ω} = {ω | P ω}ᶜ := by ext ω; simp
      rwa [hset] at h
    have hcongr : μ {ω | P ω} = μ (Set.univ) :=
      measure_congr ((MeasureTheory.ae_eq_univ).mpr hcompl)
    rwa [measure_univ] at hcongr
  -- bridge: subtype-supremum equals Finset.sup'
  have hbridge : ∀ (S : Finset (Fin p)) (hS : S.Nonempty) (F : Fin p → ℝ),
      (⨆ j : ↥S, F (j : Fin p)) = S.sup' hS F := by
    intro S hS F
    haveI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    refine le_antisymm ?_ ?_
    · apply ciSup_le
      intro j
      exact Finset.le_sup' F j.2
    · rw [Finset.sup'_le_iff hS F]
      intro b hb
      exact le_ciSup (Finite.bddAbove_range (fun j : ↥S => F (j : Fin p))) ⟨b, hb⟩
  haveI hunivne : Nonempty ↥(Finset.univ : Finset (Fin p)) :=
    ⟨⟨⟨0, by omega⟩, Finset.mem_univ _⟩⟩
  let Good : Finset (Fin p) → Prop := fun T =>
    T.Nonempty ∧
    (∀ᵐ ω ∂μ, (⨆ j : ↥T, (u ω (j : Fin p) + ms (j : Fin p))) = (⨆ j : Fin p, (u ω j + ms j))) ∧
    (∀ᵐ ω ∂μ, (⨆ j : ↥T, u ω (j : Fin p)) = (⨆ j : Fin p, u ω j))
  have hshift_univ : ∀ ω, (⨆ j : ↥(Finset.univ : Finset (Fin p)), (u ω (j : Fin p) + ms (j : Fin p)))
      = (⨆ j : Fin p, (u ω j + ms j)) := by
    intro ω
    apply le_antisymm
    · apply ciSup_le
      intro j
      exact le_ciSup (Finite.bddAbove_range (fun j : Fin p => u ω j + ms j)) (j : Fin p)
    · apply ciSup_le
      intro j
      exact le_ciSup (Finite.bddAbove_range (fun k : ↥(Finset.univ : Finset (Fin p)) => u ω (k : Fin p) + ms (k : Fin p))) ⟨j, Finset.mem_univ j⟩
  have hplain_univ : ∀ ω, (⨆ j : ↥(Finset.univ : Finset (Fin p)), u ω (j : Fin p))
      = (⨆ j : Fin p, u ω j) := by
    intro ω
    apply le_antisymm
    · apply ciSup_le
      intro j
      exact le_ciSup (Finite.bddAbove_range (fun j : Fin p => u ω j)) (j : Fin p)
    · apply ciSup_le
      intro j
      exact le_ciSup (Finite.bddAbove_range (fun k : ↥(Finset.univ : Finset (Fin p)) => u ω (k : Fin p))) ⟨j, Finset.mem_univ j⟩
  have hGood_univ : Good Finset.univ := by
    refine ⟨⟨(⟨0, by omega⟩ : Fin p), Finset.mem_univ _⟩, ?_, ?_⟩
    · exact Filter.Eventually.of_forall hshift_univ
    · exact Filter.Eventually.of_forall hplain_univ
  have hgoodset_ne : (Finset.univ.powerset.filter Good).Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun x _ => Finset.mem_univ x, hGood_univ⟩
  obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image (Finset.univ.powerset.filter Good) Finset.card hgoodset_ne
  have hTgood : Good T := (Finset.mem_filter.mp hTmem).2
  have hTne : T.Nonempty := hTgood.1
  have hT_shift := hTgood.2.1
  have hT_plain := hTgood.2.2
  have key : ∀ (a b : Fin p), a ∈ T → b ∈ T → a ≠ b →
      (fun ω => u ω a) =ᵐ[μ] (fun ω => u ω b) → ms a ≤ ms b → False := by
    intro a b ha hb hab huv hm
    have hbT' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    have hT'ne : (T.erase a).Nonempty := ⟨b, hbT'⟩
    have supeq : ∀ (F : Ω → Fin p → ℝ), (∀ᵐ ω ∂μ, F ω a ≤ F ω b) →
        (∀ᵐ ω ∂μ, (T.erase a).sup' hT'ne (fun c => F ω c) = T.sup' hTne (fun c => F ω c)) := by
      intro F hdom
      refine hdom.mono (fun ω hω => ?_)
      apply le_antisymm
      · rw [Finset.sup'_le_iff hT'ne (fun c => F ω c)]
        intro c hc
        exact Finset.le_sup' (fun c => F ω c) ((Finset.erase_subset a T) hc)
      · rw [Finset.sup'_le_iff hTne (fun c => F ω c)]
        intro c hc
        by_cases hca : c = a
        · show F ω c ≤ (T.erase a).sup' hT'ne (fun c => F ω c)
          rw [hca]
          exact le_trans hω (Finset.le_sup' (fun c => F ω c) hbT')
        · exact Finset.le_sup' (fun c => F ω c) (Finset.mem_erase.mpr ⟨hca, hc⟩)
    have dom_shift : ∀ᵐ ω ∂μ, u ω a + ms a ≤ u ω b + ms b := by
      refine huv.mono (fun ω hω => ?_)
      have hω' : u ω a = u ω b := by simpa using hω
      rw [hω']; linarith
    have dom_plain : ∀ᵐ ω ∂μ, u ω a ≤ u ω b := huv.mono (fun ω hω => le_of_eq hω)
    have hshift_ae := supeq (fun ω c => u ω c + ms c) dom_shift
    have hplain_ae := supeq (fun ω c => u ω c) dom_plain
    have hsup_shift : ∀ᵐ ω ∂μ, (⨆ j : ↥(T.erase a), (u ω (j : Fin p) + ms (j : Fin p)))
        = (⨆ j : ↥T, (u ω (j : Fin p) + ms (j : Fin p))) := by
      filter_upwards [hshift_ae] with ω h1
      calc (⨆ j : ↥(T.erase a), (u ω (j : Fin p) + ms (j : Fin p)))
          = (T.erase a).sup' hT'ne (fun c => u ω c + ms c) := hbridge (T.erase a) hT'ne (fun c => u ω c + ms c)
        _ = T.sup' hTne (fun c => u ω c + ms c) := h1
        _ = (⨆ j : ↥T, (u ω (j : Fin p) + ms (j : Fin p))) := (hbridge T hTne (fun c => u ω c + ms c)).symm
    have hsup_plain : ∀ᵐ ω ∂μ, (⨆ j : ↥(T.erase a), u ω (j : Fin p))
        = (⨆ j : ↥T, u ω (j : Fin p)) := by
      filter_upwards [hplain_ae] with ω h1
      calc (⨆ j : ↥(T.erase a), u ω (j : Fin p))
          = (T.erase a).sup' hT'ne (fun c => u ω c) := hbridge (T.erase a) hT'ne (fun c => u ω c)
        _ = T.sup' hTne (fun c => u ω c) := h1
        _ = (⨆ j : ↥T, u ω (j : Fin p)) := (hbridge T hTne (fun c => u ω c)).symm
    have hgshift : ∀ᵐ ω ∂μ, (⨆ j : ↥(T.erase a), (u ω (j : Fin p) + ms (j : Fin p))) = (⨆ j : Fin p, (u ω j + ms j)) := by
      filter_upwards [hsup_shift, hT_shift] with ω h1 h2
      rw [h1]; exact h2
    have hgplain : ∀ᵐ ω ∂μ, (⨆ j : ↥(T.erase a), u ω (j : Fin p)) = (⨆ j : Fin p, u ω j) := by
      filter_upwards [hsup_plain, hT_plain] with ω h1 h2
      rw [h1]; exact h2
    have hGood' : Good (T.erase a) := ⟨hT'ne, hgshift, hgplain⟩
    have hmem' : T.erase a ∈ Finset.univ.powerset.filter Good := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun x _ => Finset.mem_univ x, hGood'⟩
    have hle := hTmin (T.erase a) hmem'
    have hcard : (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem ha
    have hpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega
  have hnopair : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → ¬ (fun ω => u ω j) =ᵐ[μ] (fun ω => u ω k) := by
    intro j hj k hk hjk huv
    rcases le_total (ms j) (ms k) with hle | hle
    · exact key j k hj hk hjk huv hle
    · exact key k j hk hj (Ne.symm hjk) huv.symm hle
  refine ⟨T, hTne, ?_, measure_one_of_ae hT_shift, measure_one_of_ae hT_plain⟩
  intro j hj k hk hjk
  have hj2 : Integrable (fun ω => (u ω j)^2) μ := MemLp.integrable_sq (hL2 j)
  have hk2 : Integrable (fun ω => (u ω k)^2) μ := MemLp.integrable_sq (hL2 k)
  have hjk_int : Integrable (fun ω => u ω j * u ω k) μ := MemLp.integrable_mul (hL2 j) (hL2 k)
  have hdiff2 : Integrable (fun ω => (u ω j - u ω k)^2) μ :=
    MemLp.integrable_sq ((hL2 j).sub (hL2 k))
  have hkey : ∫ ω, (u ω j - u ω k)^2 ∂μ = 2 - 2 * ∫ ω, u ω j * u ω k ∂μ := by
    have hf_sum : Integrable (fun ω => (u ω j)^2 + (u ω k)^2) μ := hj2.add hk2
    have hg_2 : Integrable (fun ω => 2 * (u ω j * u ω k)) μ := hjk_int.const_mul 2
    have hpt : (fun ω => (u ω j - u ω k)^2) = (fun ω => (u ω j)^2 + (u ω k)^2 - 2 * (u ω j * u ω k)) := by
      funext ω; ring
    rw [hpt, integral_sub hf_sum hg_2, integral_add hj2 hk2, integral_const_mul, hUnit j, hUnit k]
    ring
  have hle1 : ∫ ω, u ω j * u ω k ∂μ ≤ 1 := by
    have hnn : 0 ≤ ∫ ω, (u ω j - u ω k)^2 ∂μ := integral_nonneg (fun ω => by positivity)
    rw [hkey] at hnn
    linarith
  refine lt_of_le_of_ne hle1 ?_
  intro heq
  have hzero : ∫ ω, (u ω j - u ω k)^2 ∂μ = 0 := by rw [hkey, heq]; ring
  have hae : (fun ω => (u ω j - u ω k)^2) =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hdiff2).mp hzero
  have huv : (fun ω => u ω j) =ᵐ[μ] (fun ω => u ω k) := by
    filter_upwards [hae] with ω hω
    have h2 : (u ω j - u ω k) * (u ω j - u ω k) = 0 := by rw [← pow_two]; exact hω
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  exact hnopair j hj k hk hjk huv
  /- @proof-region region.target-node.session.c58b77a1f63415b1 end -/

end Statlib.Imported

