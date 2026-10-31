import ProverJobs.job_paper_d6348dc732d4474c900772ddadac1ef8.Vocabulary
import ProverJobs.job_paper_d6348dc732d4474c900772ddadac1ef8.ProvedNodes
import ProverJobs.job_paper_d6348dc732d4474c900772ddadac1ef8.Base

open MeasureTheory Filter Topology
open scoped Topology ENNReal
namespace Statlib.Imported

theorem paper_d6348dc732d4474c900772ddadac1ef8
    {Ω : Type*} [MeasurableSpace Ω]
    (Pinfty : Measure Ω) [IsProbabilityMeasure Pinfty]
    (Ωn : ℕ → Set Ω) (hΩn : ∀ n, MeasurableSet (Ωn n))
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, Measurable (Z n))
          (hΩnProb : Tendsto (fun n => Pinfty (Ωn n)) atTop (𝓝 (1 : ℝ≥0∞)))
          (hZconv : ∀ ε > 0,
            Tendsto (fun n => Pinfty {ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω})
              atTop (𝓝 (0 : ℝ≥0∞))) :
          ∀ ε > 0, Tendsto (fun n => Pinfty {ω | ε < |Z n ω|}) atTop (𝓝 (0 : ℝ≥0∞))
:= by
  /- @proof-region region.root.6ffa8e44daae begin -/
  intro ε hε
  have hsub : ∀ n, {ω | ε < |Z n ω|} ⊆
      {ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω} ∪ (Ωn n)ᶜ := by
    intro n ω hω
    by_cases hmem : ω ∈ Ωn n
    · left
      simpa [Set.indicator_of_mem hmem] using hω
    · right
      simpa using hmem
  have hbound : ∀ n, Pinfty {ω | ε < |Z n ω|} ≤
      Pinfty {ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω} + Pinfty ((Ωn n)ᶜ) := by
    intro n
    calc Pinfty {ω | ε < |Z n ω|}
        ≤ Pinfty ({ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω} ∪ (Ωn n)ᶜ) :=
          measure_mono (hsub n)
      _ ≤ Pinfty {ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω} + Pinfty ((Ωn n)ᶜ) :=
          measure_union_le _ _
  have hcompl : ∀ n, Pinfty ((Ωn n)ᶜ) = 1 - Pinfty (Ωn n) := by
    intro n
    rw [measure_compl (hΩn n) (measure_ne_top Pinfty (Ωn n))]
    simp
  have hC : Tendsto (fun n => Pinfty ((Ωn n)ᶜ)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hlt : (1 : ℝ≥0∞) - δ < 1 :=
      ENNReal.sub_lt_self (a := 1) (b := δ) (by simp) (by simp) hδ.ne'
    have hev : ∀ᶠ n in atTop, (1 : ℝ≥0∞) - δ < Pinfty (Ωn n) :=
      hΩnProb.eventually (Ioi_mem_nhds hlt)
    refine hev.mono fun n hn => ?_
    rw [hcompl n]
    refine le_trans (tsub_le_tsub_left (a := (1 : ℝ≥0∞) - δ) (b := Pinfty (Ωn n)) hn.le 1) ?_
    rw [tsub_le_iff_right]
    rcases le_total δ (1 : ℝ≥0∞) with h | h
    · exact le_of_eq (add_tsub_cancel_of_le h).symm
    · have hz : (1 : ℝ≥0∞) - δ = 0 := by
        have h0 : (1 : ℝ≥0∞) - δ ≤ 0 := by
          rw [tsub_le_iff_right]
          simpa using h
        exact le_antisymm h0 (zero_le _)
      rw [hz, add_zero]
      exact h
  have hsum : Tendsto (fun n => Pinfty {ω | ε < |Z n ω| * (Ωn n).indicator (fun _ => (1 : ℝ)) ω}
      + Pinfty ((Ωn n)ᶜ)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h := (hZconv ε hε).add hC
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le _) hbound
  /- @proof-region region.root.6ffa8e44daae end -/

end Statlib.Imported
