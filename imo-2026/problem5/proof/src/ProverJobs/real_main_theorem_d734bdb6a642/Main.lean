import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes
import ProverJobs.real_main_theorem_d734bdb6a642.Base

theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c
:= by
  /- @proof-region region.root.af0ceeaeb2c8 begin -/
  constructor
  · intro hf
    refine ⟨(f ⟨1, by norm_num⟩ : ℝ) - 1, ?_, ?_⟩
    · have h1 := statopia_math_node_1648340497_660d8830 f hf ⟨1, by norm_num⟩
      have h1c : ((⟨1, by norm_num⟩ : PositiveReal) : ℝ) = 1 := rfl
      linarith
    · intro x
      have hc := statopia_math_node_4115935916_c5a90aa0 f hf x ⟨1, by norm_num⟩
      have h1c : ((⟨1, by norm_num⟩ : PositiveReal) : ℝ) = 1 := rfl
      linarith
  · rintro ⟨c, hc, hf⟩
    intro x y
    have hA : (0 : ℝ) ≤ (x : ℝ) := le_of_lt x.2
    have hB : (0 : ℝ) ≤ (f y : ℝ) := le_of_lt (f y).2
    have hkey := statopia_math_node_93132176_513605de (x : ℝ) (f y : ℝ) hA hB
    have hfy : (f y : ℝ) = (y : ℝ) + c := hf y
    have hfx : (f x : ℝ) = (x : ℝ) + c := hf x
    have h1 : ((f x : ℝ) + (y : ℝ)) / 2 = ((x : ℝ) + (f y : ℝ)) / 2 := by
      rw [hfx, hfy]; ring
    constructor
    · rw [h1]; exact hkey.2
    · rw [h1]; exact hkey.1
  /- @proof-region region.root.af0ceeaeb2c8 end -/
