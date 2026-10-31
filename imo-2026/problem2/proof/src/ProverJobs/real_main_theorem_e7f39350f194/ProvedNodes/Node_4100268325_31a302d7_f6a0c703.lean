import ProverJobs.real_main_theorem_e7f39350f194.Vocabulary
import ProverJobs.real_main_theorem_e7f39350f194.Base

open EuclideanGeometry

open EuclideanGeometry

set_option autoImplicit false in
theorem statopia_math_node_4100268325_31a302d7 : ∀ (A B C W : Plane)
    (hcol : ¬ Collinear ℝ ({A, B, C} : Set Plane)),
    ∃ s t : ℝ, W - A = s • (B - A) + t • (C - A) := by
  /- @proof-region region.target-node.session.e8f210c7b6eda757 begin -/
  intro A B C W hcol
  have hdim : Module.finrank ℝ Plane = 2 := by
    simp [Plane, EuclideanSpace]
  set p : Submodule ℝ Plane := Submodule.span ℝ ({B - A, C - A} : Set Plane) with hp
  have hXA : ∀ X ∈ ({A, B, C} : Set Plane), X - A ∈ p := by
    intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · rw [sub_self]; exact Submodule.zero_mem p
    · rw [hp]; exact Submodule.subset_span (by simp)
    · rw [hp]; exact Submodule.subset_span (by simp)
  have hq_le_p : vectorSpan ℝ ({A, B, C} : Set Plane) ≤ p := by
    unfold vectorSpan
    apply Submodule.span_le.mpr
    rintro x hx
    rw [Set.mem_vsub] at hx
    obtain ⟨X, hX, Y, hY, hxy⟩ := hx
    rw [← hxy]
    have h1 : X - A ∈ p := hXA X hX
    have h2 : Y - A ∈ p := hXA Y hY
    have h3 : X -ᵥ Y = (X - A) - (Y - A) := by rw [vsub_eq_sub]; abel
    rw [h3]
    exact Submodule.sub_mem p h1 h2
  have hcol' : ¬ (Module.rank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) ≤ 1) := hcol
  have h1r : (1 : Cardinal) < Module.rank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) :=
    not_le.mp hcol'
  have hbridge : (↑(Module.finrank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane))) : Cardinal)
      = Module.rank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) :=
    Module.finrank_eq_rank ℝ _
  have h1fin : (1 : ℕ) < Module.finrank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) := by
    have hc : ((1 : ℕ) : Cardinal)
        < ((Module.finrank ℝ ↥(vectorSpan ℝ ({A, B, C} : Set Plane)) : ℕ) : Cardinal) := by
      rw [hbridge]
      simpa using h1r
    exact Nat.cast_lt.mp hc
  have hmono := Submodule.finrank_mono hq_le_p
  have h2 : 2 ≤ Module.finrank ℝ ↥p := by omega
  have hle : Module.finrank ℝ ↥p ≤ 2 := by
    have hfl := Submodule.finrank_le p
    omega
  have hp_top : p = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have hWp : W - A ∈ p := by rw [hp_top]; exact Submodule.mem_top
  rw [hp] at hWp
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hWp
  exact ⟨s, t, hst.symm⟩
  /- @proof-region region.target-node.session.e8f210c7b6eda757 end -/
