import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Vocabulary
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.Base
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes.Node_1960594570_2408034e_38e7022d
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes.Node_763218555_b6110431_c7970084
import ProverJobs.job_paper_7aa885023a494b54a3d0f82a9b80e7b2.ProvedNodes.Node_83830977_efab7094_7e03b9ed



open MeasureTheory
open scoped ENNReal BigOperators
open Statlib.Imported

open MeasureTheory
open scoped ENNReal BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2961478954_435cb595 : ∀ (n : ℕ) (c θ : ℝ) (s : ℕ) (A : Fin s → Finset (Fin n))
    (hn : 0 < n) (hc : 0 < c) (hs : 1 ≤ s)
    (hA_nonempty : ∀ h : Fin s, (A h).Nonempty)
    (hA_disjoint : ∀ h h' : Fin s, h ≠ h' → Disjoint (A h) (A h'))
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (G : (h : Fin s) → ({i : Fin n // i ∈ A h} → ℝ) → ℝ≥0∞)
    (hG : ∀ h : Fin s, Measurable (G h)),
    ∫⁻ (X : Fin n → ℝ) in partitionEvent n c θ s A,
        (∏ h : Fin s, G h (fun i => X i.1))
      ∂(Measure.pi (fun _ : Fin n => P))
    ≤ ∏ h : Fin s,
        ∫⁻ (y : {i : Fin n // i ∈ A h} → ℝ) in
            (Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} =>
              Set.Icc (θ - c) (θ + c))),
          G h y
        ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := by
  /- @proof-region region.target-node.session.b2a96d5a4571bede begin -/
  intro n c θ s A hn hc hs hne hdisj P _ G hG
  classical
  have hWmeas : MeasurableSet (Set.Icc (θ - c) (θ + c)) := measurableSet_Icc
  have hUmem : ∀ (h : Fin s) (i : Fin n), i ∈ A h → i ∈ Finset.univ.biUnion A := by
    intro h i hi
    rw [Finset.mem_biUnion]
    exact ⟨h, Finset.mem_univ h, hi⟩
  have hboxmeas : ∀ h : Fin s,
      MeasurableSet (Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c))) := by
    intro h
    exact MeasurableSet.univ_pi (fun _ => hWmeas)
  have hBmeas : MeasurableSet {X : Fin n → ℝ | ∀ i : Fin n,
      (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)} := by
    have hEq : {X : Fin n → ℝ | ∀ i : Fin n,
        (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}
        = Set.univ.pi (fun i : Fin n =>
            if i ∈ Finset.univ.biUnion A then Set.Icc (θ - c) (θ + c)
            else (Set.Icc (θ - c) (θ + c))ᶜ) := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
      constructor
      · rintro h i
        by_cases hi : i ∈ Finset.univ.biUnion A
        · simp only [hi, if_true]
          exact (h i).mpr hi
        · simp only [hi, if_false, Set.mem_compl_iff]
          exact fun hc => absurd ((h i).mp hc) hi
      · rintro h i
        by_cases hi : i ∈ Finset.univ.biUnion A
        · have hh := h i
          simp only [hi, if_true] at hh
          exact ⟨fun _ => hi, fun _ => hh⟩
        · have hh := h i
          simp only [hi, if_false, Set.mem_compl_iff] at hh
          exact ⟨fun hc => absurd hc hh, fun hc => absurd hc hi⟩
    rw [hEq]
    apply MeasurableSet.univ_pi
    intro i
    by_cases hi : i ∈ Finset.univ.biUnion A
    · simp only [hi, if_true]; exact hWmeas
    · simp only [hi, if_false]; exact hWmeas.compl
  let F' : (h : Fin s) → ({i : Fin n // i ∈ A h} → ℝ) → ℝ≥0∞ :=
    fun h => (Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c))).indicator (G h)
  have hF'meas : ∀ h : Fin s, Measurable (F' h) := by
    intro h
    exact (hG h).indicator (hboxmeas h)
  have KEY : (∫⁻ (X : Fin n → ℝ), ∏ h : Fin s, F' h (fun i => X i.1)
        ∂(Measure.pi (fun _ : Fin n => P)))
      = ∏ h : Fin s, ∫⁻ y, F' h y ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := by
    exact statopia_math_node_83830977_efab7094 (n := n) (s := s) (A := A)
      (hdisj := hdisj) (P := P) (F := F') (hF := hF'meas)
  have step1 : (∫⁻ X in partitionEvent n c θ s A, ∏ h : Fin s, G h (fun i => X i.1)
        ∂(Measure.pi (fun _ : Fin n => P)))
      = ∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, G h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)) := by
    rw [statopia_math_node_763218555_b6110431 n c θ s A hc hs hne hdisj]
  have hpt : ∀ X ∈ {X : Fin n → ℝ | ∀ i : Fin n,
        (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
      (∏ h : Fin s, G h (fun i => X i.1)) = (∏ h : Fin s, F' h (fun i => X i.1)) := by
    intro X hX
    apply Finset.prod_congr rfl
    intro h _
    have hmem : (fun i : {i : Fin n // i ∈ A h} => X i.1) ∈
        Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c)) := by
      rw [Set.mem_univ_pi]
      intro i
      exact (hX i.1).mpr (hUmem h i.1 i.2)
    simp only [F']
    rw [Set.indicator_of_mem hmem]
  have step2 : (∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, G h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)))
      = ∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, F' h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)) := by
    have e1 : (∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
            ∏ h : Fin s, G h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)))
        = ∫⁻ X, ({X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}.indicator
              (fun X => ∏ h : Fin s, G h (fun i => X i.1))) X
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      simpa using (setLIntegral_indicator (μ := Measure.pi (fun _ : Fin n => P))
        (s := {X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)})
        (t := Set.univ) hBmeas (fun X => ∏ h : Fin s, G h (fun i => X i.1))).symm
    have e2 : (∫⁻ X, ({X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}.indicator
              (fun X => ∏ h : Fin s, G h (fun i => X i.1))) X
            ∂(Measure.pi (fun _ : Fin n => P)))
        = ∫⁻ X, ({X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}.indicator
              (fun X => ∏ h : Fin s, F' h (fun i => X i.1))) X
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      apply lintegral_congr
      intro X
      by_cases hXB : X ∈ {X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}
      · rw [Set.indicator_of_mem hXB, Set.indicator_of_mem hXB]
        exact hpt X hXB
      · rw [Set.indicator_of_notMem hXB, Set.indicator_of_notMem hXB]
    have e3 : (∫⁻ X, ({X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)}.indicator
              (fun X => ∏ h : Fin s, F' h (fun i => X i.1))) X
            ∂(Measure.pi (fun _ : Fin n => P)))
        = ∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
            ∏ h : Fin s, F' h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)) := by
      simpa using (setLIntegral_indicator (μ := Measure.pi (fun _ : Fin n => P))
        (s := {X : Fin n → ℝ | ∀ i : Fin n,
              (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)})
        (t := Set.univ) hBmeas (fun X => ∏ h : Fin s, F' h (fun i => X i.1)))
    rw [e1, e2, e3]
  have step3 : (∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, F' h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)))
      ≤ ∫⁻ (X : Fin n → ℝ), ∏ h : Fin s, F' h (fun i => X i.1)
          ∂(Measure.pi (fun _ : Fin n => P)) :=
    setLIntegral_le_lintegral _ _
  have step4 : (∏ h : Fin s, ∫⁻ y, F' h y
          ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)))
      = ∏ h : Fin s,
          ∫⁻ y in Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c)),
            G h y ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := by
    apply Finset.prod_congr rfl
    intro h _
    have hlem := setLIntegral_indicator
      (μ := Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P))
      (s := Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c)))
      (t := Set.univ) (hboxmeas h) (G h)
    simp only [Measure.restrict_univ, Set.inter_univ] at hlem
    exact hlem
  calc (∫⁻ X in partitionEvent n c θ s A, ∏ h : Fin s, G h (fun i => X i.1)
        ∂(Measure.pi (fun _ : Fin n => P)))
      = ∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, G h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)) := step1
    _ = ∫⁻ X in {X : Fin n → ℝ | ∀ i : Fin n,
            (X i ∈ Set.Icc (θ - c) (θ + c) ↔ i ∈ Finset.univ.biUnion A)},
          ∏ h : Fin s, F' h (fun i => X i.1) ∂(Measure.pi (fun _ : Fin n => P)) := step2
    _ ≤ ∫⁻ (X : Fin n → ℝ), ∏ h : Fin s, F' h (fun i => X i.1)
          ∂(Measure.pi (fun _ : Fin n => P)) := step3
    _ = ∏ h : Fin s, ∫⁻ y, F' h y ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := KEY
    _ = ∏ h : Fin s,
          ∫⁻ y in Set.univ.pi (fun _ : {i : Fin n // i ∈ A h} => Set.Icc (θ - c) (θ + c)),
            G h y ∂(Measure.pi (fun _ : {i : Fin n // i ∈ A h} => P)) := step4
  /- @proof-region region.target-node.session.b2a96d5a4571bede end -/

end Statlib.Imported
