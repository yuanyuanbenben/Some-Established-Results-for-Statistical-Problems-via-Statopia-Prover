import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Vocabulary
import ProverJobs.job_paper_b0cf39bbf6c845c9a6b30a5db43f8efa.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
open Statlib.Imported
open Statlib.Imported.DPMModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal MeasureTheory Topology BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3905332965_3d9d9dd7 : ∀ {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [StandardBorelSpace Θ],
    Measurable (fun P : ProbabilityMeasure Θ =>
        (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))
      ∧ (∀ P : ProbabilityMeasure Θ,
        ((Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure)))
          Set.univ = 1) := by
  /- @proof-region region.target-node.session.8eb6aaca45d7f3fe begin -/
  intro Θ _ _ _
  have hν1 : ∀ P : ProbabilityMeasure Θ,
      (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) Set.univ = 1 := by
    intro P
    have hpi : ((↑(∅ : Finset ℕ) : Set ℕ).pi (fun _ => (Set.univ : Set Θ))) = Set.univ := by
      ext y
      simp
    rw [← hpi]
    rw [Measure.infinitePi_pi (μ := fun _ : ℕ => P.toMeasure) (s := (∅ : Finset ℕ))
      (t := fun _ => (Set.univ : Set Θ)) (fun i _ => MeasurableSet.univ)]
    simp
  have hG1 : ∀ P : ProbabilityMeasure Θ,
      ((Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))) Set.univ = 1 := by
    intro P
    haveI : IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) := ⟨hν1 P⟩
    rw [Measure.dirac_prod (x := P)]
    rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ]
    simp [hν1 P]
  refine ⟨?_, hG1⟩
  classical
  have hcoe : Measurable fun P : ProbabilityMeasure Θ => P.toMeasure := measurable_subtype_coe
  have hdirc : Measurable fun P : ProbabilityMeasure Θ => Measure.dirac P := Measure.measurable_dirac
  haveI hHprob : ∀ P : ProbabilityMeasure Θ,
      IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) := fun P => ⟨hν1 P⟩
  haveI hGprob : ∀ P : ProbabilityMeasure Θ,
      IsProbabilityMeasure ((Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))) :=
    fun P => ⟨hG1 P⟩
  set Cyl : Set (Set (ℕ → Θ)) :=
    {t | ∃ (s : Finset ℕ) (B : ℕ → Set Θ), (∀ i, MeasurableSet (B i)) ∧ t = (↑s : Set ℕ).pi B} with hCyl
  set S : Set (Set (ProbabilityMeasure Θ × (ℕ → Θ))) :=
    Set.image2 (fun a b => a ×ˢ b) {a : Set (ProbabilityMeasure Θ) | MeasurableSet a} Cyl with hS
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S := S) ?_ ?_ ?_
  · rw [hS]
    have hCylGen : MeasurableSpace.generateFrom Cyl = (inferInstance : MeasurableSpace (ℕ → Θ)) := by
      refine le_antisymm ?_ ?_
      · refine MeasurableSpace.generateFrom_le ?_
        rintro t ⟨F, B, hB, rfl⟩
        exact MeasurableSet.pi F.finite_toSet.countable (fun i _ => hB i)
      · have hproj : ∀ i : ℕ, MeasurableSpace.comap (fun f : ℕ → Θ => f i)
            (inferInstance : MeasurableSpace Θ) ≤ MeasurableSpace.generateFrom Cyl := by
          intro i
          rw [MeasurableSpace.comap_eq_generateFrom]
          refine MeasurableSpace.generateFrom_le ?_
          rintro t ⟨A, hA, rfl⟩
          have hcyl : (fun f : ℕ → Θ => f i) ⁻¹' A =
              (↑({i} : Finset ℕ) : Set ℕ).pi (fun j => if j = i then A else Set.univ) := by
            ext f
            simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_singleton]
            constructor
            · rintro hf j hj
              simpa [hj] using hf
            · intro hf
              simpa using hf i rfl
          rw [hcyl]
          have hmem : (↑({i} : Finset ℕ) : Set ℕ).pi
              (fun j => if j = i then A else Set.univ) ∈ Cyl :=
            ⟨{i}, fun j => if j = i then A else Set.univ,
              fun j => by by_cases h : j = i <;> simp [h, hA], rfl⟩
          exact (MeasurableSpace.giGenerateFrom.gc.le_iff_le.mp le_rfl) hmem
        show (⨆ i : ℕ, MeasurableSpace.comap (fun f : ℕ → Θ => f i)
            (inferInstance : MeasurableSpace Θ)) ≤ MeasurableSpace.generateFrom Cyl
        exact iSup_le hproj
    refine (generateFrom_eq_prod (C := {a : Set (ProbabilityMeasure Θ) | MeasurableSet a})
      (D := Cyl) (MeasurableSpace.giGenerateFrom.l_u_eq
        (inferInstance : MeasurableSpace (ProbabilityMeasure Θ))) hCylGen
      isCountablySpanning_measurableSet ?_).symm
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      exact ⟨∅, fun _ => Set.univ, fun _ => MeasurableSet.univ, by ext y; simp⟩
    · ext y
      simp
  · intro u hu v hv _

    rw [hS] at hu hv
    obtain ⟨s₁, hs₁, t₁, ht₁, rfl⟩ := hu
    obtain ⟨s₂, hs₂, t₂, ht₂, rfl⟩ := hv
    rw [hCyl] at ht₁ ht₂
    obtain ⟨F₁, B₁, hB₁, rfl⟩ := ht₁
    obtain ⟨F₂, B₂, hB₂, rfl⟩ := ht₂
    have hs₁' : MeasurableSet s₁ := hs₁
    have hs₂' : MeasurableSet s₂ := hs₂
    refine ⟨s₁ ∩ s₂, hs₁'.inter hs₂',
      (↑(F₁ ∪ F₂) : Set ℕ).pi (fun i =>
        (if i ∈ F₁ then B₁ i else Set.univ) ∩ (if i ∈ F₂ then B₂ i else Set.univ)),
      ⟨F₁ ∪ F₂, fun i =>
        (if i ∈ F₁ then B₁ i else Set.univ) ∩ (if i ∈ F₂ then B₂ i else Set.univ),
        fun i => by by_cases h1 : i ∈ F₁ <;> by_cases h2 : i ∈ F₂ <;>
          simp [h1, h2, hB₁ i, hB₂ i], rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨hy1, hpi⟩
      have k1 : y.2 ∈ (↑F₁ : Set ℕ).pi B₁ := by
        intro i hi
        have hiF : i ∈ F₁ := by simpa using hi
        have hmem : i ∈ (↑(F₁ ∪ F₂) : Set ℕ) := by
          simp only [Finset.mem_coe, Finset.mem_union]
          exact Or.inl hiF
        have h := hpi i hmem
        rw [Set.mem_inter_iff] at h
        rw [if_pos hiF] at h
        exact h.1
      have k2 : y.2 ∈ (↑F₂ : Set ℕ).pi B₂ := by
        intro i hi
        have hiF : i ∈ F₂ := by simpa using hi
        have hmem : i ∈ (↑(F₁ ∪ F₂) : Set ℕ) := by
          simp only [Finset.mem_coe, Finset.mem_union]
          exact Or.inr hiF
        have h := hpi i hmem
        rw [Set.mem_inter_iff] at h
        rw [if_pos hiF] at h
        exact h.2
      exact ⟨⟨hy1.1, k1⟩, hy1.2, k2⟩
    · rintro ⟨⟨hy1, h1⟩, hy2, h2⟩
      refine ⟨⟨hy1, hy2⟩, ?_⟩
      intro i hi
      rw [Set.mem_inter_iff]
      constructor
      · by_cases hF : i ∈ F₁
        · rw [if_pos hF]
          exact h1 i (by simpa using hF)
        · rw [if_neg hF]
          trivial
      · by_cases hF : i ∈ F₂
        · rw [if_pos hF]
          exact h2 i (by simpa using hF)
        · rw [if_neg hF]
          trivial


  · intro u hu
    rw [hS] at hu
    obtain ⟨s₁, hs₁, t₂, ht₂, rfl⟩ := hu
    rw [hCyl] at ht₂
    obtain ⟨F, B, hB, rfl⟩ := ht₂
    have hfun : (fun P : ProbabilityMeasure Θ =>
        (Measure.dirac P).prod (Measure.infinitePi (fun _ : ℕ => P.toMeasure))
          (s₁ ×ˢ (↑F : Set ℕ).pi B))
        = fun P => (Measure.dirac P) s₁ *
            (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) ((↑F : Set ℕ).pi B) := by
      funext P
      exact Measure.prod_prod s₁ ((↑F : Set ℕ).pi B)
    rw [hfun]
    refine Measurable.mul ((Measure.measurable_measure.mp hdirc) s₁ hs₁) ?_
    have hprod : (fun P : ProbabilityMeasure Θ =>
        (Measure.infinitePi (fun _ : ℕ => P.toMeasure)) ((↑F : Set ℕ).pi B))
        = fun P => ∏ i ∈ F, P.toMeasure (B i) := by
      funext P
      exact Measure.infinitePi_pi (μ := fun _ : ℕ => P.toMeasure) (fun i _ => hB i)
    rw [hprod]
    have hpt : ∀ i ∈ F, Measurable fun P : ProbabilityMeasure Θ => P.toMeasure (B i) :=
      fun i _ => (Measure.measurable_measure.mp hcoe) (B i) (hB i)
    exact Finset.measurable_prod F hpt



  /- @proof-region region.target-node.session.8eb6aaca45d7f3fe end -/

end Statlib.Imported
