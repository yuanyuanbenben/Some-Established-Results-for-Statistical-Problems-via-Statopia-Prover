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
theorem statopia_math_node_3257560511_130c2ed0 : ∀ {Θ X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Θ]
    (μ : Measure X)
    (k : Θ → X → ℝ) (hk_nonneg : ∀ (θ : Θ) (x : X), 0 ≤ k θ x)
    (hk_meas : Measurable (Function.uncurry k))
    (hk_int : ∀ θ : Θ, ∫⁻ x, ENNReal.ofReal (k θ x) ∂μ = 1)
    (P : ProbabilityMeasure X)
    (U : Set (ProbabilityMeasure X)) (hU : U ∈ 𝓝 P)
    (t : ℕ) (ht : 2 ≤ t)
    (theta0 : Θ)
    (hsep : ∀ s : ℕ, 1 ≤ s → s < t → U ∩ Gset μ k s = ∅),
    ∃ (r : ℕ) (ψ : Fin r → BoundedContinuousFunction X ℝ) (ε M c : ℝ),
      1 ≤ r ∧ 0 < ε ∧
      M = (⨆ j : Fin r, ⨆ x : X, |(ψ j : X → ℝ) x|) ∧
      0 < M ∧
      c = ε ^ 2 / (8 * M ^ 2) ∧ 0 < c ∧
      (∀ Q : ProbabilityMeasure X,
        (∀ j : Fin r,
          |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure
            - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε) → Q ∈ U) ∧
      (∀ (s : ℕ), 1 ≤ s → s < t → ∀ Q : ProbabilityMeasure X,
        Q ∈ Gset μ k s →
          ¬ (∀ j : Fin r,
            |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure
              - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε)) := by
  /- @proof-region region.target-node.session.64d9ae89f20dd9d5 begin -/
  intro Θ X _ _ _ _ μ k hk_nonneg hk_meas hk_int P U hU t ht theta0 hsep
  classical
  haveI hXne : Nonempty X := by
    rcases isEmpty_or_nonempty X with hX | hX
    · exfalso
      haveI := hX
      have h0 : (P : Measure X) Set.univ = 1 := measure_univ
      have h2 : (Set.univ : Set X) = ∅ := Set.univ_eq_empty_iff.mpr hX
      rw [h2, measure_empty] at h0
      exact zero_ne_one h0
    · exact hX
  have hchar : ∀ F : Filter (ProbabilityMeasure X),
      F ≤ 𝓝 P ↔ ∀ (f : BoundedContinuousFunction X ℝ),
        F ≤ comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
          (𝓝 (∫ ω, f ω ∂(P : Measure X))) := by
    intro F
    have hkey := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (F := F) (μs := id) (μ := P)
    constructor
    · intro hF f
      have hid : Tendsto id F (𝓝 P) := by simpa [Filter.Tendsto] using hF
      exact Filter.map_le_iff_le_comap.mp (hkey.mp hid f)
    · intro hF
      have hid : Tendsto id F (𝓝 P) := hkey.mpr (fun f => Filter.map_le_iff_le_comap.mpr (hF f))
      simpa [Filter.Tendsto] using hid
  have hEq : 𝓝 P = ⨅ (f : BoundedContinuousFunction X ℝ),
      comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
        (𝓝 (∫ ω, f ω ∂(P : Measure X))) :=
    le_antisymm (le_iInf fun f => (hchar (𝓝 P)).mp le_rfl f) ((hchar _).mpr fun f => iInf_le _ f)
  have hUm : U ∈ ⨅ (f : BoundedContinuousFunction X ℝ),
      comap (fun Q : ProbabilityMeasure X => ∫ ω, f ω ∂(Q : Measure X))
        (𝓝 (∫ ω, f ω ∂(P : Measure X))) := by
    rw [← hEq]
    exact hU
  rw [Filter.mem_iInf] at hUm
  obtain ⟨I, hIfin, V, hV, hUV⟩ := hUm
  have hstep : ∀ i : ↑I, ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ProbabilityMeasure X,
      |∫ ω, (i : BoundedContinuousFunction X ℝ) ω ∂(Q : Measure X)
        - ∫ ω, (i : BoundedContinuousFunction X ℝ) ω ∂(P : Measure X)| < δ → Q ∈ V i := by
    intro i
    obtain ⟨W, hWmem, hWV⟩ := Filter.mem_comap.mp (hV i)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hWmem
    refine ⟨δ, hδ, fun Q hQ => hWV ?_⟩
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    exact hQ
  choose δ hδpos hδdef using hstep
  haveI : Fintype ↑I := hIfin.fintype
  obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ i : ↑I, ε ≤ δ i := by
    rcases isEmpty_or_nonempty (↑I) with h | h
    · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image (Finset.univ : Finset ↑I) δ Finset.univ_nonempty
      exact ⟨δ i0, hδpos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  set G : Option ↑I → BoundedContinuousFunction X ℝ := fun o =>
    match o with
    | none => 1
    | some i => (i : BoundedContinuousFunction X ℝ) with hG
  let ψ : Fin (Fintype.card (Option ↑I)) → BoundedContinuousFunction X ℝ :=
    fun j => G ((Fintype.equivFin (Option ↑I)).symm j)
  have hVsub : ∀ Q : ProbabilityMeasure X,
      (∀ j : Fin (Fintype.card (Option ↑I)),
        |∫ x, (ψ j : X → ℝ) x ∂Q.toMeasure - ∫ x, (ψ j : X → ℝ) x ∂P.toMeasure| < ε) →
        Q ∈ U := by
    intro Q hQ
    have hmem : ∀ i : ↑I, Q ∈ V i := by
      intro i
      refine hδdef i Q (lt_of_lt_of_le ?_ (hεle i))
      have h2 := hQ ((Fintype.equivFin (Option ↑I)) (some i))
      simpa [ψ, hG] using h2
    have hmemU : Q ∈ ⋂ i : ↑I, V i := Set.mem_iInter.mpr hmem
    rw [← hUV] at hmemU
    exact hmemU
  have hr : 1 ≤ Fintype.card (Option ↑I) := by
    have hc : Fintype.card (Option ↑I) = Fintype.card ↑I + 1 := Fintype.card_option
    omega
  have hMpos : 0 < ⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x| := by
    obtain ⟨x0⟩ := hXne
    set j0 : Fin (Fintype.card (Option ↑I)) := Fintype.equivFin (Option ↑I) none with hj0
    have hψ0b : ψ j0 = (1 : BoundedContinuousFunction X ℝ) := by
      simp [ψ, hj0, hG]
    have hψ0 : ((ψ j0 : BoundedContinuousFunction X ℝ) : X → ℝ) = fun _ => (1 : ℝ) := by
      funext x
      rw [hψ0b]
      simp
    have hbddIn : BddAbove (Set.range fun x : X => |(ψ j0 : X → ℝ) x|) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      rw [hψ0]
      simp
    have hbddOut : BddAbove (Set.range fun j : Fin (Fintype.card (Option ↑I)) =>
        ⨆ x : X, |(ψ j : X → ℝ) x|) :=
      (Set.finite_range (fun j : Fin (Fintype.card (Option ↑I)) =>
        ⨆ x : X, |(ψ j : X → ℝ) x|)).bddAbove
    have h1 : (1 : ℝ) ≤ ⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x| := by
      refine le_trans ?_ (le_ciSup hbddOut j0)
      calc (1 : ℝ) = |(ψ j0 : X → ℝ) x0| := by rw [hψ0]; simp
        _ ≤ ⨆ x : X, |(ψ j0 : X → ℝ) x| := le_ciSup hbddIn x0
    exact lt_of_lt_of_le one_pos h1
  have hcpos : 0 < ε ^ 2 /
      (8 * (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|) ^ 2) :=
    div_pos (pow_pos hεpos 2) (mul_pos (by norm_num) (pow_pos hMpos 2))
  refine ⟨Fintype.card (Option ↑I), ψ, ε,
    (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|),
    ε ^ 2 / (8 * (⨆ j : Fin (Fintype.card (Option ↑I)), ⨆ x : X, |(ψ j : X → ℝ) x|) ^ 2),
    hr, hεpos, rfl, hMpos, rfl, hcpos, hVsub, ?_⟩
  intro s hs hst Q hQ hV
  have hUQ : Q ∈ U := hVsub Q hV
  have hmem : Q ∈ U ∩ Gset μ k s := ⟨hUQ, hQ⟩
  rw [hsep s hs hst] at hmem
  exact hmem
  /- @proof-region region.target-node.session.64d9ae89f20dd9d5 end -/

end Statlib.Imported
