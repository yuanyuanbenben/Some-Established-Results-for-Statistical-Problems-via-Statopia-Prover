import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q39.Base

open MeasureTheory ProbabilityTheory

theorem eventual_recovery_unique_frechet_mean_finite_space
    {Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]
    [Fintype 𝓧] [LinearOrder 𝓧] [MetricSpace 𝓧] [Nonempty 𝓧]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝓧)
    (hXmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (mu : 𝓧)
    (hunique : ∀ z, z ≠ mu →
      (∑ x, (P {ω | X 0 ω = x}).toReal * dist mu x ^ 2) <
        ∑ x, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2)
    (muHat : ℕ → Ω → 𝓧)
    (hmuHatmeas : ∀ n, Measurable (muHat n))
    (hmin : ∀ n, 1 ≤ n → ∀ ω z,
      (∑ i ∈ Finset.range n, dist (muHat n ω) (X i ω) ^ 2) ≤
        ∑ i ∈ Finset.range n, dist z (X i ω) ^ 2)
    (hsmallest : ∀ n, 1 ≤ n → ∀ ω z,
      (∑ i ∈ Finset.range n, dist z (X i ω) ^ 2) =
          ∑ i ∈ Finset.range n, dist (muHat n ω) (X i ω) ^ 2 →
        muHat n ω ≤ z) :
    P {ω | ∃ N ≥ 1, ∀ n ≥ N, muHat n ω = mu} = 1
:= by
  /- @proof-region region.root.a60e95a002aa begin -/
  classical
  have hP : P Set.univ = 1 := measure_univ
  set F : 𝓧 → ℝ := fun z => ∑ x, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2 with hF
  have hUniq : ∀ z : 𝓧, z ≠ mu → F mu < F z := by
    intro z hz
    simpa [hF] using hunique z hz
  set U : 𝓧 → 𝓧 → ℝ := fun x z => dist z x ^ 2 with hU
  by_cases hC : (Finset.univ.erase mu : Finset 𝓧).Nonempty
  · obtain ⟨hδpos, hδle⟩ := statopia_math_node_2868299895_3d47b682 F mu hUniq hC
    set D : ℝ := ∑ z : 𝓧, ∑ x : 𝓧, dist z x ^ 2 with hD
    have hUmeas : ∀ θ : 𝓧, Measurable fun x => U x θ := by
      intro θ
      have hc : Continuous fun x : 𝓧 => dist θ x :=
        continuous_const.dist continuous_id
      exact (hc.pow 2).measurable
    have hDnn : 0 ≤ D := by
      rw [hD]
      exact Finset.sum_nonneg (fun z _ => Finset.sum_nonneg (fun x _ => by positivity))
    have hle : ∀ (x θ : 𝓧), ‖U x θ‖ ≤ D := by
      intro x θ
      have hinner : dist θ x ^ 2 ≤ ∑ y : 𝓧, dist θ y ^ 2 :=
        Finset.single_le_sum (f := fun y : 𝓧 => dist θ y ^ 2)
          (fun y _ => by positivity) (Finset.mem_univ x)
      have houter : (∑ y : 𝓧, dist θ y ^ 2) ≤ D := by
        rw [hD]
        exact Finset.single_le_sum (f := fun z : 𝓧 => ∑ y : 𝓧, dist z y ^ 2)
          (fun z _ => Finset.sum_nonneg (fun y _ => by positivity)) (Finset.mem_univ θ)
      have h1 : (0 : ℝ) ≤ dist θ x ^ 2 := by positivity
      have hUx : U x θ = dist θ x ^ 2 := rfl
      rw [hUx, Real.norm_of_nonneg h1]
      exact le_trans hinner houter
    have hSL := Statlib.StatFoundation.Convergence.strong_law_sampleAverage_finset_ae
      (P := P) (X := X) (U := U) hXmeas
      (fun i j hij => hindep.indepFun hij) hident hUmeas
      (M := fun _ : 𝓧 => D) (MeasureTheory.integrable_const D) hle (fun _ => hDnn)
      (Finset.univ : Finset 𝓧)
    have hconv : ∀ᵐ ω ∂P,
        ∀ z : 𝓧, Filter.Tendsto
          (fun n : ℕ => (∑ i ∈ Finset.range n, dist z (X i ω) ^ 2) / (n : ℝ))
          Filter.atTop (nhds (F z)) := by
      filter_upwards [hSL] with ω hω
      intro z
      have hpop : Statlib.StatFoundation.Convergence.populationMean (P := P) X U z = F z := by
        have h := (statopia_math_node_3261694732_b3b125fe P X (hXmeas 0) z).1
        simpa [hF, hU] using h
      have hfun : (fun n : ℕ => Statlib.StatFoundation.Convergence.sampleAverage X U n ω z)
          = fun n : ℕ => (∑ i ∈ Finset.range n, dist z (X i ω) ^ 2) / (n : ℝ) := by
        funext n
        simp [Statlib.StatFoundation.Convergence.sampleAverage, hU]
      have hz := hω z (Finset.mem_univ z)
      rw [hpop, hfun] at hz
      exact hz
    have hEv : ∀ᵐ ω ∂P, ω ∈ {ω : Ω | ∃ N ≥ 1, ∀ n ≥ N, muHat n ω = mu} := by
      filter_upwards [hconv] with ω hω
      exact statopia_math_node_2199421144_3cbe5eb0 F mu
        ((Finset.univ.erase mu).inf' hC (fun z => F z - F mu)) hδpos hδle
        (fun n z => ∑ i ∈ Finset.range n, dist z (X i ω) ^ 2)
        (fun n => muHat n ω) (fun z => hω z) (fun n hn z => hmin n hn ω z)
    exact statopia_math_node_3148995752_04a8170e P hP _ hEv
  · have hall : ∀ z : 𝓧, z = mu := by
      intro z
      by_contra hz
      exact hC ⟨z, Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩⟩
    have hset : {ω : Ω | ∃ N ≥ 1, ∀ n ≥ N, muHat n ω = mu} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨1, le_rfl, fun n _ => hall (muHat n ω)⟩
    rw [hset]
    exact measure_univ
  /- @proof-region region.root.a60e95a002aa end -/
