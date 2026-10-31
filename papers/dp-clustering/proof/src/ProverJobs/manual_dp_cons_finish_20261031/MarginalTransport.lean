import Mathlib
import Mathlib
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
open MeasureTheory ProbabilityTheory Filter Topology
noncomputable section
namespace ManualDPCons

lemma integral_fiber_marginals {I J X Θ : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Θ]
    (mu : I → Measure X) [∀ i, IsFiniteMeasure (mu i)]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (owner : I → J) (k : Θ → X → ℝ) (hk : Measurable (Function.uncurry k))
    (M : ℝ) (hM : 0 ≤ M) (hk0 : ∀ theta x, 0 ≤ k theta x)
    (hkM : ∀ theta x, k theta x ≤ M) :
    (∫ x : I → X, ∏ j : J, (∫ theta : Θ,
      ∏ i ∈ Finset.univ.filter (fun i => owner i = j), k theta (x i) ∂Q) ∂Measure.pi mu) =
    ∏ j : J, ∫ theta : Θ,
      ∏ i ∈ Finset.univ.filter (fun i => owner i = j), (∫ x, k theta x ∂mu i) ∂Q := by
  classical
  let F : (J → Θ) → (I → X) → ℝ := fun z x => ∏ i : I, k (z (owner i)) (x i)
  have hgroup : ∀ (z : J → Θ) (x : I → X),
      (∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => owner i = j), k (z j) (x i)) = F z x := by
    intro z x
    calc (∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => owner i = j), k (z j) (x i))
        = ∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => owner i = j), k (z (owner i)) (x i) := by
          apply Finset.prod_congr rfl
          intro j hj
          apply Finset.prod_congr rfl
          intro i hi
          have hh := (Finset.mem_filter.mp hi).2
          rw [hh]
      _ = F z x := Finset.prod_fiberwise _ owner _
  have hjoint : Measurable (Function.uncurry F) := by
    apply Finset.measurable_prod
    intro i hi
    have hp : Measurable (fun zx : (J → Θ) × (I → X) => (zx.1 (owner i), zx.2 i)) :=
      ((measurable_pi_apply (owner i)).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    exact hk.comp hp
  have hFint : Integrable (Function.uncurry F) ((Measure.pi (fun _ : J => Q)).prod (Measure.pi mu)) := by
    apply Integrable.mono' (integrable_const (M ^ Fintype.card I)) hjoint.aestronglyMeasurable
    filter_upwards [] with zx
    change ‖∏ i : I, k (zx.1 (owner i)) (zx.2 i)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i hi => hk0 _ _))]
    calc F zx.1 zx.2 ≤ ∏ i : I, M := Finset.prod_le_prod (fun i hi => hk0 _ _) (fun i hi => hkM _ _)
      _ = M ^ Fintype.card I := by simp
  have hx : ∀ x : I → X,
      (∏ j : J, ∫ theta : Θ, ∏ i ∈ Finset.univ.filter (fun i => owner i = j), k theta (x i) ∂Q) =
        ∫ z : J → Θ, F z x ∂Measure.pi (fun _ : J => Q) := by
    intro x
    rw [← integral_fintype_prod_eq_prod]
    exact integral_congr_ae (Eventually.of_forall (fun z => hgroup z x))
  have hz : ∀ z : J → Θ,
      (∫ x : I → X, F z x ∂Measure.pi mu) = ∏ i : I, ∫ x, k (z (owner i)) x ∂mu i := by
    intro z
    exact integral_fintype_prod_eq_prod _
  have hgroup2 : ∀ z : J → Θ,
      (∏ i : I, ∫ x, k (z (owner i)) x ∂mu i) =
        ∏ j : J, ∏ i ∈ Finset.univ.filter (fun i => owner i = j), (∫ x, k (z j) x ∂mu i) := by
    intro z
    rw [← Finset.prod_fiberwise Finset.univ owner (fun i => ∫ x, k (z (owner i)) x ∂mu i)]
    apply Finset.prod_congr rfl
    intro j hj
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [hx]
  rw [← integral_integral_swap hFint]
  simp_rw [hz, hgroup2]
  exact integral_fintype_prod_eq_prod (μ := fun _ : J => Q)
    (fun j theta => ∏ i ∈ Finset.univ.filter (fun i => owner i = j), ∫ x, k theta x ∂mu i)


/-- Bounded kernels make each entire partition marginal genuinely integrable. -/
lemma partition_product_integrable {I X Θ : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Θ]
    (mu : I → Measure X) [∀ i, IsFiniteMeasure (mu i)]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (k : Θ → X → ℝ) (hk : Measurable (Function.uncurry k))
    (M : ℝ) (hM : 0 ≤ M) (hk0 : ∀ theta x, 0 ≤ k theta x)
    (hkM : ∀ theta x, k theta x ≤ M)
    (A : Finset (Finset I)) :
    Integrable (fun x : I → X => ∏ B ∈ A, (∫ theta, ∏ i ∈ B, k theta (x i) ∂Q)) (Measure.pi mu) := by
  classical
  have hmeas : ∀ B : Finset I, StronglyMeasurable (fun x : I → X => ∫ theta, ∏ i ∈ B, k theta (x i) ∂Q) := by
    intro B
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod B
    intro i hi
    have hp : Measurable (fun xt : (I → X) × Θ => (xt.2, xt.1 i)) :=
      measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
    exact hk.comp hp
  have hnonneg : ∀ (B : Finset I) (x : I → X), 0 ≤ ∫ theta, ∏ i ∈ B, k theta (x i) ∂Q :=
    fun B x => integral_nonneg (fun theta => Finset.prod_nonneg (fun i hi => hk0 _ _))
  have hbound : ∀ (B : Finset I) (x : I → X),
      (∫ theta, ∏ i ∈ B, k theta (x i) ∂Q) ≤ M ^ B.card := by
    intro B x
    calc (∫ theta, ∏ i ∈ B, k theta (x i) ∂Q) ≤ ∫ theta : Θ, M ^ B.card ∂Q :=
          integral_mono_of_nonneg (Eventually.of_forall (fun theta => Finset.prod_nonneg (fun i hi => hk0 _ _)))
            (integrable_const _) (Eventually.of_forall (fun theta => by
              calc (∏ i ∈ B, k theta (x i)) ≤ ∏ i ∈ B, M :=
                    Finset.prod_le_prod (fun i hi => hk0 _ _) (fun i hi => hkM _ _)
                _ = M ^ B.card := by simp))
      _ = M ^ B.card := by simp
  have hsm : StronglyMeasurable (fun x : I → X => ∏ B ∈ A, ∫ theta, ∏ i ∈ B, k theta (x i) ∂Q) := by
    exact Finset.stronglyMeasurable_fun_prod A (fun B hB => hmeas B)
  apply Integrable.mono'
    (integrable_const (∏ B ∈ A, M ^ B.card) : Integrable (fun _ : I → X => ∏ B ∈ A, M ^ B.card) (Measure.pi mu))
    hsm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun B hB => hnonneg B x))]
  exact Finset.prod_le_prod (fun B hB => hnonneg B x) (fun B hB => hbound B x)

/-- Exact Tonelli/Fubini transport for every partition, including crossing blocks. -/
lemma integral_partition_marginals {n : ℕ} {X Θ : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ]
    (mu : Fin n → Measure X) [∀ i, IsFiniteMeasure (mu i)]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (k : Θ → X → ℝ) (hk : Measurable (Function.uncurry k))
    (M : ℝ) (hM : 0 ≤ M) (hk0 : ∀ theta x, 0 ≤ k theta x)
    (hkM : ∀ theta x, k theta x ≤ M)
    (A : Finset (Finset (Fin n)))
    (hdisj : ∀ B ∈ A, ∀ B' ∈ A, B ≠ B' → Disjoint B B')
    (hcover : ∀ i : Fin n, ∃ B ∈ A, i ∈ B) :
    (∫ x : Fin n → X, ∏ B ∈ A, (∫ theta, ∏ i ∈ B, k theta (x i) ∂Q) ∂Measure.pi mu) =
      ∏ B ∈ A, ∫ theta, ∏ i ∈ B, (∫ x, k theta x ∂mu i) ∂Q := by
  classical
  let owner : Fin n → A := fun i => ⟨(hcover i).choose, (hcover i).choose_spec.1⟩
  have hown : ∀ i : Fin n, i ∈ (owner i).val := fun i => (hcover i).choose_spec.2
  have hfiber : ∀ B : A, Finset.univ.filter (fun i => owner i = B) = B.val := by
    intro B
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have hh := hown i
      rw [hi] at hh
      exact hh
    · intro hi
      apply Subtype.ext
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj (owner i).val (owner i).property B.val B.property hne) (hown i) hi
  have hh := integral_fiber_marginals mu Q owner k hk M hM hk0 hkM
  simp only [hfiber] at hh
  convert hh using 1
  · apply integral_congr_ae
    exact Eventually.of_forall (fun x => (Finset.prod_coe_sort A
      (fun B => ∫ theta, ∏ i ∈ B, k theta (x i) ∂Q)).symm)
  · exact (Finset.prod_coe_sort A
      (fun B => ∫ theta, ∏ i ∈ B, (∫ x, k theta x ∂mu i) ∂Q)).symm

open Statlib.Imported in
lemma window_partition_integral {t n : ℕ} (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (theta : Fin t → ℝ) (lab : Fin n → Fin t)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ z, g z ≤ M)
    (hq : Measurable q0) (hq0 : ∀ z, 0 ≤ q0 z) (hQ : IsProbabilityMeasure (dpQ0 q0))
    (A : Finset (Finset (Fin n))) (s : ℕ) (hA : dpIsPartition A s) :
    let G := fun l z => ∫ x in Set.Icc (theta l - c) (theta l + c), g (x - z) ∂volume
    (∫ x : Fin n → ℝ, ∏ B ∈ A, (((B.card - 1).factorial : ℝ) * dpMargLik g q0 x B)
      ∂Measure.pi (fun i => volume.restrict (Set.Icc (theta (lab i) - c) (theta (lab i) + c)))) =
    ∏ B ∈ A, (((B.card - 1).factorial : ℝ) *
      ∫ z, (∏ l : Fin t, (G l z) ^ (B.filter (fun i => lab i = l)).card) * q0 z ∂volume) := by
  classical
  intro G
  let mu : Fin n → Measure ℝ := fun i => volume.restrict (Set.Icc (theta (lab i) - c) (theta (lab i) + c))
  haveI : ∀ i, IsFiniteMeasure (mu i) := fun i => isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  haveI := hQ
  have hkernel : Measurable (Function.uncurry (fun z x : ℝ => g (x-z))) :=
    hg.comp (measurable_snd.sub measurable_fst)
  have hQint : ∀ f : ℝ → ℝ, (∫ z, f z ∂dpQ0 q0) = ∫ z, f z * q0 z ∂volume := by
    intro f
    rw [dpQ0, integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
      (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by simp [ENNReal.toReal_ofReal (hq0 z), smul_eq_mul, mul_comm])
  have hGprod : ∀ B : Finset (Fin n), ∀ z : ℝ,
      (∏ i ∈ B, ∫ x, g (x-z) ∂mu i) = ∏ l : Fin t, (G l z) ^ (B.filter (fun i => lab i = l)).card := by
    intro B z
    rw [← Finset.prod_fiberwise B lab (fun i => ∫ x, g (x-z) ∂mu i)]
    apply Finset.prod_congr rfl
    intro l hl
    calc (∏ i ∈ B.filter (fun i => lab i = l), ∫ x, g (x-z) ∂mu i)
        = ∏ i ∈ B.filter (fun i => lab i = l), G l z := by
          apply Finset.prod_congr rfl
          intro i hi
          dsimp only [mu]
          rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  have hh := integral_partition_marginals mu (dpQ0 q0) (fun z x : ℝ => g (x-z)) hkernel
    M hM (fun z x => hg0 _) (fun z x => hgM _) A hA.2.2.1 hA.2.2.2
  simp_rw [hQint] at hh
  simp_rw [hGprod] at hh
  simp_rw [Finset.prod_mul_distrib, integral_const_mul]
  exact congrArg (fun z : ℝ => (∏ B ∈ A, ((B.card-1).factorial : ℝ)) * z) hh

#print axioms integral_fiber_marginals
#print axioms integral_partition_marginals
#print axioms window_partition_integral
end ManualDPCons
