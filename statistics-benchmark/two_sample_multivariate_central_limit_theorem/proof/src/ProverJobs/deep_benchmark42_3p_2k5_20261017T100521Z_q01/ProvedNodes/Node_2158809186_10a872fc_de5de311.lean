import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_2158809186_10a872fc : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (V W : Ω → EuclideanSpace ℝ (Fin d))
    (hV_meas : Measurable V)
    (hW_meas : Measurable W)
    (hVW_ident : IdentDistrib V W P P)
    (hV_second : Integrable (fun ω => ‖V ω‖ ^ 2) P),
    (Integrable V P ∧
      Integrable W P ∧
      (∫ ω, W ω ∂P = ∫ ω, V ω ∂P) ∧
      Integrable (fun ω => ‖W ω‖ ^ 2) P ∧
      (∀ j k : Fin d,
        ∫ ω, ((W ω).ofLp j - (∫ ω, V ω ∂P).ofLp j) *
            ((W ω).ofLp k - (∫ ω, V ω ∂P).ofLp k) ∂P =
          ∫ ω, ((V ω).ofLp j - (∫ ω, V ω ∂P).ofLp j) *
            ((V ω).ofLp k - (∫ ω, V ω ∂P).ofLp k) ∂P) ∧
      (∀ cov : Matrix (Fin d) (Fin d) ℝ,
        (∀ j k : Fin d,
          ∫ ω, ((V ω).ofLp j - (∫ ω, V ω ∂P).ofLp j) *
              ((V ω).ofLp k - (∫ ω, V ω ∂P).ofLp k) ∂P = cov j k) →
        ∀ j k : Fin d,
          ∫ ω, ((W ω).ofLp j - (∫ ω, W ω ∂P).ofLp j) *
              ((W ω).ofLp k - (∫ ω, W ω ∂P).ofLp k) ∂P = cov j k)) := by
  /- @proof-region region.target-node.session.67b68cd6473fae12 begin -/
  intro Ω _ P _ d _ V W hV_meas hW_meas hVW_ident hV_second
  have hV_int : Integrable V P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hV_second) hV_meas.aestronglyMeasurable ?_
    filter_upwards with ω
    show ‖V ω‖ ≤ 1 + ‖V ω‖ ^ 2
    nlinarith [sq_nonneg (‖V ω‖ - 1 / 2)]
  have hW_int : Integrable W P := hVW_ident.integrable_iff.mp hV_int
  have hmean : ∫ ω, W ω ∂P = ∫ ω, V ω ∂P := hVW_ident.integral_eq.symm
  have hcoord : ∀ i : Fin d, Measurable fun x : EuclideanSpace ℝ (Fin d) => x.ofLp i := fun i =>
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))
  have hsq_meas : Measurable fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2 :=
    (continuous_norm.pow 2).measurable
  have hW_second : Integrable (fun ω => ‖W ω‖ ^ 2) P :=
    (hVW_ident.comp hsq_meas).integrable_iff.mp hV_second
  have hcov_eq : ∀ j k : Fin d,
      ∫ ω, ((W ω).ofLp j - (∫ ω, V ω ∂P).ofLp j) *
          ((W ω).ofLp k - (∫ ω, V ω ∂P).ofLp k) ∂P =
        ∫ ω, ((V ω).ofLp j - (∫ ω, V ω ∂P).ofLp j) *
          ((V ω).ofLp k - (∫ ω, V ω ∂P).ofLp k) ∂P := by
    intro j k
    have hφ : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
        (x.ofLp j - (∫ ω, V ω ∂P).ofLp j) * (x.ofLp k - (∫ ω, V ω ∂P).ofLp k) := by
      have hj : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
          x.ofLp j - (∫ ω, V ω ∂P).ofLp j := (hcoord j).sub measurable_const
      have hk : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
          x.ofLp k - (∫ ω, V ω ∂P).ofLp k := (hcoord k).sub measurable_const
      exact hj.mul hk
    exact (hVW_ident.comp hφ).integral_eq.symm
  refine ⟨hV_int, hW_int, hmean, hW_second, hcov_eq, ?_⟩
  intro cov hcov j k
  simp only [hmean]
  exact (hcov_eq j k).trans (hcov j k)

  /- @proof-region region.target-node.session.67b68cd6473fae12 end -/
