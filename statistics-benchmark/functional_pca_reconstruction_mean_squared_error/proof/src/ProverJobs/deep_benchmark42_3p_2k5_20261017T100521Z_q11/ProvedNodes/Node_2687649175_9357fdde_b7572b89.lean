import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_2638301687_3687fe5f_29d4ac7c
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_2870967343_8e3526df_c0be3033
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q11.ProvedNodes.Node_714068217_742cf005_d2274bfe



open MeasureTheory

open MeasureTheory

set_option autoImplicit false in
theorem statopia_math_node_2687649175_9357fdde : ∀ {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (C : H →L[ℝ] H)
    (phi : ℕ → H) (lambda : ℕ → ℝ)
    (horth : Orthonormal ℝ phi)
    (heigen : ∀ k : ℕ, C (phi k) = lambda k • phi k)
    (hC : ∀ h : H,
      C h =
        ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) h) •
          (X ω - ∫ z, X z ∂P) ∂P)
    (hlambda : ∀ k : ℕ,
      lambda k = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P)
    (r : ℕ),
    Integrable
      (fun ω => ‖(X ω - ∫ z, X z ∂P) -
        ∑ k ∈ Finset.range r,
          (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k‖ ^ 2) P ∧
    ∫ ω, ‖(X ω - ∫ z, X z ∂P) -
        ∑ k ∈ Finset.range r,
          (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k‖ ^ 2 ∂P
      = (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ 2 ∂P)
        - ∑ k ∈ Finset.range r, lambda k := by
  /- @proof-region region.target-node.session.285a67e342f23557 begin -/
  intro Ω H _ _ _ _ P _ X hXmeas hXsq C phi lambda horth heigen hC hlambda r
  have hYint : Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2) P :=
    (statopia_math_node_714068217_742cf005 P X hXmeas hXsq).2.2.1
  have hdep3 : ∀ k : ℕ,
      AEStronglyMeasurable (fun ω => inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) P ∧
      Integrable (fun ω => (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) P ∧
      lambda k = ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P ∧
      0 ≤ lambda k :=
    fun k => statopia_math_node_2870967343_8e3526df P X hXmeas hXsq C phi lambda horth heigen hC k
  have hpt : ∀ ω : Ω,
      ‖(X ω - ∫ z, X z ∂P) - ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k‖ ^ 2
        = ‖X ω - ∫ z, X z ∂P‖ ^ 2 - ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 := by
    intro ω
    obtain ⟨_, hres, _, _, _, _⟩ :=
      statopia_math_node_2638301687_3687fe5f phi horth r (X ω - ∫ z, X z ∂P)
    simpa using hres
  have hsum_int :
      Integrable (fun ω => ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) P :=
    integrable_finset_sum (Finset.range r) (fun k _ => (hdep3 k).2.1)
  have hRHS_int :
      Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ 2 -
        ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) P :=
    hYint.sub hsum_int
  have hLHS_int :
      Integrable (fun ω => ‖(X ω - ∫ z, X z ∂P) -
        ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k‖ ^ 2) P := by
    refine hRHS_int.congr ?_
    filter_upwards with ω
    exact (hpt ω).symm
  refine ⟨hLHS_int, ?_⟩
  have hint_eq :
      (∫ ω, ‖(X ω - ∫ z, X z ∂P) -
          ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) • phi k‖ ^ 2 ∂P)
        = ∫ ω, (‖X ω - ∫ z, X z ∂P‖ ^ 2 -
            ∑ k ∈ Finset.range r, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    exact hpt ω
  rw [hint_eq, integral_sub hYint hsum_int,
    integral_finset_sum (Finset.range r) (fun k _ => (hdep3 k).2.1)]
  have hsum_eq :
      (∑ k ∈ Finset.range r, ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) (phi k)) ^ 2 ∂P)
        = ∑ k ∈ Finset.range r, lambda k :=
    Finset.sum_congr rfl (fun k _ => (hlambda k).symm)
  simp only [hsum_eq]
  /- @proof-region region.target-node.session.285a67e342f23557 end -/
