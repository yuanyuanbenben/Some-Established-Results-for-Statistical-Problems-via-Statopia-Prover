import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_1950684925_391067fc_66d07481
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.ProvedNodes.Node_2950655660_fcc1ce66_13207d78


open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_2755252338_b98666b0 : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ)
    (X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (m n : ℕ → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ j, Measurable (Y j))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hXY_indep : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P)
    (hX_ident : ∀ i, P.map (X i) = P.map (X 0))
    (hY_ident : ∀ j, P.map (Y j) = P.map (Y 0))
    (hXY_ident : P.map (Y 0) = P.map (X 0))
    (hm_pos : ∀ r, 0 < m r)
    (hn_pos : ∀ r, 0 < n r),
    ∀ (r : ℕ) (t : EuclideanSpace ℝ (Fin d)),
      charFun (P.map (fun ω =>
        Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
            ((n r : ℝ)⁻¹ • ∑ j ∈ Finset.range (n r), Y j ω)))) t =
        (charFun (P.map (X 0))
            ((Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) /
              (m r : ℝ)) • t)) ^ (m r) *
          (charFun (P.map (X 0))
            ((-(Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) /
              (n r : ℝ))) • t)) ^ (n r) := by
  /- @proof-region region.target-node.session.313e19aecbe1bb02 begin -/
  intro Ω _ P _ d X Y m n hX_meas hY_meas hX_indep hY_indep hXY_indep hX_ident hY_ident
    hXY_ident hm_pos hn_pos r t
  set c : ℝ := Real.sqrt (((m r : ℝ) * (n r : ℝ)) / ((m r : ℝ) + (n r : ℝ))) with hc
  set A : Ω → EuclideanSpace ℝ (Fin d) :=
    fun ω => (c / (m r : ℝ)) • ∑ i ∈ Finset.range (m r), X i ω with hAdef
  set B : Ω → EuclideanSpace ℝ (Fin d) :=
    fun ω => ((-c) / (n r : ℝ)) • ∑ j ∈ Finset.range (n r), Y j ω with hBdef
  have hT_eq : (fun ω => c • (((m r : ℝ)⁻¹ • ∑ i ∈ Finset.range (m r), X i ω) -
      ((n r : ℝ)⁻¹ • ∑ j ∈ Finset.range (n r), Y j ω))) = fun ω => A ω + B ω := by
    funext ω
    simp only [hAdef, hBdef, smul_add, smul_smul, smul_neg, div_eq_mul_inv, neg_mul, neg_smul,
      sub_eq_add_neg]
  have hA_meas : Measurable A := by
    rw [hAdef]
    exact (Finset.measurable_sum (Finset.range (m r)) (fun i _ => hX_meas i)).const_smul
      (c / (m r : ℝ))
  have hB_meas : Measurable B := by
    rw [hBdef]
    exact (Finset.measurable_sum (Finset.range (n r)) (fun j _ => hY_meas j)).const_smul
      ((-c) / (n r : ℝ))
  have hAB : IndepFun A B P := by
    have hu : Measurable (fun f : ℕ → EuclideanSpace ℝ (Fin d) =>
        (c / (m r : ℝ)) • ∑ i ∈ Finset.range (m r), f i) :=
      (Finset.measurable_sum (Finset.range (m r)) (fun i _ => measurable_pi_apply i)).const_smul
        (c / (m r : ℝ))
    have hv : Measurable (fun g : ℕ → EuclideanSpace ℝ (Fin d) =>
        ((-c) / (n r : ℝ)) • ∑ j ∈ Finset.range (n r), g j) :=
      (Finset.measurable_sum (Finset.range (n r)) (fun j _ => measurable_pi_apply j)).const_smul
        ((-c) / (n r : ℝ))
    have h := hXY_indep.comp hu hv
    simpa only [Function.comp_apply, hAdef, hBdef] using h
  have hsum : charFun (P.map (fun ω => A ω + B ω)) t =
      charFun (P.map A) t * charFun (P.map B) t :=
    statopia_math_node_1950684925_391067fc P d A B hA_meas hB_meas hAB t
  have hXblock : charFun (P.map A) t =
      (charFun (P.map (X 0)) ((c / (m r : ℝ)) • t)) ^ (m r) := by
    have h := statopia_math_node_2950655660_fcc1ce66 P d X hX_meas hX_indep hX_ident
      (m r) (hm_pos r) c t
    rw [← hAdef] at h
    exact h
  have hYblock : charFun (P.map B) t =
      (charFun (P.map (X 0)) ((-(c / (n r : ℝ))) • t)) ^ (n r) := by
    have h := statopia_math_node_2950655660_fcc1ce66 P d Y hY_meas hY_indep hY_ident
      (n r) (hn_pos r) (-c) t
    rw [← hBdef] at h
    rw [hXY_ident] at h
    simp only [neg_div] at h
    exact h
  have hmain : charFun (P.map (fun ω => A ω + B ω)) t =
      (charFun (P.map (X 0)) ((c / (m r : ℝ)) • t)) ^ (m r) *
        (charFun (P.map (X 0)) ((-(c / (n r : ℝ))) • t)) ^ (n r) := by
    rw [hsum, hXblock, hYblock]
  rw [hT_eq]
  exact hmain
  /- @proof-region region.target-node.session.313e19aecbe1bb02 end -/
