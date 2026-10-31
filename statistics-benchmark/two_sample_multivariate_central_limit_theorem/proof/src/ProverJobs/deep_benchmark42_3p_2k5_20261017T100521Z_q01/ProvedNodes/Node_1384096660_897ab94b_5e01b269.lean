import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q01.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

set_option autoImplicit false in
theorem statopia_math_node_1384096660_897ab94b : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (G : Ω → EuclideanSpace ℝ (Fin d))
    (cov : Matrix (Fin d) (Fin d) ℝ)
    (hG_meas : Measurable G)
    (hG_gaussian : IsGaussian (P.map G))
    (hG_mean : ∫ ω, G ω ∂P = 0)
    (hG_cov : ∀ j k : Fin d, ∫ ω, G ω j * G ω k ∂P = cov j k)
    (t : EuclideanSpace ℝ (Fin d)),
    (Integrable (fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ t x) ^ 2) (P.map G) ∧
        variance (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ t x) (P.map G) =
          ∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k) ∧
      charFun (P.map G) t =
        Complex.exp (-(1 / 2 : ℂ) * ↑(∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k)) := by
  /- @proof-region region.target-node.session.8fec160e55430c82 begin -/
  intro Ω _ P _ d hd G cov hG_meas hG_gaussian hG_mean hG_cov t
  haveI : IsGaussian (P.map G) := hG_gaussian
  have hIdInt : ∫ x : EuclideanSpace ℝ (Fin d), id x ∂(P.map G) = ∫ ω, G ω ∂P := by
    rw [integral_map hG_meas.aemeasurable measurable_id.aestronglyMeasurable]
    simp
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ t x) ^ 2) (P.map G) := by
    have hL : MemLp (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ t x) 2 (P.map G) := by
      have h := IsGaussian.memLp_dual (P.map G)
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) t) 2 (by norm_num)
      simpa using h
    exact (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).1 hL
  have hvar : variance (fun x : EuclideanSpace ℝ (Fin d) => inner ℝ t x) (P.map G) =
      ∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k := by
    have h1mem : MemLp (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) 1 (P.map G) :=
      IsGaussian.memLp_id (P.map G) 1 (by norm_num)
    have hIntId : Integrable (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (P.map G) :=
      memLp_one_iff_integrable.1 h1mem
    have hmean : ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ t x ∂(P.map G) = 0 := by
      have h1 : ∫ x : EuclideanSpace ℝ (Fin d), inner ℝ t x ∂(P.map G)
          = inner ℝ t (∫ x : EuclideanSpace ℝ (Fin d), id x ∂(P.map G)) := by
        simpa using ContinuousLinearMap.integral_comp_comm
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) t) hIntId
      rw [h1, hIdInt, hG_mean, inner_zero_right]
    have hval : ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ t x) ^ 2 ∂(P.map G) =
        ∑ j : Fin d, ∑ k : Fin d, t j * t k * cov j k := by
      have hcoord : ∀ i : Fin d, MemLp (fun z : EuclideanSpace ℝ (Fin d) => z i) 2 (P.map G) := by
        intro i
        have h := IsGaussian.memLp_dual (P.map G)
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
            ((EuclideanSpace.basisFun (Fin d) ℝ) i)) 2 (by norm_num)
        have h2 : MemLp (fun z : EuclideanSpace ℝ (Fin d) =>
            inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z) 2 (P.map G) := by
          simpa using h
        have hin : (fun z : EuclideanSpace ℝ (Fin d) =>
            inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) i) z) = fun z => z i := by
          funext z
          exact EuclideanSpace.basisFun_inner (Fin d) ℝ z i
        rw [hin] at h2
        exact h2
      have hcross : ∀ j k : Fin d,
          Integrable (fun z : EuclideanSpace ℝ (Fin d) => z j * z k) (P.map G) := by
        intro j k
        have h := MemLp.integrable_mul (hcoord j) (hcoord k)
        simpa using h
      have hmj : ∀ j : Fin d, Measurable fun z : EuclideanSpace ℝ (Fin d) => z j := by
        intro j
        have hin : (fun z : EuclideanSpace ℝ (Fin d) => z j)
            = fun z => inner ℝ ((EuclideanSpace.basisFun (Fin d) ℝ) j) z := by
          funext z
          exact (EuclideanSpace.basisFun_inner (Fin d) ℝ z j).symm
        rw [hin]
        exact (continuous_const.inner continuous_id).measurable
      have hpush : ∀ j k : Fin d,
          ∫ z : EuclideanSpace ℝ (Fin d), z j * z k ∂(P.map G) = cov j k := by
        intro j k
        rw [integral_map hG_meas.aemeasurable ((hmj j).mul (hmj k)).aestronglyMeasurable]
        exact hG_cov j k
      have hterm : ∀ j k : Fin d,
          Integrable (fun x : EuclideanSpace ℝ (Fin d) => (t j * t k) * (x j * x k))
            (P.map G) := by
        intro j k
        exact (hcross j k).const_mul (t j * t k)
      have hinner : ∀ x : EuclideanSpace ℝ (Fin d), inner ℝ t x = ∑ j : Fin d, t j * x j := by
        intro x
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, mul_comm]
      have hstep1 : ∫ x : EuclideanSpace ℝ (Fin d), (inner ℝ t x) ^ 2 ∂(P.map G)
          = ∫ x : EuclideanSpace ℝ (Fin d),
              ∑ j : Fin d, ∑ k : Fin d, (t j * t k) * (x j * x k) ∂(P.map G) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show inner ℝ t x ^ 2 = ∑ j : Fin d, ∑ k : Fin d, (t j * t k) * (x j * x k)
        rw [hinner x, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hstep2 : ∫ x : EuclideanSpace ℝ (Fin d),
            ∑ j : Fin d, ∑ k : Fin d, (t j * t k) * (x j * x k) ∂(P.map G)
          = ∑ j : Fin d, ∑ k : Fin d,
              t j * t k * ∫ z : EuclideanSpace ℝ (Fin d), z j * z k ∂(P.map G) := by
        have houter : ∫ x : EuclideanSpace ℝ (Fin d),
              ∑ j : Fin d, ∑ k : Fin d, (t j * t k) * (x j * x k) ∂(P.map G)
            = ∑ j : Fin d, ∫ x : EuclideanSpace ℝ (Fin d),
                ∑ k : Fin d, (t j * t k) * (x j * x k) ∂(P.map G) :=
          integral_finset_sum Finset.univ
            (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hterm j k))
        rw [houter]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finset_sum Finset.univ (fun k _ => hterm j k)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simpa [smul_eq_mul] using integral_smul (t j * t k)
          (fun a : EuclideanSpace ℝ (Fin d) => a.ofLp j * a.ofLp k) (μ := P.map G)
      rw [hstep1, hstep2]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hpush j k]
    rw [variance_eq_integral (X := fun x : EuclideanSpace ℝ (Fin d) => inner ℝ t x)
      ((continuous_const.inner continuous_id).measurable.aemeasurable), hmean]
    simpa using hval
  refine ⟨⟨hInt, hvar⟩, ?_⟩
  have hzero : ∫ x : EuclideanSpace ℝ (Fin d), id x ∂(P.map G) = 0 := by
    rw [hIdInt, hG_mean]
  have hsub : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) t) = t := by simp
  conv_lhs => rw [← hsub]
  rw [charFun_toDual_symm_eq_charFunDual]
  rw [IsGaussian.charFunDual_eq_of_integral_eq_zero (μ := P.map G) hzero]
  congr 1
  have hfe : (⇑(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) t)) =
      fun x : EuclideanSpace ℝ (Fin d) => inner ℝ t x := by
    funext x
    simp
  rw [hfe, hvar]
  ring
  /- @proof-region region.target-node.session.8fec160e55430c82 end -/
