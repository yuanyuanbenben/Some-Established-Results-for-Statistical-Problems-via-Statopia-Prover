import ProverJobs.paper_fresh_20261028t224543381z_eills.Vocabulary
import ProverJobs.paper_fresh_20261028t224543381z_eills.ProvedNodes
import ProverJobs.paper_fresh_20261028t224543381z_eills.Base

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory
open StrongConvexityMain

theorem Theorem_4_2_Strong_Convexity_with_respect_to_beta_star_thm_global_strong_convexity_main
    (p : ℕ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : ι → Measure (Eucl p × ℝ))
    (βstar : Eucl p) (S_star : Finset (Fin p))
    (hS_star : ∀ j : Fin p, j ∈ S_star ↔ βstar j ≠ 0)
    (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hLaw : ∀ e : ι, InTrueLawSet βstar S_star σ2 (μ e))
    
    
    
    
    
    
    
    
    
    
    
    (hY2 : ∀ e : ι, MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e))
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n)
    (Z : ι → Fin n → Ω → Eucl p × ℝ)
    (hZ_meas : ∀ (e : ι) (i : Fin n), Measurable (Z e i))
    (hZ_law : ∀ (e : ι) (i : Fin n), Measure.map (Z e i) P = μ e)
    (hZ_indep : iIndepFun (fun q : ι × Fin n => Z q.1 q.2) P)
    (hCenter : ∀ e : ι, ∫ z, z.1 ∂(μ e) = 0)
    (hCenter_int : ∀ e : ι, Integrable (fun z : Eucl p × ℝ => z.1) (μ e))
    (ω : ι → ℝ) (hω_sum : ∑ e, ω e = 1) (hω_pos : ∀ e, 0 < ω e)
    (hω_unif : ∀ e : ι, ω e = (Fintype.card ι : ℝ)⁻¹)
    (betaLocal : ι → Finset (Fin p) → Eucl p)
    (hbeta_supp : ∀ (e : ι) (S : Finset (Fin p)), suppVec (betaLocal e S) ⊆ S)
    (hbeta_min : ∀ (e : ι) (S : Finset (Fin p)),
      IsMinOn (fun β => risk (μ e) β) {β : Eucl p | suppVec β ⊆ S} (betaLocal e S))
    (kappaL kappaU : ℝ) (hkappaL_pos : 0 < kappaL) (hkappaL_le : kappaL ≤ 1)
    (hkappaU : 1 ≤ kappaU)
    (hLoewnerL : ∀ (e : ι) (v : Eucl p), kappaL * ‖v‖ ^ 2 ≤ quad (covMat (μ e)) v)
    (hLoewnerU : ∀ (e : ι) (v : Eucl p), quad (covMat (μ e)) v ≤ kappaU * ‖v‖ ^ 2)
    (hIdent : ∀ S : Finset (Fin p), (S ∩ spurSet μ βstar).Nonempty →
      ∃ e e' : ι, betaLocal e S ≠ betaLocal e' S) :
    (∀ (eps : ℝ), 0 < eps → eps < 1 → ∀ γ : ℝ,
      eps⁻¹ * gammaStar μ betaLocal βstar kappaL ≤ γ → ∀ β : Eucl p,
      Qobj μ ω γ β - Qobj μ ω γ βstar ≥
        (1 - eps) * quad (pooledCov μ) (β - βstar) +
          kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
            dBar betaLocal (suppVec β)) ∧
    (∀ γ : ℝ, gammaStar μ betaLocal βstar kappaL < γ → ∀ β : Eucl p, β ≠ βstar →
      Qobj μ ω γ βstar < Qobj μ ω γ β)
:= by
  /- @proof-region region.root.3c7cc334b910 begin -/
  classical
  have hProb : ∀ e : ι, IsProbabilityMeasure (μ e) := fun e => (hLaw e).1
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have h : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast h
  have hsub_le : sigmaSub S_star ≤ (inferInstance : MeasurableSpace (Eucl p × ℝ)) := by
    simp only [sigmaSub]
    rw [← measurable_iff_comap_le]
    fun_prop
  have hVarInt : ∀ (e : ι),
      ∫ z, (z.2 - condExp (sigmaSub S_star) (μ e) (fun z' : Eucl p × ℝ => z'.2) z) ^ 2
        ∂(μ e) ≤ σ2 := by
    intro e
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hEq : ∫ z, (z.2 - condExp (sigmaSub S_star) (μ e)
          (fun z' : Eucl p × ℝ => z'.2) z) ^ 2 ∂(μ e)
        = ∫ z, condExp (sigmaSub S_star) (μ e)
            (fun z : Eucl p × ℝ =>
              (z.2 - condExp (sigmaSub S_star) (μ e) (fun z' : Eucl p × ℝ => z'.2) z) ^ 2)
            z ∂(μ e) := by
      rw [integral_condExp hsub_le]
    rw [hEq]
    have hle : condExp (sigmaSub S_star) (μ e)
        (fun z : Eucl p × ℝ =>
          (z.2 - condExp (sigmaSub S_star) (μ e) (fun z' : Eucl p × ℝ => z'.2) z) ^ 2) ≤ᵐ[μ e]
        (fun _ => σ2) := (hLaw e).2.2.2.2
    have hmono := integral_mono_ae (integrable_condExp) (integrable_const (μ := μ e) σ2) hle
    simpa using hmono
  have hVarRes : ∀ (e : ι),
      condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => residAt βstar z ^ 2)
        ≤ᵐ[μ e] (fun _ => σ2) := by
    intro e
    have h5 : condExp (sigmaSub S_star) (μ e)
        (fun z : Eucl p × ℝ =>
          (z.2 - condExp (sigmaSub S_star) (μ e) (fun z' : Eucl p × ℝ => z'.2) z) ^ 2)
        ≤ᵐ[μ e] (fun _ => σ2) := (hLaw e).2.2.2.2
    have hcongr : condExp (sigmaSub S_star) (μ e)
        (fun z : Eucl p × ℝ =>
          (z.2 - condExp (sigmaSub S_star) (μ e) (fun z' : Eucl p × ℝ => z'.2) z) ^ 2)
        =ᵐ[μ e]
        condExp (sigmaSub S_star) (μ e) (fun z : Eucl p × ℝ => residAt βstar z ^ 2) := by
      apply MeasureTheory.condExp_congr_ae
      filter_upwards [(hLaw e).2.2.2.1] with z hz
      simp only [residAt, hz]
    filter_upwards [h5, hcongr] with z hz1 hz2
    rw [← hz2]
    exact hz1
  have hResInt : ∀ (e : ι), ∫ z, residAt βstar z ^ 2 ∂(μ e) ≤ σ2 := by
    intro e
    have hEq : ∫ z, (z.2 - condExp (sigmaSub S_star) (μ e)
          (fun z' : Eucl p × ℝ => z'.2) z) ^ 2 ∂(μ e)
        = ∫ z, residAt βstar z ^ 2 ∂(μ e) := by
      apply integral_congr_ae
      filter_upwards [(hLaw e).2.2.2.1] with z hz
      simp only [residAt, hz]
    rw [← hEq]
    exact hVarInt e
  have hX2 : ∀ (e : ι) (j : Fin p), MemLp (fun z : Eucl p × ℝ => z.1 j) 2 (μ e) := by
    intro e j
    have hint : Integrable (fun z : Eucl p × ℝ => (z.1 j) ^ 2) (μ e) := (hLaw e).2.1 j
    have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.1 j) (μ e) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    exact (memLp_two_iff_integrable_sq hmeas).2 hint
  have hProdAll : ∀ (e : ι) (i j : Fin p),
      Integrable (fun z : Eucl p × ℝ => z.1 i * z.1 j) (μ e) := by
    intro e i j
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hmul : MemLp (fun z : Eucl p × ℝ => z.1 i * z.1 j) 1 (μ e) :=
      MemLp.mul (f := fun z : Eucl p × ℝ => z.1 j) (φ := fun z : Eucl p × ℝ => z.1 i)
        (p := 2) (q := 2) (hX2 e j) (hX2 e i)
    exact hmul.integrable le_rfl
  have hSqDot : ∀ (e : ι) (b : Eucl p),
      Integrable (fun z : Eucl p × ℝ => (dot b z.1) ^ 2) (μ e) := by
    intro e b
    have hsq : ∀ z : Eucl p × ℝ, (dot b z.1) ^ 2
        = ∑ i : Fin p, ∑ j : Fin p, (b i * b j) * (z.1 i * z.1 j) := by
      intro z
      simp only [dot, pow_two]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfun : (fun z : Eucl p × ℝ => (dot b z.1) ^ 2)
        = fun z => ∑ i : Fin p, ∑ j : Fin p, (b i * b j) * (z.1 i * z.1 j) := funext hsq
    rw [hfun]
    exact integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => by
        simpa only [smul_eq_mul] using (hProdAll e i j).const_mul (b i * b j)))
  have hDotMeas : ∀ (e : ι) (b : Eucl p),
      AEStronglyMeasurable (fun z : Eucl p × ℝ => dot b z.1) (μ e) := by
    intro e b
    have hfun : (fun z : Eucl p × ℝ => dot b z.1) = fun z => ∑ j : Fin p, b j * z.1 j := by
      funext z
      simp only [dot]
    rw [hfun]
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hResOfY : (∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) →
      ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => residAt βstar z ^ 2) (μ e) := by
    intro hY e
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hy : MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e) := by
      have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      exact (memLp_two_iff_integrable_sq hmeas).2 (hY e)
    have hdotmem : MemLp (fun z : Eucl p × ℝ => dot βstar z.1) 2 (μ e) :=
      (memLp_two_iff_integrable_sq (hDotMeas e βstar)).2 (hSqDot e βstar)
    have hres : MemLp (fun z : Eucl p × ℝ => residAt βstar z) 2 (μ e) := by
      have hsub : MemLp (fun z : Eucl p × ℝ => z.2 - dot βstar z.1) 2 (μ e) :=
        hy.sub hdotmem
      simpa only [residAt] using hsub
    exact hres.integrable_sq
  have hYsqOfMemLp : (∀ (e : ι), MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e)) →
      ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) :=
    fun hY e => (hY e).integrable_sq
  have hResOfMemLp : (∀ (e : ι), MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e)) →
      ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => residAt βstar z ^ 2) (μ e) := by
    intro hY e
    have hdotmem : MemLp (fun z : Eucl p × ℝ => dot βstar z.1) 2 (μ e) :=
      (memLp_two_iff_integrable_sq (hDotMeas e βstar)).2 (hSqDot e βstar)
    have hsub : MemLp (fun z : Eucl p × ℝ => z.2 - dot βstar z.1) 2 (μ e) :=
      (hY e).sub hdotmem
    have hres : MemLp (fun z : Eucl p × ℝ => residAt βstar z) 2 (μ e) := by
      simpa only [residAt] using hsub
    exact hres.integrable_sq
  have hGapForms : (∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) ↔
      (∀ (e : ι), MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e)) := by
    constructor
    · intro hY e
      have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      exact (memLp_two_iff_integrable_sq hmeas).2 (hY e)
    · exact hYsqOfMemLp
  have hYsqOfRes : (∀ (e : ι), Integrable (fun z : Eucl p × ℝ => residAt βstar z ^ 2) (μ e)) →
      ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) := by
    intro hR e
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hdotmem : MemLp (fun z : Eucl p × ℝ => dot βstar z.1) 2 (μ e) :=
      (memLp_two_iff_integrable_sq (hDotMeas e βstar)).2 (hSqDot e βstar)
    have hresmem : MemLp (fun z : Eucl p × ℝ => residAt βstar z) 2 (μ e) := by
      have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => residAt βstar z) (μ e) := by
        have h1 : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
          apply Measurable.aestronglyMeasurable
          fun_prop
        have h2 : AEStronglyMeasurable (fun z : Eucl p × ℝ => dot βstar z.1) (μ e) :=
          hDotMeas e βstar
        have h3 : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2 - dot βstar z.1) (μ e) :=
          h1.sub h2
        simpa only [residAt] using h3
      exact (memLp_two_iff_integrable_sq hmeas).2 (hR e)
    have hsum : MemLp (fun z : Eucl p × ℝ => residAt βstar z + dot βstar z.1) 2 (μ e) :=
      hresmem.add hdotmem
    have hy : MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e) := by
      simpa only [residAt, sub_add_cancel] using hsum
    exact hy.integrable_sq
  have hJunkRisk : ∀ (e : ι), ¬ Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) →
      ∀ b : Eucl p, risk (μ e) b = 0 := by
    intro e hni b
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hdotmem : MemLp (fun z : Eucl p × ℝ => dot b z.1) 2 (μ e) :=
      (memLp_two_iff_integrable_sq (hDotMeas e b)).2 (hSqDot e b)
    have hnotint : ¬ Integrable (fun z : Eucl p × ℝ => (z.2 - dot b z.1) ^ 2) (μ e) := by
      intro hint
      have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2 - dot b z.1) (μ e) := by
        have h1 : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
          apply Measurable.aestronglyMeasurable
          fun_prop
        exact h1.sub (hDotMeas e b)
      have hresmem : MemLp (fun z : Eucl p × ℝ => z.2 - dot b z.1) 2 (μ e) :=
        (memLp_two_iff_integrable_sq hmeas).2 hint
      have hsum : MemLp (fun z : Eucl p × ℝ => (z.2 - dot b z.1) + dot b z.1) 2 (μ e) :=
        hresmem.add hdotmem
      have hy : MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e) := by
        simpa only [sub_add_cancel] using hsum
      exact hni hy.integrable_sq
    exact integral_undef hnotint
  have hDegenerate : (∀ (e : ι), ¬ Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) →
      ∀ (γ : ℝ) (b : Eucl p), Qobj μ ω γ b = 0 := by
    intro hni γ b
    have hrisk : ∀ (e : ι) (b : Eucl p), risk (μ e) b = 0 := fun e => hJunkRisk e (hni e)
    have hpooled : pooledRisk μ ω b = 0 := by
      simp only [pooledRisk]
      refine Finset.sum_eq_zero (fun e _ => ?_)
      rw [hrisk e b]
      ring
    have hpart : ∀ (e : ι) (j : Fin p), partDeriv (μ e) b j = 0 := by
      intro e j
      have hconst : (fun t : ℝ => risk (μ e) (b + t • EuclideanSpace.single j (1 : ℝ)))
          = fun _ => (0 : ℝ) := by
        funext t
        exact hrisk e (b + t • EuclideanSpace.single j (1 : ℝ))
      simp only [partDeriv]
      rw [hconst]
      simp
    have hreg : regJ μ ω b = 0 := by
      simp only [regJ]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hb : b j ≠ 0
      · rw [if_pos hb]
        refine Finset.sum_eq_zero (fun e _ => ?_)
        rw [hpart e j]
        ring
      · rw [if_neg hb]
    simp only [Qobj]
    rw [hpooled, hreg]
    ring
  have hDegenerate_strict : (∀ (e : ι), ¬ Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) →
      ∀ (γ : ℝ) (β : Eucl p), ¬ (Qobj μ ω γ βstar < Qobj μ ω γ β) := by
    intro hni γ β
    have h1 : Qobj μ ω γ βstar = 0 := hDegenerate hni γ βstar
    have h2 : Qobj μ ω γ β = 0 := hDegenerate hni γ β
    rw [h1, h2]
    exact lt_irrefl 0
  have hNoGo : (∀ (γ : ℝ), gammaStar μ betaLocal βstar kappaL < γ →
      ∀ (β : Eucl p), β ≠ βstar → Qobj μ ω γ βstar < Qobj μ ω γ β) →
      (∀ (e : ι), ¬ Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) →
      ∀ (β : Eucl p), β = βstar := by
    intro hconv hni β
    by_contra hβ
    have hlt : Qobj μ ω (gammaStar μ betaLocal βstar kappaL + 1) βstar <
        Qobj μ ω (gammaStar μ betaLocal βstar kappaL + 1) β :=
      hconv (gammaStar μ betaLocal βstar kappaL + 1) (by linarith) β hβ
    exact hDegenerate_strict hni (gammaStar μ betaLocal βstar kappaL + 1) β hlt
  have hYsq0 : ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) :=
    hYsqOfMemLp hY2
  have hResL2 : ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => residAt βstar z ^ 2) (μ e) :=
    hResOfY hYsq0
  have hResMem : ∀ (e : ι), MemLp (fun z : Eucl p × ℝ => residAt βstar z) 2 (μ e) := by
    intro e
    have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => residAt βstar z) (μ e) := by
      have h1 : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      have h2 : AEStronglyMeasurable (fun z : Eucl p × ℝ => dot βstar z.1) (μ e) :=
        hDotMeas e βstar
      have h3 : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2 - dot βstar z.1) (μ e) :=
        h1.sub h2
      simpa only [residAt] using h3
    exact (memLp_two_iff_integrable_sq hmeas).2 (hResL2 e)
  have hYsq : ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) := by
    intro e
    have hdotmem : MemLp (fun z : Eucl p × ℝ => dot βstar z.1) 2 (μ e) :=
      (memLp_two_iff_integrable_sq (hDotMeas e βstar)).2 (hSqDot e βstar)
    have hsum : MemLp (fun z : Eucl p × ℝ => residAt βstar z + dot βstar z.1) 2 (μ e) :=
      (hResMem e).add hdotmem
    have hy : MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e) := by
      simpa only [residAt, sub_add_cancel] using hsum
    exact hy.integrable_sq
  have hYbound : ∀ (e : ι),
      ∫ z, z.2 ^ 2 ∂(μ e) ≤ 2 * σ2 + 2 * ∫ z, (dot βstar z.1) ^ 2 ∂(μ e) := by
    have hpt : ∀ z : Eucl p × ℝ,
        z.2 ^ 2 ≤ 2 * residAt βstar z ^ 2 + 2 * (dot βstar z.1) ^ 2 := by
      intro z
      have h2 := two_mul_le_add_sq |residAt βstar z| |dot βstar z.1|
      have h3 : residAt βstar z * dot βstar z.1
          ≤ |residAt βstar z| * |dot βstar z.1| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h5 : |residAt βstar z| ^ 2 = residAt βstar z ^ 2 := sq_abs _
      have h6 : |dot βstar z.1| ^ 2 = (dot βstar z.1) ^ 2 := sq_abs _
      simp only [residAt] at h2 h3 h5 h6 ⊢
      nlinarith [h2, h3, h5, h6]
    intro e
    haveI : IsProbabilityMeasure (μ e) := hProb e
    by_cases hint : Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)
    · have hA : Integrable (fun z : Eucl p × ℝ => 2 * residAt βstar z ^ 2) (μ e) :=
        (hResL2 e).const_mul 2
      have hB : Integrable (fun z : Eucl p × ℝ => 2 * (dot βstar z.1) ^ 2) (μ e) :=
        (hSqDot e βstar).const_mul 2
      have hae : (fun z : Eucl p × ℝ => z.2 ^ 2)
          ≤ᵐ[μ e] fun z => 2 * residAt βstar z ^ 2 + 2 * (dot βstar z.1) ^ 2 := by
        filter_upwards with z
        exact hpt z
      have h1 : ∫ z, z.2 ^ 2 ∂(μ e)
          ≤ ∫ z, 2 * residAt βstar z ^ 2 + 2 * (dot βstar z.1) ^ 2 ∂(μ e) := by
        have hmono := integral_mono_ae hint (hA.add hB) hae
        simpa only [Pi.add_apply] using hmono
      have hsplit : ∫ z, 2 * residAt βstar z ^ 2 + 2 * (dot βstar z.1) ^ 2 ∂(μ e)
          = 2 * ∫ z, residAt βstar z ^ 2 ∂(μ e)
            + 2 * ∫ z, (dot βstar z.1) ^ 2 ∂(μ e) := by
        have hsum := integral_add hA hB
        rw [integral_const_mul, integral_const_mul] at hsum
        simpa only [Pi.add_apply] using hsum
      rw [hsplit] at h1
      have hres := hResInt e
      linarith
    · rw [integral_undef hint]
      have hnn : (0:ℝ) ≤ ∫ z, (dot βstar z.1) ^ 2 ∂(μ e) :=
        integral_nonneg (fun z => sq_nonneg _)
      linarith [hσ2]
  have hY2 : ∀ (e : ι), MemLp (fun z : Eucl p × ℝ => z.2) 2 (μ e) := by
    intro e
    have hmeas : AEStronglyMeasurable (fun z : Eucl p × ℝ => z.2) (μ e) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    exact (memLp_two_iff_integrable_sq hmeas).2 (hYsq e)
  have hYint : ∀ (e : ι), Integrable (fun z : Eucl p × ℝ => z.2) (μ e) := by
    intro e
    haveI : IsProbabilityMeasure (μ e) := hProb e
    exact (hY2 e).integrable (by norm_num)
  have hYzj : ∀ (e : ι) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => z.2 * z.1 j) (μ e) := by
    intro e j
    haveI : IsProbabilityMeasure (μ e) := hProb e
    have hm : MemLp (fun z : Eucl p × ℝ => z.2 * z.1 j) 1 (μ e) :=
      MemLp.mul (f := fun z : Eucl p × ℝ => z.1 j) (φ := fun z : Eucl p × ℝ => z.2)
        (p := 2) (q := 2) (hX2 e j) (hY2 e)
    exact hm.integrable le_rfl
  have hYcross : ∀ (e : ι) (b : Eucl p),
      Integrable (fun z : Eucl p × ℝ => z.2 * dot b z.1) (μ e) := by
    intro e b
    have hfun : (fun z : Eucl p × ℝ => z.2 * dot b z.1)
        = fun z => ∑ j : Fin p, b j * (z.2 * z.1 j) := by
      funext z
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfun]
    exact integrable_finset_sum _ (fun j _ => by
      simpa only [smul_eq_mul] using (hYzj e j).const_mul (b j))
  have hIntAll : ∀ (e : ι) (b : Eucl p) (j : Fin p),
      Integrable (fun z : Eucl p × ℝ => (z.2 - dot b z.1) * z.1 j) (μ e) := by
    intro e b j
    have hdotzj : Integrable (fun z : Eucl p × ℝ => dot b z.1 * z.1 j) (μ e) := by
      have hfun : (fun z : Eucl p × ℝ => dot b z.1 * z.1 j)
          = fun z => ∑ i : Fin p, b i * (z.1 i * z.1 j) := by
        funext z
        simp only [dot, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hfun]
      exact integrable_finset_sum _ (fun i _ => by
        simpa only [smul_eq_mul] using (hProdAll e i j).const_mul (b i))
    have hsub : Integrable (fun z : Eucl p × ℝ => z.2 * z.1 j - dot b z.1 * z.1 j) (μ e) :=
      (hYzj e j).sub hdotzj
    simpa only [sub_mul] using hsub
  have hSqAll : ∀ (e : ι) (b : Eucl p),
      Integrable (fun z : Eucl p × ℝ => (z.2 - dot b z.1) ^ 2) (μ e) := by
    intro e b
    have hA : Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e) := (hY2 e).integrable_sq
    have hB : Integrable (fun z : Eucl p × ℝ => 2 * (z.2 * dot b z.1)) (μ e) := by
      simpa only [smul_eq_mul] using (hYcross e b).const_mul 2
    have hC : Integrable (fun z : Eucl p × ℝ => (dot b z.1) ^ 2) (μ e) := hSqDot e b
    have hcomb : Integrable
        (fun z : Eucl p × ℝ => z.2 ^ 2 - 2 * (z.2 * dot b z.1) + (dot b z.1) ^ 2) (μ e) :=
      (hA.sub hB).add hC
    convert hcomb using 1
    funext z
    ring
  have hPartDerivAll : ∀ (e : ι) (b : Eucl p) (j : Fin p),
      partDeriv (μ e) b j = -2 * ∫ z, (z.2 - dot b z.1) * z.1 j ∂(μ e) := by
    intro e b j
    haveI : IsProbabilityMeasure (μ e) := hProb e
    exact statopia_math_node_358034260_300c6b38 p (μ e) b j
      (hSqAll e b) (hIntAll e b j) ((hLaw e).2.1 j)
  have hOrth := statopia_math_node_3875025507_3baf775f p μ βstar S_star hS_star hProb hYint
    (fun e => (hLaw e).2.2.2.1) (fun e j => hIntAll e βstar j)
  have hOrthPer : ∀ (e : ι) (j : Fin p), j ∈ S_star →
      ∫ z, residAt βstar z * z.1 j ∂(μ e) = 0 := hOrth.1
  have hOrthStar : ∀ j : Fin p, j ∈ S_star →
      (Fintype.card ι : ℝ)⁻¹ * ∑ e, ∫ z, residAt βstar z * z.1 j ∂(μ e) = 0 := hOrth.2.1
  have hbCoeff_id : ∀ S : Finset (Fin p),
      bCoeff μ βstar S =
        ∑ j ∈ S, ((Fintype.card ι : ℝ)⁻¹ *
          ∑ e, ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) ^ 2 := by
    intro S
    rw [hOrth.2.2 S]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j hj
      exact Finset.mem_union_left _ hj
    · intro j hj hjs
      have hmem : j ∈ S_star := by
        rcases Finset.mem_union.mp hj with h | h
        · exact absurd h hjs
        · exact h
      rw [hOrthStar j hmem]
      ring
  have hRegStar : regJ μ ω βstar = 0 := by
    simp only [regJ]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hb : βstar j ≠ 0
    · rw [if_pos hb]
      apply Finset.sum_eq_zero
      intro e _
      have hmem : j ∈ S_star := (hS_star j).2 hb
      have hpd : partDeriv (μ e) βstar j = 0 := by
        rw [hPartDerivAll e βstar j]
        have h0 : (∫ z, residAt βstar z * z.1 j ∂(μ e)) = 0 := hOrthPer e j hmem
        simp only [residAt] at h0
        rw [h0]
        ring
      rw [hpd]
      ring
    · rw [if_neg hb]
  have hquad_smul : ∀ (c : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (v : Eucl p),
      quad (c • M) v = c * quad M v := by
    intro c M v
    simp only [quad, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad_sum : ∀ (M : ι → Matrix (Fin p) (Fin p) ℝ) (v : Eucl p),
      quad (∑ e, M e) v = ∑ e, quad (M e) v := by
    intro M v
    have h1 : quad (∑ e, M e) v = ∑ i, ∑ j, ∑ e, M e i j * v i * v j := by
      simp only [quad, Matrix.sum_apply, Finset.sum_mul]
    rw [h1]
    have h2 : (∑ i, ∑ j, ∑ e, M e i j * v i * v j : ℝ)
        = ∑ i, ∑ e, ∑ j, M e i j * v i * v j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    rw [h2, Finset.sum_comm]
    simp only [quad]
  have hpooled_loewner : ∀ v : Eucl p, kappaL * ‖v‖ ^ 2 ≤ quad (pooledCov μ) v := by
    intro v
    have h1 : quad (pooledCov μ) v = (Fintype.card ι : ℝ)⁻¹ * ∑ e, quad (covMat (μ e)) v := by
      simp only [pooledCov]
      rw [hquad_smul, hquad_sum]
    have hsum_ge : (Fintype.card ι : ℝ) * (kappaL * ‖v‖ ^ 2) ≤ ∑ e, quad (covMat (μ e)) v := by
      have h := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset ι)) => hLoewnerL e v)
      simpa using h
    have h6 : (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * (kappaL * ‖v‖ ^ 2))
        = kappaL * ‖v‖ ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard_pos), one_mul]
    calc quad (pooledCov μ) v
        = (Fintype.card ι : ℝ)⁻¹ * ∑ e, quad (covMat (μ e)) v := h1
      _ ≥ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * (kappaL * ‖v‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hsum_ge (le_of_lt (inv_pos.mpr hcard_pos))
      _ = kappaL * ‖v‖ ^ 2 := h6
  have hpooled_nonneg : ∀ v : Eucl p, 0 ≤ quad (pooledCov μ) v := by
    intro v
    have h1 := hpooled_loewner v
    have h2 : 0 ≤ kappaL * ‖v‖ ^ 2 := mul_nonneg (le_of_lt hkappaL_pos) (sq_nonneg _)
    linarith
  have hb_nonneg : ∀ S : Finset (Fin p), 0 ≤ bCoeff μ βstar S := by
    intro S
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hd_nonneg : ∀ S : Finset (Fin p), 0 ≤ dBar betaLocal S := by
    intro S
    apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (le_of_lt (inv_pos.mpr hcard_pos)) (by simp only [l2sq]; positivity)
  have hDegenerate_first : (∀ (e : ι), ¬ Integrable (fun z : Eucl p × ℝ => z.2 ^ 2) (μ e)) →
      ∀ (eps γ : ℝ) (β : Eucl p), β ≠ βstar → 0 < eps → eps < 1 →
        eps⁻¹ * gammaStar μ betaLocal βstar kappaL ≤ γ →
        ¬ ((1 - eps) * quad (pooledCov μ) (β - βstar) +
            kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
              dBar betaLocal (suppVec β) ≤
          Qobj μ ω γ β - Qobj μ ω γ βstar) := by
    intro hni eps γ β hβ heps heps1 hγ
    have hQβ : Qobj μ ω γ β = 0 := hDegenerate hni γ β
    have hQ0 : Qobj μ ω γ βstar = 0 := hDegenerate hni γ βstar
    have hq : 0 < quad (pooledCov μ) (β - βstar) := by
      have hne : β - βstar ≠ 0 := sub_ne_zero.mpr hβ
      have hnorm : 0 < ‖β - βstar‖ ^ 2 := by
        have hpos : 0 < ‖β - βstar‖ := by
          rw [norm_pos_iff]
          exact hne
        positivity
      have hlow := hpooled_loewner (β - βstar)
      nlinarith [hkappaL_pos]
    have hbase : (0 : ℝ) < (1 - eps) * quad (pooledCov μ) (β - βstar) := by
      have h1 : 0 < 1 - eps := by linarith
      exact mul_pos h1 hq
    have hgam : 0 ≤ kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
        dBar betaLocal (suppVec β) := by
      have h1 : 0 ≤ γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL := by linarith
      have h2 : 0 ≤ kappaL ^ 2 := sq_nonneg _
      have h3 : 0 ≤ dBar betaLocal (suppVec β) := hd_nonneg _
      exact mul_nonneg (mul_nonneg h2 h1) h3
    intro hcon
    rw [hQβ, hQ0, sub_zero] at hcon
    nlinarith [hbase, hgam, hcon]
  have hgs := statopia_math_node_3749859444_25f5fe8c p μ hProb βstar betaLocal kappaL hkappaL_pos hIdent
  have key : ∀ (eps γ : ℝ) (β : Eucl p), 0 < eps →
      eps⁻¹ * gammaStar μ betaLocal βstar kappaL ≤ γ →
      Qobj μ ω γ β - Qobj μ ω γ βstar ≥
        (1 - eps) * quad (pooledCov μ) (β - βstar) +
          kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
            dBar betaLocal (suppVec β) := by
    intro eps γ β heps hγ
    have hγ_nonneg : 0 ≤ γ := by
      have h1 : 0 ≤ eps⁻¹ * gammaStar μ betaLocal βstar kappaL :=
        mul_nonneg (le_of_lt (inv_pos.mpr heps)) hgs.1
      linarith
    have hDeltaSupp : ∀ j : Fin p, j ∉ suppVec β ∪ S_star → (β - βstar) j = 0 := by
      intro j hj
      have h1 : β j = 0 := by
        by_contra h
        exact hj (Finset.mem_union_left _ (by simpa [suppVec] using h))
      have h2 : βstar j = 0 := by
        by_contra h
        exact hj (Finset.mem_union_right _ ((hS_star j).2 h))
      have h3 : (β - βstar) j = β j - βstar j := by simp
      rw [h3, h1, h2]
      simp
    have hQ : Qobj μ ω γ β - Qobj μ ω γ βstar
        = (pooledRisk μ ω β - pooledRisk μ ω βstar) + γ * regJ μ ω β := by
      simp only [Qobj]
      rw [hRegStar]
      ring
    have hT1 := statopia_math_node_504088973_94182ea9 p μ hProb β βstar ω hω_unif
      (fun e => hSqAll e βstar) (fun e => hSqAll e β) (fun e j => hIntAll e βstar j)
      (fun e i j => hProdAll e i j)
    have hdot :
        dot (β - βstar)
            (WithLp.toLp 2 (fun j : Fin p => ∑ e : ι, ω e *
              ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)))
          = ∑ j : Fin p, (β - βstar) j *
              ((Fintype.card ι : ℝ)⁻¹ * ∑ e : ι,
                ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) := by
      simp only [dot]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [hω_unif, ← Finset.mul_sum]
    have hT1' : pooledRisk μ ω β - pooledRisk μ ω βstar
        = quad (pooledCov μ) (β - βstar) -
            2 * ∑ j : Fin p, (β - βstar) j *
              ((Fintype.card ι : ℝ)⁻¹ * ∑ e : ι,
                ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) := by
      rw [hT1, hdot]
    have huBar_eq : (WithLp.toLp 2 (fun j : Fin p => ∑ e : ι, ω e *
          ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) : Eucl p)
        = WithLp.toLp 2 (fun j : Fin p => (Fintype.card ι : ℝ)⁻¹ * ∑ e : ι,
            ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e)) := by
      have hf : (fun j : Fin p => ∑ e : ι, ω e *
            ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e))
          = fun j : Fin p => (Fintype.card ι : ℝ)⁻¹ * ∑ e : ι,
              ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) := by
        funext j
        simp only [hω_unif, ← Finset.mul_sum]
      rw [hf]
    have huBar_zero : ∀ j : Fin p, j ∈ S_star →
        (Fintype.card ι : ℝ)⁻¹ * ∑ e : ι,
          ∫ z : Eucl p × ℝ, residAt βstar z * z.1 j ∂(μ e) = 0 :=
      fun j hj => hOrthStar j hj
    have hlin := statopia_math_node_3737555372_fcbbc30d p μ βstar S_star hS_star hProb
      (fun e j => hIntAll e βstar j)
      β hDeltaSupp huBar_zero kappaL hkappaL_pos hpooled_loewner eps heps
    have hT1lb : pooledRisk μ ω β - pooledRisk μ ω βstar
        ≥ (1 - eps) * quad (pooledCov μ) (β - βstar) -
            eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) := by
      rw [hT1']
      rw [← huBar_eq] at hlin
      rw [hdot] at hlin
      linarith [hlin]
    have hT2 := statopia_math_node_2170213884_2b763c53 p μ hProb βstar S_star hS_star β betaLocal
      hbeta_supp hbeta_min kappaL hkappaL_pos hLoewnerL ω hω_unif hIntAll hPartDerivAll
    have hγregJ : γ * (kappaL ^ 2 * dBar betaLocal (suppVec β)) ≤ γ * regJ μ ω β :=
      mul_le_mul_of_nonneg_left hT2 hγ_nonneg
    have hb := hgs.2 (suppVec β)
    have hneg : -eps⁻¹ * kappaL ^ 2 * gammaStar μ betaLocal βstar kappaL *
          dBar betaLocal (suppVec β)
        ≤ -eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) := by
      have hle : (-eps⁻¹ * kappaL⁻¹) ≤ 0 := by
        have h2 : 0 < eps⁻¹ * kappaL⁻¹ := mul_pos (inv_pos.mpr heps) (inv_pos.mpr hkappaL_pos)
        linarith
      have hmul := mul_le_mul_of_nonpos_left hb hle
      have hinv : kappaL⁻¹ * kappaL ^ 3 = kappaL ^ 2 := by
        have hk : kappaL ≠ 0 := ne_of_gt hkappaL_pos
        calc kappaL⁻¹ * kappaL ^ 3 = kappaL⁻¹ * kappaL * kappaL ^ 2 := by ring
          _ = 1 * kappaL ^ 2 := by rw [inv_mul_cancel₀ hk]
          _ = kappaL ^ 2 := one_mul _
      have e1 : -eps⁻¹ * kappaL⁻¹ *
            (kappaL ^ 3 * gammaStar μ betaLocal βstar kappaL * dBar betaLocal (suppVec β))
          = -eps⁻¹ * kappaL ^ 2 * gammaStar μ betaLocal βstar kappaL *
              dBar betaLocal (suppVec β) := by
        have hsplit : -eps⁻¹ * kappaL⁻¹ *
              (kappaL ^ 3 * gammaStar μ betaLocal βstar kappaL * dBar betaLocal (suppVec β))
            = -eps⁻¹ * (kappaL⁻¹ * kappaL ^ 3) * gammaStar μ betaLocal βstar kappaL *
                dBar betaLocal (suppVec β) := by ring
        rw [hsplit, hinv]
      linarith [hmul, e1]
    have hcomb : (pooledRisk μ ω β - pooledRisk μ ω βstar) + γ * regJ μ ω β
        ≥ (1 - eps) * quad (pooledCov μ) (β - βstar) -
            eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) +
          γ * (kappaL ^ 2 * dBar betaLocal (suppVec β)) := by
      linarith [hT1lb, hγregJ]
    have hexp : (1 - eps) * quad (pooledCov μ) (β - βstar) -
            eps⁻¹ * kappaL⁻¹ * bCoeff μ βstar (suppVec β) +
          γ * (kappaL ^ 2 * dBar betaLocal (suppVec β))
        ≥ (1 - eps) * quad (pooledCov μ) (β - βstar) +
          kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
            dBar betaLocal (suppVec β) := by
      nlinarith [hneg]
    rw [hQ]
    linarith [hcomb, hexp]
  constructor
  · intro eps heps heps1 γ hγ β
    exact key eps γ β heps hγ
  · intro γ hγ β hβ
    have hQpos : 0 < quad (pooledCov μ) (β - βstar) := by
      have hne : β - βstar ≠ 0 := sub_ne_zero.mpr hβ
      have hnorm : 0 < ‖β - βstar‖ ^ 2 := by
        have hpos : 0 < ‖β - βstar‖ := by
          rw [norm_pos_iff]
          exact hne
        positivity
      have hlow := hpooled_loewner (β - βstar)
      nlinarith [hkappaL_pos]
    have hexists : ∃ eps : ℝ, 0 < eps ∧ eps < 1 ∧
        eps⁻¹ * gammaStar μ betaLocal βstar kappaL ≤ γ := by
      by_cases hpos : 0 < gammaStar μ betaLocal βstar kappaL
      · refine ⟨(1 + gammaStar μ betaLocal βstar kappaL / γ) / 2, ?_, ?_, ?_⟩
        · have hγpos : 0 < γ := lt_trans hpos hγ
          have : 0 < gammaStar μ betaLocal βstar kappaL / γ := div_pos hpos hγpos
          linarith
        · have hγpos : 0 < γ := lt_trans hpos hγ
          have hratio : gammaStar μ betaLocal βstar kappaL / γ < 1 := by
            rw [div_lt_one hγpos]
            exact hγ
          linarith
        · have hγpos : 0 < γ := lt_trans hpos hγ
          have hratio : gammaStar μ betaLocal βstar kappaL / γ < 1 := by
            rw [div_lt_one hγpos]
            exact hγ
          have hratio_pos : 0 < gammaStar μ betaLocal βstar kappaL / γ := div_pos hpos hγpos
          have heps_pos : (0:ℝ) < (1 + gammaStar μ betaLocal βstar kappaL / γ) / 2 := by linarith
          have h2 : gammaStar μ betaLocal βstar kappaL
              ≤ ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2) * γ := by
            have hexp : ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2) * γ
                = (γ + gammaStar μ betaLocal βstar kappaL) / 2 := by
              have hm : (1 + gammaStar μ betaLocal βstar kappaL / γ) * γ
                  = γ + gammaStar μ betaLocal βstar kappaL := by
                rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hγpos)]
              calc ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2) * γ
                  = (1 + gammaStar μ betaLocal βstar kappaL / γ) * γ / 2 := by ring
                _ = (γ + gammaStar μ betaLocal βstar kappaL) / 2 := by rw [hm]
            rw [hexp]
            linarith
          have h4 : ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2)⁻¹ *
                gammaStar μ betaLocal βstar kappaL
              ≤ ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2)⁻¹ *
                (((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2) * γ) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr heps_pos))
          have h3 : ((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2)⁻¹ *
                (((1 + gammaStar μ betaLocal βstar kappaL / γ) / 2) * γ) = γ := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt heps_pos), one_mul]
          linarith [h4, h3]
      · refine ⟨1 / 2, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · have hgsle : gammaStar μ betaLocal βstar kappaL ≤ 0 := le_of_not_gt hpos
          have hinv : ((1:ℝ) / 2)⁻¹ = 2 := by norm_num
          rw [hinv]
          linarith
    obtain ⟨eps, heps_pos, heps_lt, hle⟩ := hexists
    have hkey := key eps γ β heps_pos hle
    have hnneg : 0 ≤ kappaL ^ 2 * (γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL) *
        dBar betaLocal (suppVec β) := by
      have h1 : 0 ≤ γ - eps⁻¹ * gammaStar μ betaLocal βstar kappaL := by linarith
      have h2 : 0 ≤ kappaL ^ 2 := sq_nonneg _
      have h3 : 0 ≤ dBar betaLocal (suppVec β) := hd_nonneg _
      exact mul_nonneg (mul_nonneg h2 h1) h3
    have hmulpos : (0:ℝ) < (1 - eps) * quad (pooledCov μ) (β - βstar) := by
      have h1 : 0 < 1 - eps := by linarith
      exact mul_pos h1 hQpos
    have : 0 < Qobj μ ω γ β - Qobj μ ω γ βstar := by linarith
    linarith
  /- @proof-region region.root.3c7cc334b910 end -/

end Statlib.Imported

-- Paper root revision bcc9ddb5-5d12-4674-9e7f-52948aeb6877
