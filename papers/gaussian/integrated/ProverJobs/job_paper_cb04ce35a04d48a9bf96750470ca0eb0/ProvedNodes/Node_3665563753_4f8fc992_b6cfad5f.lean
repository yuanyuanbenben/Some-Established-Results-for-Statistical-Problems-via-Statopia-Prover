import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_193944682_6a261332_98805dda
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_3046040406_9e149626_a9cc1c4b
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_3740261163_f3714e7b_ab62c890
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ExternalNodes.Node_71807a7fff064607989e

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0




open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_3665563753_4f8fc992 : ∀ (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta < 1 / 2)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (alpha : ℝ) (halpha : 0 < alpha)
    (C_sigma : ℝ) (hC_sigma : 0 < C_sigma)
    (c_circ : ℝ) (hc_circ0 : 0 < c_circ) (hc_circ1 : c_circ < 1)
    (eps0 : ℝ) (heps0_0 : 0 < eps0) (heps0_1 : eps0 < 1)
    (C_R : ℝ) (hC_R : 0 < C_R)
    (c_0 : ℝ) (hc_0 : 0 < c_0),
    ∃ c_II : ℝ, 0 < c_II ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
      (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
      (hSig_psd : ∀ n, (Sig n).PosSemidef)
      (hSig_diag : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sig n j j)
      (π : (n : ℕ) → Equiv.Perm (Fin (p n)))
      (hπ_sorted : ∀ n, Antitone (fun i : Fin (p n) => Real.sqrt (Sig n (π n i) (π n i))))
      (Z : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
      (μv : (n : ℕ) → Fin (p n) → ℝ)
      (X : (n : ℕ) → Fin n → Ω → (Fin (p n) → ℝ))
      (hX_model : ∀ (n : ℕ) (i : Fin n) (ω : Ω),
        X n i ω = μv n + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω))
      (hX_mean : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), ∫ ω, X n i ω j ∂μ = μv n j)
      (hX_mem : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), MemLp (fun ω => X n i ω j) 2 μ)
      (hZ_meas : ∀ (n : ℕ) (i : Fin n), Measurable (Z n i))
      (hZ_indep : ∀ n, ProbabilityTheory.iIndepFun (Z n) μ)
      (hZ_ident : ∀ (n : ℕ) (i i' : Fin n), ProbabilityTheory.IdentDistrib (Z n i) (Z n i') μ μ)
      (hZ_mem : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), MemLp (fun ω => Z n i ω j) 2 μ)
      (hZ_mean : ∀ (n : ℕ) (i : Fin n) (j : Fin (p n)), ∫ ω, Z n i ω j ∂μ = 0)
      (hZ_cov : ∀ (n : ℕ) (i : Fin n) (j j' : Fin (p n)),
        ∫ ω, Z n i ω j * Z n i ω j' ∂μ = if j = j' then 1 else 0)
      (hZ_psi : ∀ (n : ℕ) (i : Fin n) (u : Fin (p n) → ℝ),
        (∑ j : Fin (p n), u j ^ 2) = 1 →
        psi1Norm μ (fun ω => ∑ j : Fin (p n), Z n i ω j * u j) ≤ ENNReal.ofReal c_0)
      (L : ℕ → ℕ)
      (hL_def : ∀ n, L n = Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
      (hL_le_p : ∀ n, L n ≤ p n)
      (k : ℕ → ℕ)
      (hk_def : ∀ n, k n = Nat.ceil
        (min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ))))
      (τ : ℕ → ℝ) (hτ0 : ∀ n, 0 ≤ τ n) (hτ1 : ∀ n, τ n < 1)
      (β : ℕ → ℝ) (hβ_def : ∀ n, β n = alpha * (1 - τ n))
      (c_tau : ℝ) (hc_tau : 0 < c_tau) (n_tau : ℕ) (hn_tau : 1 ≤ n_tau)
      (h_tau_cond : ∀ n : ℕ, n_tau ≤ n →
        c_tau ≤ (1 - τ n) * Real.sqrt (Real.log (n : ℝ)))
      (hσ_upper : ∀ (n : ℕ) (i : Fin (p n)), k n ≤ (i : ℕ) + 1 →
        Real.sqrt (Sig n (π n i) (π n i)) ≤
          C_sigma * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-alpha))
      (hσ_lower : ∀ (n : ℕ) (i : Fin (p n)), (i : ℕ) + 1 ≤ k n →
        c_circ * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-alpha) ≤
          Real.sqrt (Sig n (π n i) (π n i)))
      (hR_off : ∀ (n : ℕ) (i j : Fin (L n)), i ≠ j → corrMat p L Sig π hL_le_p n i j ≤ 1 - eps0)
      (hR_psd : ∀ n, (posPartMat (corrMat p L Sig π hL_le_p n)).PosSemidef)
      (hR_sum : ∀ n, ∑ i : Fin (L n), ∑ j : Fin (L n),
        (if i < j then max (corrMat p L Sig π hL_le_p n i j) 0 else 0) ≤ C_R * (L n : ℝ)),
      ∃ n_bridge : ℕ, 1 ≤ n_bridge ∧
        ∀ n : ℕ, n_bridge ≤ n → k n < p n →
          μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n)) ≤
            ENNReal.ofReal
              ((Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))
                {z : Fin (p n) → ℝ | ∀ j : Fin (p n),
                  ((π n).symm j : ℕ) < k n →
                    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z j
                      / Real.rpow (Real.sqrt (Sig n j j)) (τ n) ≤ t2fun L β c_circ n}).toReal
              + ENNReal.ofReal (c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + delta)) := by
  /- @proof-region region.target-node.session.cbf2415da6a30e2d begin -/
  intro δ hδ0 hδ1 a ha0 ha1 α hα C_sigma hC_sigma c_circ hc_circ0 hc_circ1
    epsilon0 hepsilon0_0 hepsilon0_1 C_R hC_R c_0 hc_0
  obtain ⟨c_II, hc_II_pos, hc_II⟩ :=
    PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.paper_e9c0500526fe4a15b7473a5f9efc21ed
      δ a c_0 α C_sigma c_circ epsilon0 C_R
      hδ0 hδ1 ha0 ha1 hc_0 hα hC_sigma hc_circ0 hc_circ1 hepsilon0_0 hepsilon0_1 hC_R
  refine ⟨c_II, hc_II_pos, ?_⟩
  intro Ω inst μ hμ p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem
    hZ_meas hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def τ hτ0 hτ1
    β hβ_def c_τ hc_τ n_τ hn_τ h_τ_cond hσ_upper hσ_lower hR_off hR_psd hR_sum
  have hL_fun : L = fun n : ℕ => Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))) :=
    funext hL_def
  subst hL_fun

  have hsdOf : ∀ (n : ℕ) (j : Fin (p n)),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j
        = Real.sqrt (Sig n j j) := fun n j => rfl
  have hsdOf_pos : ∀ (n : ℕ) (j : Fin (p n)),
      0 < PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j :=
    fun n j => by rw [hsdOf]; exact Real.sqrt_pos.2 (hSig_diag n j)
  have hsqrtCov : ∀ (n : ℕ),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sqrtCovMat (hSig_psd n)
        = Matrix.PosSemidef.sqrt (hSig_psd n) := fun n => rfl

  have hmulVec : ∀ {pn : ℕ} (A : Matrix (Fin pn) (Fin pn) ℝ) (v : Fin pn → ℝ) (j : Fin pn),
      A.mulVec v j = ∑ k, A j k * v k := fun A v j => rfl

  have hkIdx : ∀ (n : ℕ),
      k n = PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n := by
    intro n
    rw [hk_def]
    rfl

  haveI hOm : ∀ n : ℕ, MeasurableSpace Ω := fun _ => inst
  obtain ⟨n0, hn0_ge, hn0⟩ :=
    hc_II p hp (fun _ => Ω) (fun _ => μ) (fun _ => hμ)
      μv Sig hSig_psd Z (fun n i j => (measurable_pi_apply j).comp (hZ_meas n i))
      X (fun n i ω j => congrFun (hX_model n i ω) j) (fun n => hZ_indep n)
      (fun n i i' => hZ_ident n i i')
      (fun n hn j => ⟨(hZ_mem n ⟨0, hn⟩ j).integrable (by norm_num), hZ_mean n ⟨0, hn⟩ j⟩)
      (fun n hn i j => ⟨MeasureTheory.MemLp.integrable_mul (hZ_mem n ⟨0, hn⟩ i)
        (hZ_mem n ⟨0, hn⟩ j), hZ_cov n ⟨0, hn⟩ i j⟩)
      (fun n hn u hu => by
        have h1 : (∑ j : Fin (p n), u j ^ 2) = 1 := by
          have h := Real.sq_sqrt (x := ∑ j : Fin (p n), u j ^ 2)
            (Finset.sum_nonneg (fun j _ => sq_nonneg (u j)))
          rw [hu] at h
          simpa using h.symm
        have hm : Measurable fun om => ∑ j : Fin (p n), u j * Z n ⟨0, hn⟩ om j :=
          Finset.measurable_sum Finset.univ
            (fun j _ => measurable_const.mul ((measurable_pi_apply j).comp (hZ_meas n ⟨0, hn⟩)))
        have hfun : (fun om => ∑ j : Fin (p n), u j * Z n ⟨0, hn⟩ om j)
            = fun om => ∑ j : Fin (p n), Z n ⟨0, hn⟩ om j * u j := by
          funext om
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        rw [statopia_math_node_193944682_6a261332 Ω μ
          (fun om => ∑ j : Fin (p n), u j * Z n ⟨0, hn⟩ om j) hm.aemeasurable, hfun]
        exact hZ_psi n ⟨0, hn⟩ u h1)



      (fun n hn j => by
        have hmv : Measurable fun om =>
            (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n ⟨0, hn⟩ om) j := by
          simp only [hmulVec]
          exact Finset.measurable_sum Finset.univ
            (fun k _ => measurable_const.mul ((measurable_pi_apply k).comp (hZ_meas n ⟨0, hn⟩)))
        have hfun : (fun om => X n ⟨0, hn⟩ om j)
            = fun om => μv n j
                + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n ⟨0, hn⟩ om) j := by
          funext om
          rw [hX_model n ⟨0, hn⟩ om]
          rfl
        rw [hfun]
        exact measurable_const.add hmv)

      (fun n hn j => by
        set A : Matrix (Fin (p n)) (Fin (p n)) ℝ := Matrix.PosSemidef.sqrt (hSig_psd n) with hA
        have hsub : ∀ om, X n ⟨0, hn⟩ om j - μv n j = A.mulVec (Z n ⟨0, hn⟩ om) j := by
          intro om
          have h1 : (μv n + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n ⟨0, hn⟩ om)) j
              = μv n j + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n ⟨0, hn⟩ om) j := rfl
          rw [hX_model n ⟨0, hn⟩ om, hA, h1]
          ring
        have hexp : ∀ om, (X n ⟨0, hn⟩ om j - μv n j) ^ 2
            = ∑ k : Fin (p n), ∑ l : Fin (p n),
                (A j k * Z n ⟨0, hn⟩ om k) * (A j l * Z n ⟨0, hn⟩ om l) := by
          intro om
          rw [hsub om, hmulVec A (Z n ⟨0, hn⟩ om) j, pow_two, Finset.sum_mul]
          simp only [Finset.mul_sum]
        have hInt : ∀ k l : Fin (p n),
            Integrable (fun om => (A j k * Z n ⟨0, hn⟩ om k) * (A j l * Z n ⟨0, hn⟩ om l)) μ := by
          intro k l
          have h1 : Integrable (fun om => Z n ⟨0, hn⟩ om k * Z n ⟨0, hn⟩ om l) μ :=
            MeasureTheory.MemLp.integrable_mul (hZ_mem n ⟨0, hn⟩ k) (hZ_mem n ⟨0, hn⟩ l)
          have h2 : Integrable (fun om => (A j k * A j l)
              * (Z n ⟨0, hn⟩ om k * Z n ⟨0, hn⟩ om l)) μ := h1.const_mul (A j k * A j l)
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
        have hint : (fun om => (X n ⟨0, hn⟩ om j - μv n j) ^ 2)
            = fun om => ∑ k : Fin (p n), ∑ l : Fin (p n),
                (A j k * Z n ⟨0, hn⟩ om k) * (A j l * Z n ⟨0, hn⟩ om l) := funext hexp
        have hrow : ∑ k : Fin (p n), A j k * A j k = Sig n j j := by
          rw [hA]
          exact statopia_math_node_3740261163_f3714e7b (p n) (Sig n) (hSig_psd n) j






        have hinner : ∀ k : Fin (p n),
            ∑ l : Fin (p n), (A j k * A j l) * (if k = l then 1 else 0) = A j k * A j k := by
          intro k
          have hite : ∀ l : Fin (p n), (A j k * A j l) * (if k = l then 1 else 0)
              = if k = l then A j k * A j l else 0 := by
            intro l
            by_cases h : k = l <;> simp [h]
          simp only [hite]
          simp
        constructor
        · rw [hint]
          exact MeasureTheory.integrable_finset_sum Finset.univ
            (fun k _ => MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => hInt k l))
        · have hstep : ∫ om, ∑ k : Fin (p n), ∑ l : Fin (p n),
                (A j k * Z n ⟨0, hn⟩ om k) * (A j l * Z n ⟨0, hn⟩ om l) ∂μ
              = ∑ k : Fin (p n), ∑ l : Fin (p n), (A j k * A j l) * (if k = l then 1 else 0) := by
            rw [integral_finset_sum Finset.univ
              (fun k _ => MeasureTheory.integrable_finset_sum Finset.univ (fun l _ => hInt k l))]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [integral_finset_sum Finset.univ (fun l _ => hInt k l)]
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [← hZ_cov n ⟨0, hn⟩ k l, ← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall (fun om => by ring))
          rw [hint, hstep]
          simp only [hinner]
          exact hrow)


      hsdOf_pos
      π (fun n i i' h => hπ_sorted n h)
      (fun n => ⟨fun j hj => hσ_upper n j (by have hk := hkIdx n; omega),
        fun j => hσ_lower n
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n) j)
          (by
            have h1 : ((PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.posIn
                  (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n)
                  j : Fin (p n)) : ℕ) = (j : ℕ) := rfl
            have h2 : (j : ℕ) + 1 ≤
                PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n :=
              Nat.succ_le_of_lt j.2
            have hk := hkIdx n
            omega)⟩)
      (fun n => by
        intro i j hij
        exact hR_off n i j hij)
      (fun n => hR_psd n)
      (fun n => hR_sum n)



      τ (fun n => ⟨hτ0 n, hτ1 n⟩) ⟨c_τ, hc_τ, n_τ, hn_τ, h_τ_cond⟩
      (fun n => Fin (p n) → ℝ)
      (fun n => Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))
      (fun n => Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability (p n))
      (fun n z => z) (fun n => measurable_id)
      (fun n => Measure.map_id (μ := Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))



  refine ⟨n0, hn0_ge, ?_⟩
  intro n hn hkn
  set t : ℝ := t2fun
    (fun n : ℕ => Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ))))
    β c_circ n with ht
  set Mex : Ω → ℝ := fun ω =>
    PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
      (π n) (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n)) (τ n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
        (X n) (μv n) ω) with hMex
  set Mtil : (Fin (p n) → ℝ) → ℝ := fun z =>
    PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
      (π n) (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n)) (τ n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.StildeVec
        (hSig_psd n) (fun w => w) z) with hMtil
  have hK : PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kolmogorovDist
      (Measure.map Mex μ)
      (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
      ≤ c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) := hn0 n hn
  have hGauss : (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
      (Set.Iic t) =
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))
        {z : Fin (p n) → ℝ | ∀ j : Fin (p n), ((π n).symm j : ℕ) < k n →
          Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z j
            / Real.rpow (Real.sqrt (Sig n j j)) (τ n) ≤ t} := by
    rw [hkIdx n]
    exact statopia_math_node_3046040406_9e149626 (p n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
      (hp n)
      (le_trans
        (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.one_le_ellIdx p hp n)
        (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.ellIdx_le_kIdx p a n))
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n)
      (Sig n) (hSig_psd n) (τ n) t (π n)
  have hne : μ (Aevent p X μv Sig τ k π n t) ≠ ⊤ := measure_ne_top μ _
  have hnn1 : (0 : ℝ) ≤ ((Measure.map Mtil
      (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))) (Set.Iic t)).toReal :=
    ENNReal.toReal_nonneg

  have hnn2 : (0 : ℝ) ≤ c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) :=
    mul_nonneg hc_II_pos.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfac : (Real.sqrt (n : ℝ))⁻¹ = Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
    have h : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n)]
    exact h.symm
  have hSn : ∀ (ω : Ω) (j : Fin (p n)),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec (X n) (μv n) ω j
        = Svec p X μv n ω j := by
    intro ω j
    simp only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec,
      Svec]
    rw [hfac]
  have hdle :
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n ≤ p n :=
    PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx_le p a n
  have hd1 :
      1 ≤ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n :=
    le_trans
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.one_le_ellIdx p hp n)
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.ellIdx_le_kIdx p a n)
  have hkeyAbs : ∀ (f : Fin (p n) → ℝ) (s : ℝ),
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ
          (π n) (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)
          (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n)) (τ n) f
        ≤ s
        ↔ ∀ j : Fin (p n),
            ((π n).symm j : ℕ) <
                PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n →
              f j
                / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                  ^ (τ n) ≤ s := by
    intro f s
    simp only [PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.maxOverJ]
    set F : Finset ℝ :=
      (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (π n)
        (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).image
        (fun j => f j
          / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
            ^ (τ n))
      with hF
    have hbdd : BddAbove (↑F : Set ℝ) := F.finite_toSet.bddAbove
    constructor
    · intro h j hj
      have hmem : f j
            / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
              ^ (τ n) ∈
          ((PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (π n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).image
            (fun j => f j
              / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                ^ (τ n)) :
            Finset ℝ) :=
        Finset.mem_image.2
          ⟨j, Finset.mem_image.2
            ⟨(π n).symm j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩,
              Equiv.apply_symm_apply (π n) j⟩, rfl⟩
      have hmem' : f j
            / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
              ^ (τ n) ∈ (F : Set ℝ) := by
        rw [hF]
        exact hmem
      exact le_trans (le_csSup hbdd hmem') h
    · intro h
      refine csSup_le ⟨f (π n ⟨0, lt_of_lt_of_le hd1 hdle⟩)
        / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n)
            (π n ⟨0, lt_of_lt_of_le hd1 hdle⟩)) ^ (τ n), ?_⟩ ?_
      · exact (Finset.mem_image.2
          ⟨π n ⟨0, lt_of_lt_of_le hd1 hdle⟩, Finset.mem_image.2
            ⟨⟨0, lt_of_lt_of_le hd1 hdle⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd1⟩, rfl⟩,
            rfl⟩ :
          f (π n ⟨0, lt_of_lt_of_le hd1 hdle⟩)
              / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n)
                  (π n ⟨0, lt_of_lt_of_le hd1 hdle⟩)) ^ (τ n) ∈
            ((PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (π n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).image
              (fun j => f j
                / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                  ^ (τ n)) :
              Finset ℝ))
      · rintro x hx
        have hx' : x ∈
            ((PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset (π n)
              (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n)).image
              (fun j => f j
                / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                  ^ (τ n)) :
              Finset ℝ) := hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx'
        obtain ⟨i, hi, hπi⟩ := Finset.mem_image.1 hj
        have hsymm : (π n).symm j = i := by
          rw [← hπi]
          exact Equiv.symm_apply_apply (π n) i
        refine h j ?_
        rw [hsymm]
        exact (Finset.mem_filter.1 hi).2
  have hkey : ∀ (ω : Ω) (s : ℝ),
      (Mex ω ≤ s) ↔ ∀ j : Fin (p n),
        ((π n).symm j : ℕ) <
            PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n →
          PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
                (X n) (μv n) ω j
              / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                ^ (τ n) ≤ s := by
    intro ω s
    rw [hMex]
    exact hkeyAbs (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
      (X n) (μv n) ω) s
  have hAevent_eq : Aevent p X μv Sig τ k π n t = Mex ⁻¹' (Set.Iic t) := by
    ext ω
    simp only [Aevent, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, hkey ω t, hkIdx]
    constructor
    · intro h j hj
      rw [hSn ω j, hsdOf n j]
      exact h j hj
    · intro h j hj
      have h' := h j hj
      rwa [hSn ω j, hsdOf n j] at h'
  have hXm : ∀ (i : Fin n) (j : Fin (p n)), Measurable fun ω => X n i ω j := by
    intro i j
    have hmv : Measurable fun ω =>
        (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω) j := by
      simp only [hmulVec]
      exact Finset.measurable_sum Finset.univ
        (fun k _ => measurable_const.mul ((measurable_pi_apply k).comp (hZ_meas n i)))
    have hfun : (fun ω => X n i ω j) = fun ω =>
        μv n j + (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec (Z n i ω) j := by
      funext ω
      rw [hX_model n i ω]
      rfl
    rw [hfun]
    exact measurable_const.add hmv
  have hSv : ∀ j : Fin (p n), Measurable fun ω =>
      PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
        (X n) (μv n) ω j := by
    intro j
    have hsum : Measurable fun ω => ∑ i : Fin n, (X n i ω j - μv n j) :=
      Finset.measurable_sum Finset.univ (fun i _ => (hXm i j).sub measurable_const)
    exact hsum.const_mul _
  have hIdx : ∀ (P : Fin (p n) → Prop),
      (∀ j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
          (π n) (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n),
          P j)
        ↔ ∀ j : Fin (p n),
            ((π n).symm j : ℕ) <
                PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n →
              P j := by
    intro P
    constructor
    · intro h j hj
      exact h j (Finset.mem_image.2
        ⟨(π n).symm j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩,
          Equiv.apply_symm_apply (π n) j⟩)
    · intro h j hj
      obtain ⟨i, hi, hπi⟩ := Finset.mem_image.1 hj
      have hsymm : (π n).symm j = i := by
        rw [← hπi]
        exact Equiv.symm_apply_apply (π n) i
      refine h j ?_
      rw [hsymm]
      exact (Finset.mem_filter.1 hi).2
  have hmeas : Measurable Mex := by
    refine measurable_of_Iic (fun s => ?_)
    have hset : Mex ⁻¹' (Set.Iic s) =
        ⋂ j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
            (π n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n),
          {ω : Ω | PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
                  (X n) (μv n) ω j
                / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
                  ^ (τ n) ≤ s} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter]
      rw [hkey ω s]
      exact (hIdx (fun j =>
        PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.SnVec
              (X n) (μv n) ω j
            / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
              ^ (τ n) ≤ s)).symm
    rw [hset]
    exact Finset.measurableSet_biInter _ (fun j _ => ((hSv j).div_const _) measurableSet_Iic)
  have hLHS : μ (Aevent p X μv Sig τ k π n t) = (Measure.map Mex μ) (Set.Iic t) := by
    rw [hAevent_eq, Measure.map_apply hmeas measurableSet_Iic]
  have hP0 : (0 : ℝ) ≤ ((Measure.map Mex μ) (Set.Iic t)).toReal := ENNReal.toReal_nonneg
  have hMv : ∀ j : Fin (p n), Measurable fun z : Fin (p n) → ℝ =>
      (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec z j := by
    intro j
    simp only [hmulVec]
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_const.mul (measurable_pi_apply k))
  have hkeyMtil : ∀ (z : Fin (p n) → ℝ) (s : ℝ), (Mtil z ≤ s) ↔
      ∀ j : Fin (p n),
        ((π n).symm j : ℕ) <
            PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n →
          (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec z j
            / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
              ^ (τ n) ≤ s := by
    intro z s
    rw [hMtil]
    exact hkeyAbs (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.StildeVec
      (hSig_psd n) (fun w => w) z) s
  have hmeasMtil : Measurable Mtil := by
    refine measurable_of_Iic (fun s => ?_)
    have hset : Mtil ⁻¹' (Set.Iic s) =
        ⋂ j ∈ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.Jset
            (π n)
            (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kIdx p a n),
          {z : Fin (p n) → ℝ | (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec z j
            / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
              ^ (τ n) ≤ s} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter]
      rw [hkeyMtil z s]
      exact (hIdx (fun j => (Matrix.PosSemidef.sqrt (hSig_psd n)).mulVec z j
        / (PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.sdOf (Sig n) j)
          ^ (τ n) ≤ s)).symm
    rw [hset]
    exact Finset.measurableSet_biInter _ (fun j _ => ((hMv j).div_const _) measurableSet_Iic)
  have hxle : ∀ s : ℝ, ((Measure.map Mex μ) (Set.Iic s)).toReal ≤ 1 := by
    intro s
    have h1 : (Measure.map Mex μ) (Set.Iic s) ≤ 1 := by
      calc (Measure.map Mex μ) (Set.Iic s)
          ≤ (Measure.map Mex μ) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            rw [Measure.map_apply hmeas MeasurableSet.univ]
            simp
    calc ((Measure.map Mex μ) (Set.Iic s)).toReal
        ≤ ((1 : ℝ≥0∞)).toReal := ENNReal.toReal_mono (by simp) h1
      _ = 1 := by simp
  have hyle : ∀ s : ℝ,
      ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
        (Set.Iic s)).toReal ≤ 1 := by
    intro s
    have h1 : (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
        (Set.Iic s) ≤ 1 := by
      calc (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
            (Set.Iic s)
          ≤ (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
            Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            haveI :=
              Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability (p n)
            rw [Measure.map_apply hmeasMtil MeasurableSet.univ]
            simp
    calc ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
          (Set.Iic s)).toReal
        ≤ ((1 : ℝ≥0∞)).toReal := ENNReal.toReal_mono (by simp) h1
      _ = 1 := by simp
  have hbdd : BddAbove (Set.range (fun s : ℝ =>
      |((Measure.map Mex μ) (Set.Iic s)).toReal
        - ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
            (Set.Iic s)).toReal|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    have h1 := hxle s
    have h2 := hyle s
    have h3 : (0 : ℝ) ≤ ((Measure.map Mex μ) (Set.Iic s)).toReal := ENNReal.toReal_nonneg
    have h4 : (0 : ℝ) ≤ ((Measure.map Mtil
        (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))) (Set.Iic s)).toReal :=
      ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hstep : |((Measure.map Mex μ) (Set.Iic t)).toReal
      - ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
          (Set.Iic t)).toReal| ≤ c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) :=
    calc |((Measure.map Mex μ) (Set.Iic t)).toReal
          - ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
              (Set.Iic t)).toReal|
        ≤ PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Statlib.Imported.kolmogorovDist
            (Measure.map Mex μ)
            (Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))) :=
          le_ciSup hbdd t
      _ ≤ c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) := hK
  have hfrac := (abs_le.1 hstep).2
  have hpoint : ((Measure.map Mex μ) (Set.Iic t)).toReal
      ≤ ((Measure.map Mtil (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)))
          (Set.Iic t)).toReal + c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) := by
    linarith
  calc μ (Aevent p X μv Sig τ k π n t)
      = ENNReal.ofReal ((μ (Aevent p X μv Sig τ k π n t)).toReal) :=
        (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal ((Measure.map Mex μ) (Set.Iic t)).toReal := by rw [hLHS]
    _ ≤ ENNReal.ofReal (((Measure.map Mtil
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))) (Set.Iic t)).toReal
          + c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) :=
        ENNReal.ofReal_le_ofReal hpoint
    _ = ENNReal.ofReal ((Measure.map Mtil
          (Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))) (Set.Iic t)).toReal
          + ENNReal.ofReal (c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) :=
        ENNReal.ofReal_add hnn1 hnn2
    _ = ENNReal.ofReal ((Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n))
          {z : Fin (p n) → ℝ | ∀ j : Fin (p n), ((π n).symm j : ℕ) < k n →
            Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z j
              / Real.rpow (Real.sqrt (Sig n j j)) (τ n) ≤ t}).toReal
          + ENNReal.ofReal (c_II * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) := by rw [hGauss]







  /- @proof-region region.target-node.session.cbf2415da6a30e2d end -/

end

end Statlib.Imported

