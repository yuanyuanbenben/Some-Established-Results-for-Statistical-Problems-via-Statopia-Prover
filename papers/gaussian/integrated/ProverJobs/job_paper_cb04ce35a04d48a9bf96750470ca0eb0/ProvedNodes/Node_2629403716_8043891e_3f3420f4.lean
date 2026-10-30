import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_1071413046_2a904d5b_c0da11da
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_1614795123_3bc3bd18_7f037ed0
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes.Node_3665563753_4f8fc992_b6cfad5f
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
theorem statopia_math_node_2629403716_8043891e : ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (α : ℝ) (hα : 0 < α)
    (C_sigma : ℝ) (hC_sigma : 0 < C_sigma)
    (c_circ : ℝ) (hc_circ0 : 0 < c_circ) (hc_circ1 : c_circ < 1)
    (ε0 : ℝ) (hε0_0 : 0 < ε0) (hε0_1 : ε0 < 1)
    (C_R : ℝ) (hC_R : 0 < C_R)
    (c_0 : ℝ) (hc_0 : 0 < c_0),
    ∃ C₁ : ℝ, 0 < C₁ ∧
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
      (hZ_indep : ∀ n, iIndepFun (Z n) μ)
      (hZ_ident : ∀ (n : ℕ) (i i' : Fin n), IdentDistrib (Z n i) (Z n i') μ μ)
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
      (β : ℕ → ℝ) (hβ_def : ∀ n, β n = α * (1 - τ n))
      (hτ_cond : LessTilde (fun _ => (1 : ℝ))
        (fun n => (1 - τ n) * Real.sqrt (Real.log (n : ℝ))))
      (hσ_upper : ∀ (n : ℕ) (i : Fin (p n)), k n ≤ (i : ℕ) + 1 →
        Real.sqrt (Sig n (π n i) (π n i)) ≤
          C_sigma * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-α))
      (hσ_lower : ∀ (n : ℕ) (i : Fin (p n)), (i : ℕ) + 1 ≤ k n →
        c_circ * Real.rpow (((i : ℕ) + 1 : ℕ) : ℝ) (-α) ≤
          Real.sqrt (Sig n (π n i) (π n i)))
      (hR_off : ∀ (n : ℕ) (i j : Fin (L n)), i ≠ j → corrMat p L Sig π hL_le_p n i j ≤ 1 - ε0)
      (hR_psd : ∀ n, (posPartMat (corrMat p L Sig π hL_le_p n)).PosSemidef)
      (hR_sum : ∀ n, ∑ i : Fin (L n), ∑ j : Fin (L n),
          (if i < j then max (corrMat p L Sig π hL_le_p n i j) 0 else 0) ≤ C_R * (L n : ℝ)),
        ∃ N₁ : ℕ, 1 ≤ N₁ ∧
        ∀ n : ℕ, N₁ ≤ n → k n < p n →
          μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n)) ≤
            ENNReal.ofReal (C₁ * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) := by
  /- @proof-region region.target-node.session.108754179e53fefb begin -/
  classical
  intro δ hδ0 hδ1 a ha0 ha1 α hα C_sigma hC_sigma c_circ hc_circ0 hc_circ1 ε0 hε0_0 hε0_1
    C_R hC_R c_0 hc_0
  obtain ⟨C', hC'pos, hC'⟩ :=
    @statopia_math_node_1614795123_3bc3bd18.{0} ε0 hε0_0 hε0_1 C_R hC_R
  obtain ⟨cII, hcIIpos, h_bridge⟩ :=
    statopia_math_node_3665563753_4f8fc992 δ hδ0 hδ1 a ha0 ha1 α hα C_sigma hC_sigma c_circ hc_circ0
      hc_circ1 ε0 hε0_0 hε0_1 C_R hC_R c_0 hc_0
  refine ⟨C' + cII, by linarith, ?_⟩
  intro Ω _ μ _ p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem hZ_meas
    hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def τ hτ0 hτ1 β
    hβ_def hτ_cond hσ_upper hσ_lower hR_off hR_psd hR_sum
  obtain ⟨c_τ, hc_τ_pos, n_τ0, h_τ_pt⟩ := hτ_cond
  set c_tau : ℝ := c_τ⁻¹ with hc_tau_def
  have hc_tau_pos : 0 < c_tau := by
    rw [hc_tau_def]
    exact inv_pos.mpr hc_τ_pos
  set n_tau0 : ℕ := max n_τ0 1 with hn_tau_def
  have hn_tau_ge : 1 ≤ n_tau0 := by
    rw [hn_tau_def]
    exact le_max_right _ _
  have h_tau_cond : ∀ n : ℕ, n_tau0 ≤ n →
      c_tau ≤ (1 - τ n) * Real.sqrt (Real.log (n : ℝ)) := by
    intro n hn
    have h1 : n_τ0 ≤ n := by
      rw [hn_tau_def] at hn
      exact le_trans (le_max_left _ _) hn
    have h2 : (1 : ℝ) ≤ c_τ * ((1 - τ n) * Real.sqrt (Real.log (n : ℝ))) := h_τ_pt n h1
    have h4 : c_τ⁻¹ * c_τ ≤ ((1 - τ n) * Real.sqrt (Real.log (n : ℝ))) * c_τ := by
      rw [inv_mul_cancel₀ (ne_of_gt hc_τ_pos)]
      nlinarith [h2]
    have h5 : c_τ⁻¹ ≤ (1 - τ n) * Real.sqrt (Real.log (n : ℝ)) :=
      le_of_mul_le_mul_right h4 hc_τ_pos
    rw [hc_tau_def]
    exact h5
  obtain ⟨n_num, _, _⟩ :=
    statopia_math_node_1071413046_2a904d5b a ha0 ha1 α hα c_tau hc_tau_pos n_tau0 hn_tau_ge
  obtain ⟨n_bridge, _, h_bridge_n⟩ :=
    @h_bridge Ω _ μ _ p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem hZ_meas
      hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def τ hτ0 hτ1 β hβ_def
      c_tau hc_tau_pos n_tau0 hn_tau_ge h_tau_cond
      hσ_upper hσ_lower hR_off hR_psd hR_sum
  refine ⟨max (max n_num n_bridge) 3,
    le_trans (by norm_num : (1 : ℕ) ≤ 3) (le_max_right _ _), ?_⟩
  intro n hn hkn
  let G : (Fin (p n) → ℝ) → Fin (p n) → ℝ :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n)
  let A : Matrix (Fin (L n)) (Fin (p n)) ℝ :=
    fun i j => if j = π n (Fin.castLE (hL_le_p n) i) then (Real.sqrt (Sig n j j))⁻¹ else 0
  let zeta : (Fin (p n) → ℝ) → Fin (L n) → ℝ := fun z => A.mulVec (G z)
  let P' : Measure (Fin (p n) → ℝ) :=
    Statlib.StatFoundation.RandomVariable.Gaussian.standardPi (p n)
  let Kset : Set (Fin (p n) → ℝ) :=
    {z | ∀ j : Fin (p n), ((π n).symm j : ℕ) < k n →
      G z j / Real.rpow (Real.sqrt (Sig n j j)) (τ n) ≤ t2fun L β c_circ n}
  let Gset : Set (Fin (p n) → ℝ) :=
    {z | ∀ i : Fin (L n), zeta z i ≤ Real.sqrt (Real.log (L n : ℝ))}
  have hTransfer : μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n)) ≤
      ENNReal.ofReal (P' Kset).toReal
        + ENNReal.ofReal (cII * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) :=
    h_bridge_n n (le_trans (le_trans (le_max_right n_num n_bridge) (le_max_left _ 3)) hn) hkn
  have hShrink : (P' Kset).toReal ≤ (P' Gset).toReal := by
    have hLpos : 0 < L n := by
      have hpos : (0 : ℝ) < min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) := by
        refine lt_min (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_
        have hm : (1 : ℝ) ≤ (p n : ℝ) := by exact_mod_cast hp n
        linarith
      rw [hL_def]
      exact Nat.ceil_pos.mpr hpos
    have hLk : L n ≤ k n := by
      have h1 : (L n : ℝ) ≤
          min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
            ((p n : ℝ)) :=
        le_min (le_max_left _ _) (by exact_mod_cast hL_le_p n)
      have h2 : min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ)) ≤ (k n : ℝ) := by
        rw [hk_def]
        exact (Nat.ceil_le).mp le_rfl
      exact_mod_cast le_trans h1 h2
    have hz : ∀ (v : Fin (p n) → ℝ) (i : Fin (L n)),
        zeta v i = G v (π n (Fin.castLE (hL_le_p n) i)) /
          Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
            (π n (Fin.castLE (hL_le_p n) i))) := by
      intro v i
      change (∑ j : Fin (p n),
          (if j = π n (Fin.castLE (hL_le_p n) i) then (Real.sqrt (Sig n j j))⁻¹ else 0)
            * G v j)
        = G v (π n (Fin.castLE (hL_le_p n) i)) /
            Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i)))
      rw [Finset.sum_eq_single (π n (Fin.castLE (hL_le_p n) i))]
      · rw [if_pos rfl, div_eq_mul_inv]
        ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hsub : Kset ⊆ Gset := by
      intro v hv
      have hzi : ∀ i : Fin (L n),
          G v (π n (Fin.castLE (hL_le_p n) i)) /
            Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i))) ≤ Real.sqrt (Real.log (L n : ℝ)) := by
        intro i
        have hi_lt : (i : ℕ) < k n := by
          have h1 := i.isLt
          omega
        have hi_le : (i : ℕ) + 1 ≤ k n := by omega
        have hcast : ((Fin.castLE (hL_le_p n) i : Fin (p n)) : ℕ) = (i : ℕ) := rfl
        have hSpos : 0 < Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
            (π n (Fin.castLE (hL_le_p n) i))) :=
          Real.sqrt_pos.mpr (hSig_diag n (π n (Fin.castLE (hL_le_p n) i)))
        have hσlow : c_circ * Real.rpow ((i : ℝ) + 1) (-α) ≤
            Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i))) := by
          have h := hσ_lower n (Fin.castLE (hL_le_p n) i) (by rw [hcast]; exact hi_le)
          simpa only [hcast, Nat.cast_add, Nat.cast_one] using h
        have hY : G v (π n (Fin.castLE (hL_le_p n) i)) /
            Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i)))) (τ n) ≤ t2fun L β c_circ n := by
          refine hv (π n (Fin.castLE (hL_le_p n) i)) ?_
          rw [Equiv.symm_apply_apply, hcast]
          exact hi_lt
        have he_pos : 0 < 1 - τ n := by linarith [hτ1 n]
        have he_nonneg : 0 ≤ 1 - τ n := le_of_lt he_pos
        have hXnonneg : 0 ≤ c_circ * Real.rpow ((i : ℝ) + 1) (-α) :=
          mul_nonneg hc_circ0.le (Real.rpow_nonneg (by positivity) _)
        have hYpos : 0 < Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) :=
          Real.rpow_pos_of_pos (by positivity) _
        have hYleL : Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) ≤
            Real.rpow (L n : ℝ) (α * (1 - τ n)) :=
          Real.rpow_le_rpow (by positivity) (by
            have h1 : ((i : ℕ) + 1 : ℕ) ≤ L n := by
              have := i.isLt
              omega
            have h2 : ((i : ℕ) : ℝ) + 1 ≤ (L n : ℝ) := by exact_mod_cast h1
            linarith) (mul_nonneg hα.le he_nonneg)
        have hLposR : (0 : ℝ) < (L n : ℝ) := by exact_mod_cast hLpos
        have hβe : β n = α * (1 - τ n) := hβ_def n
        have hA2 : t2fun L β c_circ n * Real.rpow (L n : ℝ) (α * (1 - τ n))
            = c_circ * Real.sqrt (Real.log (L n : ℝ)) := by
          have hstep : Real.rpow (L n : ℝ) (-(β n)) *
              Real.rpow (L n : ℝ) (α * (1 - τ n)) = 1 := by
            have h0 : -(β n) + α * (1 - τ n) = 0 := by
              rw [hβe]
              ring
            calc Real.rpow (L n : ℝ) (-(β n)) * Real.rpow (L n : ℝ) (α * (1 - τ n))
                = Real.rpow (L n : ℝ) (-(β n) + α * (1 - τ n)) :=
                  (Real.rpow_add hLposR (-(β n)) (α * (1 - τ n))).symm
              _ = Real.rpow (L n : ℝ) 0 := by rw [h0]
              _ = 1 := Real.rpow_zero _
          simp only [t2fun]
          calc c_circ * (Real.rpow (L n : ℝ) (-(β n)) * Real.sqrt (Real.log (L n : ℝ)))
                * Real.rpow (L n : ℝ) (α * (1 - τ n))
              = c_circ * Real.sqrt (Real.log (L n : ℝ))
                  * (Real.rpow (L n : ℝ) (-(β n))
                    * Real.rpow (L n : ℝ) (α * (1 - τ n))) := by ring
            _ = c_circ * Real.sqrt (Real.log (L n : ℝ)) * 1 := by rw [hstep]
            _ = c_circ * Real.sqrt (Real.log (L n : ℝ)) := by ring
        have ht2nonneg : 0 ≤ t2fun L β c_circ n := by
          simp only [t2fun]
          exact mul_nonneg hc_circ0.le
            (mul_nonneg (Real.rpow_nonneg hLposR.le _) (Real.sqrt_nonneg _))
        have hA : t2fun L β c_circ n * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n))
            ≤ c_circ * Real.sqrt (Real.log (L n : ℝ)) := by
          calc t2fun L β c_circ n * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n))
              ≤ t2fun L β c_circ n * Real.rpow (L n : ℝ) (α * (1 - τ n)) :=
                mul_le_mul_of_nonneg_left hYleL ht2nonneg
            _ = c_circ * Real.sqrt (Real.log (L n : ℝ)) := hA2
        have hmono : ∀ y z : ℝ, y ≤ z → Real.rpow c_circ z ≤ Real.rpow c_circ y := by
          intro y z hyz
          exact Real.rpow_le_rpow_of_exponent_ge hc_circ0 hc_circ1.le hyz
        have hcc_e : c_circ ≤ Real.rpow c_circ (1 - τ n) := by
          have h : Real.rpow c_circ 1 ≤ Real.rpow c_circ (1 - τ n) :=
            hmono (1 - τ n) 1 (by linarith [hτ0 n])
          simpa using h
        have hXe : Real.rpow (c_circ * Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n)
            ≤ Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n) :=
          Real.rpow_le_rpow hXnonneg hσlow he_nonneg
        have hmulrpow : Real.rpow (c_circ * Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n)
            = Real.rpow c_circ (1 - τ n)
              * Real.rpow (Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n) :=
          Real.mul_rpow hc_circ0.le (Real.rpow_nonneg (by positivity) _)
        have hrpowmul : Real.rpow (Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n)
            = Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n))) := by
          have h := Real.rpow_mul (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1) (-α) (1 - τ n)
          rw [show -α * (1 - τ n) = -(α * (1 - τ n)) by ring] at h
          exact h.symm
        have hXsplit : Real.rpow (c_circ * Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n)
            = Real.rpow c_circ (1 - τ n)
              * Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n))) := by
          rw [hmulrpow, hrpowmul]
        have h1eq : Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n)))
            * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) = 1 := by
          have h0 : -(α * (1 - τ n)) + α * (1 - τ n) = 0 := by ring
          calc Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n)))
                * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n))
              = Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n)) + α * (1 - τ n)) :=
                (Real.rpow_add (by positivity : (0 : ℝ) < (i : ℝ) + 1) _ _).symm
            _ = Real.rpow ((i : ℝ) + 1) 0 := by rw [h0]
            _ = 1 := Real.rpow_zero _
        have hB : c_circ * Real.sqrt (Real.log (L n : ℝ))
            ≤ Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n) * Real.sqrt (Real.log (L n : ℝ))
              * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) := by
          calc c_circ * Real.sqrt (Real.log (L n : ℝ))
              ≤ Real.rpow c_circ (1 - τ n) * Real.sqrt (Real.log (L n : ℝ)) :=
                mul_le_mul_of_nonneg_right hcc_e (Real.sqrt_nonneg _)
            _ = Real.rpow c_circ (1 - τ n) * Real.sqrt (Real.log (L n : ℝ)) * 1 := by ring
            _ = Real.rpow c_circ (1 - τ n) * Real.sqrt (Real.log (L n : ℝ))
                  * (Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n)))
                      * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n))) := by rw [h1eq]
            _ = (Real.rpow c_circ (1 - τ n)
                    * Real.rpow ((i : ℝ) + 1) (-(α * (1 - τ n))))
                  * Real.sqrt (Real.log (L n : ℝ))
                  * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) := by ring
            _ = Real.rpow (c_circ * Real.rpow ((i : ℝ) + 1) (-α)) (1 - τ n)
                  * Real.sqrt (Real.log (L n : ℝ))
                  * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) := by rw [hXsplit]
            _ ≤ Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n)
                  * Real.sqrt (Real.log (L n : ℝ))
                  * Real.rpow ((i : ℝ) + 1) (α * (1 - τ n)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hXe (Real.sqrt_nonneg _)) (le_of_lt hYpos)
        have hKey : t2fun L β c_circ n ≤
            Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n)
              * Real.sqrt (Real.log (L n : ℝ)) :=
          le_of_mul_le_mul_right (le_trans hA hB) hYpos
        have hG_le : G v (π n (Fin.castLE (hL_le_p n) i)) ≤
            t2fun L β c_circ n * Real.rpow (Real.sqrt
              (Sig n (π n (Fin.castLE (hL_le_p n) i))
                (π n (Fin.castLE (hL_le_p n) i)))) (τ n) :=
          (div_le_iff₀ (Real.rpow_pos_of_pos hSpos (τ n))).mp hY
        have hmain : G v (π n (Fin.castLE (hL_le_p n) i)) ≤
            Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
              (π n (Fin.castLE (hL_le_p n) i))) * Real.sqrt (Real.log (L n : ℝ)) := by
          calc G v (π n (Fin.castLE (hL_le_p n) i))
              ≤ t2fun L β c_circ n * Real.rpow (Real.sqrt
                  (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) (τ n) := hG_le
            _ ≤ (Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n)
                  * Real.sqrt (Real.log (L n : ℝ)))
                  * Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) (τ n) :=
                mul_le_mul_of_nonneg_right hKey (Real.rpow_nonneg hSpos.le _)
            _ = Real.sqrt (Real.log (L n : ℝ))
                  * (Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                      (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n)
                    * Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                      (π n (Fin.castLE (hL_le_p n) i)))) (τ n)) := by ring
            _ = Real.sqrt (Real.log (L n : ℝ))
                  * Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) ((1 - τ n) + τ n) := by
                have hadd : Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) ((1 - τ n) + τ n)
                    = Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                        (π n (Fin.castLE (hL_le_p n) i)))) (1 - τ n)
                      * Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                        (π n (Fin.castLE (hL_le_p n) i)))) (τ n) :=
                  Real.rpow_add hSpos (1 - τ n) (τ n)
                rw [hadd]
            _ = Real.sqrt (Real.log (L n : ℝ))
                  * Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) 1 := by
                rw [show (1 - τ n) + τ n = 1 by ring]
            _ = Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                  (π n (Fin.castLE (hL_le_p n) i))) * Real.sqrt (Real.log (L n : ℝ)) := by
                have hrw1 : Real.rpow (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                    (π n (Fin.castLE (hL_le_p n) i)))) (1 : ℝ)
                    = Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i))
                      (π n (Fin.castLE (hL_le_p n) i))) := Real.rpow_one _
                rw [hrw1]
                ring
        rw [div_le_iff₀ hSpos]
        simpa only [mul_comm] using hmain
      intro i
      rw [hz v i]
      exact hzi i
    haveI : IsProbabilityMeasure P' :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability (p n)
    exact ENNReal.toReal_mono (measure_ne_top P' Gset) (measure_mono hsub)
  have hL_one : ∀ m : ℕ, 1 ≤ L m := by
    intro m
    have hpos : (0 : ℝ) < min (max 1 ((Real.log (m : ℝ)) ^ (3 : ℕ))) ((p m : ℝ)) := by
      refine lt_min (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_
      have hm : (1 : ℝ) ≤ (p m : ℝ) := by exact_mod_cast hp m
      linarith
    have h0 : 0 < L m := by
      rw [hL_def]
      exact Nat.ceil_pos.mpr hpos
    omega
  haveI : IsProbabilityMeasure P' :=
    Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.standardPi_probability (p n)
  have hmat : A * Sig n * A.transpose = corrMat p L Sig π hL_le_p n := by
    ext i j
    simp [A, corrMat, Matrix.mul_apply]
    try ring
  have hζcov : Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P' zeta
      (corrMat p L Sig π hL_le_p n) := by
    have hp_pos : 0 < p n := lt_of_lt_of_le zero_lt_one (hp n)
    have hbase :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_isCenteredGaussianVector
        hp_pos (Sig n) (hSig_psd n)
    have hlin :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.linearImage
        P' G (Sig n) hbase A
    rw [hmat] at hlin
    exact hlin
  have hcorrPSD : (corrMat p L Sig π hL_le_p n).PosSemidef := by
    rw [← hmat]
    have hAc : (A.transpose).conjTranspose = A := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same (hSig_psd n) A.transpose
    rwa [hAc] at h
  have hGcoord : ∀ (z : Fin (p n) → ℝ) (i : Fin (p n)),
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z i
        = ∑ j : Fin (p n), (CFC.sqrt (Sig n)) j i * z j := by
    intro z i
    have h :=
      Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector_linearCombination
        (Sig n) (hSig_psd n) (fun j : Fin (p n) => if j = i then (1 : ℝ) else 0) z
    have hsingle : ∑ k : Fin (p n), (if k = i then (1 : ℝ) else 0) *
        Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z k
        = Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    have hmid : ∑ j : Fin (p n),
        (CFC.sqrt (Sig n)).mulVec (fun k : Fin (p n) => if k = i then (1 : ℝ) else 0) j * z j
        = ∑ j : Fin (p n), (CFC.sqrt (Sig n)) j i * z j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hc : (CFC.sqrt (Sig n)).mulVec (fun k : Fin (p n) => if k = i then (1 : ℝ) else 0) j
          = (CFC.sqrt (Sig n)) j i := by
        change (∑ k : Fin (p n), (CFC.sqrt (Sig n)) j k * (if k = i then (1 : ℝ) else 0)) = _
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon
      rw [hc]
    rw [← hsingle, h, hmid]
  have hζmeas : Measurable zeta := by
    have hfun : zeta = fun z (i : Fin (L n)) =>
        ∑ j : Fin (p n), A i j * (∑ k : Fin (p n), (CFC.sqrt (Sig n)) k j * z k) := by
      funext z i
      change (∑ j : Fin (p n), A i j *
        Statlib.StatFoundation.RandomVariable.Gaussian.Slepian.canonicalGaussianVector (Sig n) z j) = _
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hGcoord z j]
    rw [hfun]
    refine measurable_pi_iff.mpr (fun i => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.const_mul (Finset.measurable_sum _ (fun k _ => ?_)) (A i j)
    exact measurable_const.mul (measurable_pi_apply k)
  have hζlaw : ∀ u : Fin (L n) → ℝ,
      Measure.map (fun ω => ∑ j : Fin (L n), u j * zeta ω j) P'
        = gaussianReal 0 (Real.toNNReal
            (∑ i : Fin (L n), ∑ j : Fin (L n),
              u i * u j * corrMat p L Sig π hL_le_p n i j)) := by
    intro u
    have hsum : (∑ i : Fin (L n), ∑ j : Fin (L n),
          u i * u j * corrMat p L Sig π hL_le_p n i j)
        = ∑ i : Fin (L n), ∑ j : Fin (L n),
            u i * corrMat p L Sig π hL_le_p n i j * u j := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    have hnn : (0 : ℝ) ≤ ∑ i : Fin (L n), ∑ j : Fin (L n),
        u i * u j * corrMat p L Sig π hL_le_p n i j := by
      have hdot := hcorrPSD.dotProduct_mulVec_nonneg u
      have hEq : star u ⬝ᵥ (corrMat p L Sig π hL_le_p n).mulVec u
          = ∑ i : Fin (L n), ∑ j : Fin (L n),
              u i * u j * corrMat p L Sig π hL_le_p n i j := by
        change (∑ i : Fin (L n), star (u i)
            * ∑ j : Fin (L n), corrMat p L Sig π hL_le_p n i j * u j) = _
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp
        try ring
      rwa [hEq] at hdot
    have h :=
      Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector.map_linearCombination
        P' zeta (corrMat p L Sig π hL_le_p n) hζcov hcorrPSD u
    rw [h]
    have harg : Real.toNNReal (∑ i : Fin (L n), ∑ j : Fin (L n),
        u i * u j * corrMat p L Sig π hL_le_p n i j)
        = ⟨∑ i : Fin (L n), ∑ j : Fin (L n),
            u i * corrMat p L Sig π hL_le_p n i j * u j,
            by rw [← hsum]; exact hnn⟩ := by
      rw [Real.toNNReal_of_nonneg hnn]
      exact Subtype.ext hsum
    rw [harg]
  have hGaussExp : (P' Gset).toReal ≤
      C' * Real.exp ((-(1 / 2) : ℝ) * (L n : ℝ) ^ ((1 : ℝ) / 3)) :=
    hC' p hp L hL_one hL_le_p Sig hSig_psd hSig_diag π hR_off hR_psd hR_sum
      n P' zeta hζcov
  have hExpPoly : C' * Real.exp ((-(1 / 2) : ℝ) * (L n : ℝ) ^ ((1 : ℝ) / 3))
      ≤ C' * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : (1 : ℕ) ≤ n := by omega
      exact_mod_cast h
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hknr : (k n : ℝ) < (p n : ℝ) := by exact_mod_cast hkn
    have hkmin :
        min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
          ((p n : ℝ)) ≤ (k n : ℝ) := by
      rw [hk_def]
      exact (Nat.ceil_le).mp le_rfl
    have hLmax : (L n : ℝ) < (p n : ℝ) := by
      have hLk' : (L n : ℝ) ≤
          min (max (L n : ℝ) (Real.rpow (n : ℝ) (1 / Real.rpow (Real.log (n : ℝ)) a)))
            ((p n : ℝ)) :=
        le_min (le_max_left _ _) (by exact_mod_cast hL_le_p n)
      exact lt_of_le_of_lt (le_trans hLk' hkmin) hknr
    have hmax_le : max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ)) ≤ (L n : ℝ) := by
      have hr_le : min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) ≤ (L n : ℝ) := by
        rw [hL_def]
        exact (Nat.ceil_le).mp le_rfl
      have hlt : min (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) ((p n : ℝ)) < (p n : ℝ) :=
        lt_of_le_of_lt hr_le hLmax
      have hle : max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ)) ≤ (p n : ℝ) := by
        by_contra hcon
        have h2 : (p n : ℝ) ≤ max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ)) := le_of_lt (not_le.mp hcon)
        rw [min_eq_right h2] at hlt
        exact absurd hlt (lt_irrefl _)
      have hLdef' : L n = Nat.ceil (max 1 ((Real.log (n : ℝ)) ^ (3 : ℕ))) := by
        rw [hL_def, min_eq_left hle]
      rw [hLdef']
      exact (Nat.ceil_le).mp le_rfl
    have hx3 : Real.rpow (Real.log (n : ℝ)) 3 ≤ (L n : ℝ) := by
      have h31 : (Real.log (n : ℝ)) ^ (3 : ℕ) ≤ (L n : ℝ) :=
        le_trans (le_max_right _ _) hmax_le
      calc Real.rpow (Real.log (n : ℝ)) 3 = (Real.log (n : ℝ)) ^ (3 : ℕ) :=
            Real.rpow_natCast (Real.log (n : ℝ)) 3
        _ ≤ (L n : ℝ) := h31
    have hlog_le : Real.log (n : ℝ) ≤ Real.rpow (L n : ℝ) ((1 : ℝ) / 3) := by
      have hcube : Real.rpow (Real.rpow (Real.log (n : ℝ)) 3) ((1 : ℝ) / 3)
          = Real.log (n : ℝ) := by
        calc Real.rpow (Real.rpow (Real.log (n : ℝ)) 3) ((1 : ℝ) / 3)
            = Real.rpow (Real.log (n : ℝ)) (3 * ((1 : ℝ) / 3)) :=
              (Real.rpow_mul hlog0 3 ((1 : ℝ) / 3)).symm
          _ = Real.rpow (Real.log (n : ℝ)) 1 := by
              rw [show (3 : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num]
          _ = Real.log (n : ℝ) := Real.rpow_one _
      rw [← hcube]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hlog0 3) hx3 (by norm_num)
    have harg : (-(1 / 2) : ℝ) * (L n : ℝ) ^ ((1 : ℝ) / 3)
        ≤ (-(1 / 2) : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonpos_left hlog_le (by norm_num)
    have hexp : Real.exp ((-(1 / 2) : ℝ) * (L n : ℝ) ^ ((1 : ℝ) / 3))
        ≤ Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
      have hrw : Real.rpow (n : ℝ) (-(1 / 2 : ℝ))
          = Real.exp (Real.log (n : ℝ) * (-(1 / 2 : ℝ))) :=
        Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hn1) _
      rw [hrw]
      refine Real.exp_le_exp.mpr ?_
      calc (-(1 / 2) : ℝ) * (L n : ℝ) ^ ((1 : ℝ) / 3)
          ≤ (-(1 / 2) : ℝ) * Real.log (n : ℝ) := harg
        _ = Real.log (n : ℝ) * (-(1 / 2) : ℝ) := by ring
    have hδ : Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) ≤ Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    exact mul_le_mul_of_nonneg_left (le_trans hexp hδ) hC'pos.le
  have hGauss : (P' Gset).toReal ≤ C' * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ) :=
    le_trans hGaussExp hExpPoly
  have hcomb : μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n)) ≤
      ENNReal.ofReal (C' * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)
        + cII * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) := by
    refine le_trans hTransfer ?_
    refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hShrink) le_rfl) ?_
    refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hGauss) le_rfl) ?_
    exact (ENNReal.ofReal_add
      (mul_nonneg hC'pos.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg hcIIpos.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))).symm.le
  calc μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n))
      ≤ ENNReal.ofReal (C' * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)
          + cII * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) := hcomb
    _ = ENNReal.ofReal ((C' + cII) * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)) := by
          rw [add_mul]
  /- @proof-region region.target-node.session.108754179e53fefb end -/

end

end Statlib.Imported

