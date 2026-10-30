import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ProvedNodes
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported
noncomputable section

theorem paper_cb04ce35a04d48a9bf96750470ca0eb0
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (α : ℝ) (hα : 0 < α)
    (C_sigma : ℝ) (hC_sigma : 0 < C_sigma)
    (c_circ : ℝ) (hc_circ0 : 0 < c_circ) (hc_circ1 : c_circ < 1)
    (ε0 : ℝ) (hε0_0 : 0 < ε0) (hε0_1 : ε0 < 1)
    (C_R : ℝ) (hC_R : 0 < C_R)
    (c_0 : ℝ) (hc_0 : 0 < c_0) :
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
      (∃ c_thr : ℝ, 0 < c_thr ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N₂ : ℕ, 1 ≤ N₂ ∧
        ∀ n : ℕ, N₂ ≤ n →
          μ (Bevent p X μv Sig τ k π n (t1fun k β c_thr n)) ≤
            ENNReal.ofReal (C₂ * Real.rpow (n : ℝ) (-1))) ∧
      (∃ N₁ : ℕ, 1 ≤ N₁ ∧
        ∀ n : ℕ, N₁ ≤ n → k n < p n →
          μ (Aevent p X μv Sig τ k π n (t2fun L β c_circ n)) ≤
            ENNReal.ofReal (C₁ * Real.rpow (n : ℝ) (-(1 / 2 : ℝ) + δ)))
:= by
  /- @proof-region region.root.dc21b4b813f5 begin -/
  obtain ⟨C₁, hC₁_pos, hA⟩ :=
    statopia_math_node_2629403716_8043891e δ hδ0 hδ1 a ha0 ha1 α hα C_sigma hC_sigma
      c_circ hc_circ0 hc_circ1 ε0 hε0_0 hε0_1 C_R hC_R c_0 hc_0
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro _ _ _ _ p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem
    hZ_meas hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def
    τ hτ0 hτ1 β hβ_def hτ_cond hσ_upper hσ_lower hR_off hR_psd hR_sum
  refine ⟨?_, ?_⟩
  · exact statopia_math_node_1547769943_b198a36d δ hδ0 hδ1 a ha0 ha1 α hα C_sigma hC_sigma
      c_circ hc_circ0 hc_circ1 ε0 hε0_0 hε0_1 C_R hC_R c_0 hc_0
      p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem
      hZ_meas hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def
      τ hτ0 hτ1 β hβ_def hτ_cond hσ_upper hσ_lower hR_off hR_psd hR_sum
  
  · exact hA p hp Sig hSig_psd hSig_diag π hπ_sorted Z μv X hX_model hX_mean hX_mem
      hZ_meas hZ_indep hZ_ident hZ_mem hZ_mean hZ_cov hZ_psi L hL_def hL_le_p k hk_def
      τ hτ0 hτ1 β hβ_def hτ_cond hσ_upper hσ_lower hR_off hR_psd hR_sum
  /- @proof-region region.root.dc21b4b813f5 end -/

end

end Statlib.Imported

-- Paper root revision dfdc11fd-fc5e-4d67-b686-1b8cd046344b
