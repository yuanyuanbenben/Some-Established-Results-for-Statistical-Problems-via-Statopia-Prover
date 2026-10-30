import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Vocabulary
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Base
import ProverJobs.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.ExternalNodes.Node_79d648e6c4a5423390cc

namespace PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open _root_.PaperProofTasks.job_paper_cb04ce35a04d48a9bf96750470ca0eb0.Statlib.Imported

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace Statlib.Imported

noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1614795123_3bc3bd18 : ∀ (eps0 : ℝ) (h_eps0_pos : 0 < eps0) (h_eps0_lt_one : eps0 < 1)
    (C_R : ℝ) (hC_R : 0 < C_R),
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (p : ℕ → ℕ) (hp : ∀ n : ℕ, 1 ≤ p n)
        (L : ℕ → ℕ) (hL_pos : ∀ n : ℕ, 1 ≤ L n) (hL_le_p : ∀ n : ℕ, L n ≤ p n)
        (Sig : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ)
        (hSig_psd : ∀ n : ℕ, (Sig n).PosSemidef)
        (hSig_diag : ∀ (n : ℕ) (j : Fin (p n)), 0 < Sig n j j)
        (pi : (n : ℕ) → Equiv.Perm (Fin (p n)))
        (hR_off : ∀ (n : ℕ) (i j : Fin (L n)), i ≠ j →
          corrMat p L Sig pi hL_le_p n i j ≤ 1 - eps0)
        (hR_psd : ∀ n : ℕ, (posPartMat (corrMat p L Sig pi hL_le_p n)).PosSemidef)
        (hR_sum : ∀ n : ℕ, ∑ i : Fin (L n), ∑ j : Fin (L n),
          (if i < j then max (corrMat p L Sig pi hL_le_p n i j) 0 else 0)
            ≤ C_R * (L n : ℝ)),
        ∀ (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

          (zeta : Ω → Fin (L n) → ℝ),
          (Statlib.StatFoundation.RandomVariable.Gaussian.IsCenteredGaussianVector P zeta
            (corrMat p L Sig pi hL_le_p n)) →
          (P {ω : Ω | ∀ i : Fin (L n), zeta ω i ≤ Real.sqrt (Real.log (L n : ℝ))}).toReal ≤
            C' * Real.exp ((-(1 / 2) : ℝ) * Real.rpow (L n : ℝ) (1 / 3)) := by
  /- @proof-region region.target-node.session.94be0e5a7138c61e begin -/
  intro eps0 heps0_pos heps0_lt_one C_R hC_R
  obtain ⟨C', hC'_pos, hC'_bound⟩ :=
    PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported.paper_d731a49b3997405b944f72bca5b16eab
      eps0 heps0_pos heps0_lt_one C_R hC_R
  refine ⟨C', hC'_pos, ?_⟩
  intro p hp L hL_pos hL_le_p Sig hSig_psd hSig_diag π hR_off hR_psd hR_sum n Ω instΩ P instP zeta hζ
  have hR_symm : (corrMat p L Sig π hL_le_p n).IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    simp only [corrMat]
    have hs : Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) i))
        = Sig n (π n (Fin.castLE (hL_le_p n) i)) (π n (Fin.castLE (hL_le_p n) j)) := by
      have hh := Matrix.PosSemidef.isHermitian (hSig_psd n)
      have h2 := hh.apply (π n (Fin.castLE (hL_le_p n) i)) (π n (Fin.castLE (hL_le_p n) j))
      simpa using h2
    have hD : Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j))) *
          Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i)) (π n (Fin.castLE (hL_le_p n) i)))
        = Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i)) (π n (Fin.castLE (hL_le_p n) i))) *
          Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j))) :=
      mul_comm _ _
    rw [hs, hD]
  have hR_diag : ∀ j : Fin (L n), corrMat p L Sig π hL_le_p n j j = 1 := by
    intro j
    simp only [corrMat]
    have hpos : 0 < Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j)) :=
      hSig_diag n _
    have hden : Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j))) *
        Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j)))
        = Sig n (π n (Fin.castLE (hL_le_p n) j)) (π n (Fin.castLE (hL_le_p n) j)) := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hpos)]
    rw [hden]
    exact div_self (ne_of_gt hpos)
  have hR_psdR : (corrMat p L Sig π hL_le_p n).PosSemidef := by
    have hM : ((Sig n).submatrix (fun i => π n (Fin.castLE (hL_le_p n) i)) (fun i => π n (Fin.castLE (hL_le_p n) i))).PosSemidef :=
      (hSig_psd n).submatrix (fun i => π n (Fin.castLE (hL_le_p n) i))
    have hD := hM.conjTranspose_mul_mul_same
      (fun i j : Fin (L n) => if i = j then (Real.sqrt (Sig n (π n (Fin.castLE (hL_le_p n) i)) (π n (Fin.castLE (hL_le_p n) i))))⁻¹ else 0)
    convert hD using 1
    ext i j
    simp only [corrMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, star_trivial]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [if_neg hk, mul_zero]) (by simp)]
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [if_neg hl, zero_mul]) (by simp)]
    rw [if_pos rfl]
    rw [div_eq_mul_inv, mul_inv]
    ring
  exact hC'_bound Ω P (L n) (hL_pos n) (corrMat p L Sig π hL_le_p n) hR_symm hR_diag hR_psdR
    (hR_psd n) (hR_off n)
    (by rw [Finset.sum_filter, Fintype.sum_prod_type]; exact hR_sum n) zeta hζ
  /- @proof-region region.target-node.session.94be0e5a7138c61e end -/

end

end Statlib.Imported

