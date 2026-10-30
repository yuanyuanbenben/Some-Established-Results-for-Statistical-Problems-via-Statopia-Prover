import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Vocabulary
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Base
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_1043829637_02d50666_07067a8c
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ProvedNodes.Node_2265874833_6a88c8f0_3447a9cc
import ProverJobs.job_paper_82217ff9ed45452ea25ea7588fe2ef01.ExternalNodes.Node_e7e3b4e2028d428ab478

namespace PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01


open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported
open _root_.PaperProofTasks.job_paper_82217ff9ed45452ea25ea7588fe2ef01.Statlib.Imported.Model

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Statlib.Imported
open _root_.Statlib
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1204950056_f3779bef : ∀ (a c0 alpha cvar ccirc eps0 Ccor : ℝ)
    (halpha : 0 < alpha) (hccirc : ccirc ∈ Set.Ioo (0 : ℝ) 1)
    (heps0 : eps0 ∈ Set.Ioo (0 : ℝ) 1) (hCcor : 0 < Ccor),
    ∃ CA : ℝ, 0 < CA ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        (M : Model Ω μ a) (hM : Model.Assumptions M c0 alpha cvar ccirc eps0 Ccor)
        (n : ℕ), 1 ≤ n →
          (M.tildeLaw n) {w : Fin (M.p n) → ℝ |
              fmax (M.J n (M.ell n)) (fun j => w j / (M.sigma n j)) ≤
                Real.sqrt (Real.log (M.ell n : ℝ))} ≤
            ENNReal.ofReal (CA * Real.exp (-(1 / 2 : ℝ) * (M.ell n : ℝ) ^ ((1 : ℝ) / 3))) := by
  /- @proof-region region.target-node.session.51e85359963d72d7 begin -/
  intro a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0 hCcor
  obtain ⟨CA, hCApos, hCAbound⟩ :=
    PaperProofTasks.job_paper_d731a49b3997405b944f72bca5b16eab.Statlib.Imported.paper_d731a49b3997405b944f72bca5b16eab
      eps0 heps0.1 heps0.2 Ccor hCcor
  refine ⟨CA, hCApos, ?_⟩
  intro Ω _ μ _ M hM n hn
  have hℓ : M.ell n ≤ M.p n := M.ell_le_p n
  haveI hprob : IsProbabilityMeasure (M.tildeLaw n) := by
    have hA : Measurable (fun w : Fin (M.p n) → ℝ =>
        Matrix.mulVec (Matrix.PosSemidef.sqrt (M.hSigma n)) w) := by
      apply measurable_pi_iff.mpr
      intro i
      show Measurable (fun w : Fin (M.p n) → ℝ =>
        ∑ j, (Matrix.PosSemidef.sqrt (M.hSigma n)) i j * w j)
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
    haveI hstd : IsProbabilityMeasure (stdGauss (M.p n)) := by
      unfold stdGauss
      infer_instance
    unfold Model.tildeLaw
    exact Measure.isProbabilityMeasure_map hA.aemeasurable
  let R : Matrix (Fin (M.ell n)) (Fin (M.ell n)) ℝ := M.corrMat n (M.ell n) hℓ
  let ζ : (Fin (M.p n) → ℝ) → Fin (M.ell n) → ℝ :=
    fun w i => w (M.g n (Fin.castLE hℓ i)) / M.sigma n (M.g n (Fin.castLE hℓ i))
  obtain ⟨hRsym, hRdiag, hRlaw, -, -, -⟩ :=
    statopia_math_node_1043829637_02d50666 a c0 alpha cvar ccirc eps0 Ccor M hM n hn hℓ
  have hone : (1 : ℕ) ≤ M.ell n := by
    have h1 : (1 : ℝ) ≤ min (max 1 ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ) := by
      apply le_min
      · exact le_max_left _ _
      · exact_mod_cast M.hp n
    have h2 : Nat.ceil (1 : ℝ) = 1 := by
      have hc : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
      rw [hc]
      exact Nat.ceil_natCast (R := ℝ) 1
    calc (1 : ℕ) = Nat.ceil (1 : ℝ) := h2.symm
      _ ≤ Nat.ceil (min (max 1 ((Real.log (n : ℝ)) ^ 3)) (M.p n : ℝ)) := Nat.ceil_mono h1
      _ = M.ell n := rfl
  have hS : R.IsSymm := by
    show Matrix.transpose R = R
    ext i j
    exact (hRsym i j).symm
  have hdiag : ∀ j : Fin (M.ell n), R j j = 1 := hRdiag
  obtain ⟨hposdef, hcG⟩ :=
    statopia_math_node_2265874833_6a88c8f0 a c0 alpha cvar ccirc eps0 Ccor halpha hccirc heps0 hCcor M hM n hn
  have hpsdmap : (R.map (fun x => max x 0)).PosSemidef := hM.hcorr_psd n
  have hoff : ∀ i j : Fin (M.ell n), i ≠ j → R i j ≤ 1 - eps0 := by
    intro i j hij
    exact hM.hcorr_max n (Fin.castLE hℓ i) (Fin.castLE hℓ j) i.isLt j.isLt
      (fun h => hij (Fin.castLE_injective hℓ h))
  have hsum : (∑ p : Fin (M.ell n) × Fin (M.ell n) with p.1 < p.2, max (R p.1 p.2) 0) ≤
      Ccor * (M.ell n : ℝ) := by
    have hsum_eq :
        (∑ p : Fin (M.ell n) × Fin (M.ell n) with p.1 < p.2, max (R p.1 p.2) 0)
          = ∑ q ∈ (Finset.univ : Finset (Fin (M.p n) × Fin (M.p n))).filter
              (fun q => (q.1 : ℕ) < M.ell n ∧ (q.2 : ℕ) < M.ell n ∧ q.1 < q.2),
              max (M.corrEntry n (M.g n q.1) (M.g n q.2)) 0 := by
      exact Finset.sum_nbij
        (fun p : Fin (M.ell n) × Fin (M.ell n) => (Fin.castLE hℓ p.1, Fin.castLE hℓ p.2))
        (fun a ha => by
          rw [Finset.mem_filter] at ha
          obtain ⟨-, ha_lt⟩ := ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.1.isLt, a.2.isLt, ha_lt⟩)
        (fun a _ b _ hab => by
          injection hab with h1 h2
          exact Prod.ext (Fin.castLE_injective hℓ h1) (Fin.castLE_injective hℓ h2))
        (fun b hb => by
          have hb' : b ∈ (Finset.univ : Finset (Fin (M.p n) × Fin (M.p n))).filter
              (fun q => (q.1 : ℕ) < M.ell n ∧ (q.2 : ℕ) < M.ell n ∧ q.1 < q.2) := hb
          rw [Finset.mem_filter] at hb'
          obtain ⟨-, hb1, hb2, hb_lt⟩ := hb'
          exact ⟨(⟨b.1.val, hb1⟩, ⟨b.2.val, hb2⟩),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_lt⟩,
            Prod.ext (Fin.ext rfl) (Fin.ext rfl)⟩)
        (fun a _ => rfl)
    rw [hsum_eq]
    exact hM.hcorr_sum n
  have hmain := hCAbound (Fin (M.p n) → ℝ) (M.tildeLaw n) (M.ell n) hone R
    hS hdiag hposdef hpsdmap hoff hsum ζ hcG
  have hset :
      {w : Fin (M.p n) → ℝ |
          fmax (M.J n (M.ell n)) (fun j => w j / M.sigma n j) ≤ Real.sqrt (Real.log (M.ell n : ℝ))}
        = {w : Fin (M.p n) → ℝ | ∀ i : Fin (M.ell n), ζ w i ≤ Real.sqrt (Real.log (M.ell n : ℝ))} := by
    ext w
    constructor
    · intro hfmax i
      have hmem : M.g n (Fin.castLE hℓ i) ∈ M.J n (M.ell n) := by
        show M.g n (Fin.castLE hℓ i) ∈
          ((Finset.univ : Finset (Fin (M.p n))).filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)).image (M.g n)
        exact Finset.mem_image.mpr
          ⟨Fin.castLE hℓ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
      have hbdd : BddAbove ((fun j : Fin (M.p n) => w j / M.sigma n j) '' (M.J n (M.ell n) : Set (Fin (M.p n)))) :=
        ((M.J n (M.ell n)).finite_toSet.image (fun j : Fin (M.p n) => w j / M.sigma n j)).bddAbove
      have hx_mem : (fun j : Fin (M.p n) => w j / M.sigma n j) (M.g n (Fin.castLE hℓ i)) ∈
          (fun j : Fin (M.p n) => w j / M.sigma n j) '' (M.J n (M.ell n) : Set (Fin (M.p n))) :=
        Set.mem_image_of_mem (fun j : Fin (M.p n) => w j / M.sigma n j) hmem
      exact le_trans (le_csSup hbdd hx_mem) hfmax
    · intro hall
      show sSup ((fun j : Fin (M.p n) => w j / M.sigma n j) '' (M.J n (M.ell n) : Set (Fin (M.p n)))) ≤
        Real.sqrt (Real.log (M.ell n : ℝ))
      apply Real.sSup_le
      · rintro x hx
        rw [Set.mem_image (fun j : Fin (M.p n) => w j / M.sigma n j) (M.J n (M.ell n) : Set (Fin (M.p n))) x] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        obtain ⟨i, hi, hgi⟩ :
            ∃ i ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)), M.g n i = j := by
          have hji : j ∈ (Finset.univ.filter (fun i : Fin (M.p n) => (i : ℕ) < M.ell n)).image (M.g n) := hj
          exact Finset.mem_image.mp hji
        rw [Finset.mem_filter] at hi
        obtain ⟨-, hi_lt⟩ := hi
        have hii : Fin.castLE hℓ ⟨i.val, hi_lt⟩ = i := Fin.ext (by simp)
        have hEq : ζ w ⟨i.val, hi_lt⟩ = w (M.g n i) / M.sigma n (M.g n i) := by
          show w (M.g n (Fin.castLE hℓ ⟨i.val, hi_lt⟩)) / M.sigma n (M.g n (Fin.castLE hℓ ⟨i.val, hi_lt⟩)) =
            w (M.g n i) / M.sigma n (M.g n i)
          rw [hii]
        rw [← hgi, ← hEq]
        exact hall ⟨i.val, hi_lt⟩
      · exact Real.sqrt_nonneg _
  rw [hset]
  have hle1 : (M.tildeLaw n) {w : Fin (M.p n) → ℝ | ∀ i : Fin (M.ell n), ζ w i ≤ Real.sqrt (Real.log (M.ell n : ℝ))} ≤ 1 := by
    rw [← measure_univ (μ := M.tildeLaw n)]
    exact measure_mono (Set.subset_univ _)
  have hne : (M.tildeLaw n) {w : Fin (M.p n) → ℝ | ∀ i : Fin (M.ell n), ζ w i ≤ Real.sqrt (Real.log (M.ell n : ℝ))} ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle1 (by simp))
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hmain
  /- @proof-region region.target-node.session.51e85359963d72d7 end -/

end
end Statlib.Imported

