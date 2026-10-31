import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Vocabulary
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.Base
import ProverJobs.job_paper_53e951f48c854f4db91e6ecda697ee2b.ProvedNodes.Node_204287509_2babc882_a5b3181d

namespace PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b

open Filter Topology MeasureTheory
open scoped Topology ENNReal
open _root_.PaperProofTasks.job_paper_53e951f48c854f4db91e6ecda697ee2b.Statlib.Imported

noncomputable section
open Filter Topology MeasureTheory
open scoped Topology ENNReal
namespace Statlib.Imported


set_option autoImplicit false in
theorem statopia_math_node_2675730550_7175d3dc : ∀ (d : ℕ) (U : HMCState d → ℝ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) (hL : 1 ≤ L) (δ : ℝ) (hδ : δ < 1)
    (h17 : ∀ M : ℝ, ∃ R : ℝ, ∀ x : HMCState d, R ≤ ‖x‖ → M ≤ ‖gradient U x‖ / ‖x‖),
    ∃ R : ℝ, ∀ x0 : HMCState d, R ≤ ‖x0‖ → ∀ p0 : HMCState d, ‖p0‖ ≤ ‖x0‖ ^ δ →
      (∀ i : ℕ, 1 ≤ i → i ≤ L →
        ‖leapfrogPosition U ε i x0 p0‖
          ≥ 3 * ‖leapfrogPosition U ε (i - 1) x0 p0‖) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ L →
        ‖leapfrogPosition U ε i x0 p0‖ ≥ (3 : ℝ) ^ i * ‖x0‖) ∧
      (∀ i : ℕ, i ≤ L → ‖leapfrogPosition U ε i x0 p0‖ ≥ ‖x0‖ ∧ R ≤ ‖x0‖) ∧
      ‖leapfrogPosition U ε L x0 p0‖ ≥ (3 : ℝ) ^ L * ‖x0‖ ∧
      (3 : ℝ) ^ L * ‖x0‖ ≥ (2 : ℝ) ^ L * ‖x0‖ := by
  /- @proof-region region.target-node.session.2d62eecba50e118f begin -/
  intro d U ε hε L hL δ hδ h17
  classical
  set M : ℝ := max ((8 + 2 * ε) / ε ^ 2) (16 / (3 * ε ^ 2)) with hM
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hMpos : 0 < M := by
    have hle : (8 + 2 * ε) / ε ^ 2 ≤ M := by rw [hM]; exact le_max_left _ _
    have hpos : 0 < (8 + 2 * ε) / ε ^ 2 := by positivity
    linarith
  have hb1 : 4 + ε ≤ ε ^ 2 / 2 * M := by
    have hle : (8 + 2 * ε) / ε ^ 2 ≤ M := by rw [hM]; exact le_max_left _ _
    have hm := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2)
    have heq : ε ^ 2 / 2 * ((8 + 2 * ε) / ε ^ 2) = 4 + ε := by field_simp; ring
    linarith [hm, heq]
  have hb2 : 16 / 3 ≤ ε ^ 2 * M := by
    have hle : 16 / (3 * ε ^ 2) ≤ M := by rw [hM]; exact le_max_right _ _
    have hm := mul_le_mul_of_nonneg_left hle (le_of_lt hε2)
    have heq : ε ^ 2 * (16 / (3 * ε ^ 2)) = 16 / 3 := by field_simp
    linarith [hm, heq]
  obtain ⟨R₁, hR₁⟩ := h17 M
  refine ⟨max R₁ 1, ?_⟩
  intro x0 hx0 p0 hp0
  have hx0R1 : R₁ ≤ ‖x0‖ := le_trans (le_max_left _ _) hx0
  have hx01 : (1 : ℝ) ≤ ‖x0‖ := le_trans (le_max_right _ _) hx0
  have hgrad : ∀ x : HMCState d, R₁ ≤ ‖x‖ → M * ‖x‖ ≤ ‖gradient U x‖ := by
    intro x hx
    have hxne : ‖x‖ ≠ 0 := by
      intro h
      have hx' : R₁ ≤ ‖x‖ := hx
      rw [h] at hx'
      have hle := hR₁ x hx
      have hratio : ‖gradient U x‖ / ‖x‖ = 0 := by rw [h, div_zero]
      rw [hratio] at hle
      linarith
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxne)
    have hcancel : (‖gradient U x‖ / ‖x‖) * ‖x‖ = ‖gradient U x‖ := by field_simp
    calc M * ‖x‖ ≤ (‖gradient U x‖ / ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hR₁ x hx) (le_of_lt hxpos)
      _ = ‖gradient U x‖ := hcancel
  have hp0le : ‖p0‖ ≤ ‖x0‖ := by
    calc ‖p0‖ ≤ ‖x0‖ ^ δ := hp0
      _ ≤ ‖x0‖ := Real.rpow_le_self_of_one_le hx01 (le_of_lt hδ)
  let X : ℕ → HMCState d := fun i => leapfrogPosition U ε i x0 p0
  let Pm : ℕ → HMCState d := fun i => leapfrogMomentum U ε i x0 p0
  let Q : ℕ → HMCState d := fun i => Pm i - (ε / 2) • gradient U (X i)
  have hX0 : X 0 = x0 := by simp [X, leapfrogPosition]
  have hP0 : Pm 0 = p0 := by simp [Pm, leapfrogMomentum]
  obtain ⟨h1, _h2, h3, _h4, _h5, _h6, _h7⟩ := statopia_math_node_204287509_2babc882 d U ε hε L hL x0 p0
  have hstep1 : ∀ i, X (i + 1) = X i + ε • Q i := fun i => h1 i
  have hstep3 : ∀ i, Q (i + 1) = Q i - ε • gradient U (X (i + 1)) := fun i => h3 i
  have hx1 : X 1 = x0 + ε • p0 - (ε ^ 2 / 2) • gradient U x0 := by
    have h := hstep1 0
    rw [Nat.zero_add, hX0] at h
    have hQ0 : Q 0 = p0 - (ε / 2) • gradient U x0 := by
      show Pm 0 - (ε / 2) • gradient U (X 0) = p0 - (ε / 2) • gradient U x0
      rw [hP0, hX0]
    rw [hQ0] at h
    rw [h]
    rw [smul_sub, smul_smul]
    have hs : ε * (ε / 2) = ε ^ 2 / 2 := by ring
    rw [hs]
    abel
  have hstep0 : ‖X 1‖ ≥ 3 * ‖X 0‖ := by
    have hcancel : (ε ^ 2 / 2) • gradient U x0 = x0 + ε • p0 - X 1 := by
      rw [hx1]; abel
    have htri : ‖x0 + ε • p0 - X 1‖ ≤ ‖x0‖ + ε * ‖p0‖ + ‖X 1‖ := by
      have a1 : ‖x0 + ε • p0 - X 1‖ ≤ ‖x0 + ε • p0‖ + ‖X 1‖ := norm_sub_le _ _
      have a2 : ‖x0 + ε • p0‖ ≤ ‖x0‖ + ε * ‖p0‖ := by
        have hh := norm_add_le x0 (ε • p0)
        rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at hh
      linarith
    have hgtri : (ε ^ 2 / 2) * ‖gradient U x0‖ ≤ ‖x0‖ + ε * ‖p0‖ + ‖X 1‖ := by
      have hgg : ‖(ε ^ 2 / 2) • gradient U x0‖ = (ε ^ 2 / 2) * ‖gradient U x0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2 / 2)]
      rw [← hgg, hcancel]
      exact htri
    have hg0 : M * ‖x0‖ ≤ ‖gradient U x0‖ := hgrad x0 hx0R1
    have hg0' : ε ^ 2 / 2 * (M * ‖x0‖) ≤ ε ^ 2 / 2 * ‖gradient U x0‖ :=
      mul_le_mul_of_nonneg_left hg0 (by positivity)
    have hb1' : (4 + ε) * ‖x0‖ ≤ (ε ^ 2 / 2 * M) * ‖x0‖ :=
      mul_le_mul_of_nonneg_right hb1 (norm_nonneg x0)
    have hp0b : ε * ‖p0‖ ≤ ε * ‖x0‖ := mul_le_mul_of_nonneg_left hp0le (le_of_lt hε)
    rw [hX0]
    nlinarith [hgtri, hg0', hb1', hp0b, norm_nonneg x0, norm_nonneg (X 1)]
  have hrec : ∀ n, 1 ≤ n → X (n + 1) = X n + X n - X (n - 1) - ε ^ 2 • gradient U (X n) := by
    intro n hn
    have h1n : X (n + 1) = X n + ε • Q n := hstep1 n
    have h3n : Q n = Q (n - 1) - ε • gradient U (X n) := by
      have hh := hstep3 (n - 1)
      rwa [Nat.sub_add_cancel hn] at hh
    have h1m : X n = X (n - 1) + ε • Q (n - 1) := by
      have hh := hstep1 (n - 1)
      rwa [Nat.sub_add_cancel hn] at hh
    have hq : ε • Q (n - 1) = X n - X (n - 1) := by rw [h1m]; abel
    rw [h1n, h3n, smul_sub, hq, smul_smul, pow_two]
    abel
  have hstepN : ∀ n, 1 ≤ n → M * ‖X n‖ ≤ ‖gradient U (X n)‖ →
      ‖X (n - 1)‖ ≤ ‖X n‖ / 3 → ‖X (n + 1)‖ ≥ 3 * ‖X n‖ := by
    intro n hn hgn hprev
    have hrecn := hrec n hn
    have hg_eq : ε ^ 2 • gradient U (X n) = X n + X n - X (n - 1) - X (n + 1) := by
      rw [hrecn]; abel
    have h1 : ‖X n + X n - X (n - 1) - X (n + 1)‖ ≤ 2 * ‖X n‖ + ‖X (n - 1)‖ + ‖X (n + 1)‖ := by
      have a1 : ‖X n + X n - X (n - 1) - X (n + 1)‖ ≤ ‖X n + X n - X (n - 1)‖ + ‖X (n + 1)‖ := norm_sub_le _ _
      have a2 : ‖X n + X n - X (n - 1)‖ ≤ ‖X n + X n‖ + ‖X (n - 1)‖ := norm_sub_le _ _
      have a3 : ‖X n + X n‖ ≤ ‖X n‖ + ‖X n‖ := norm_add_le _ _
      linarith
    have h2 : ‖ε ^ 2 • gradient U (X n)‖ = ε ^ 2 * ‖gradient U (X n)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε2]
    have hbound : ε ^ 2 * ‖gradient U (X n)‖ ≤ 2 * ‖X n‖ + ‖X (n - 1)‖ + ‖X (n + 1)‖ := by
      rw [← h2, hg_eq]
      exact h1
    have hgn' : ε ^ 2 * (M * ‖X n‖) ≤ ε ^ 2 * ‖gradient U (X n)‖ :=
      mul_le_mul_of_nonneg_left hgn (le_of_lt hε2)
    have hb2' : 16 / 3 * ‖X n‖ ≤ (ε ^ 2 * M) * ‖X n‖ :=
      mul_le_mul_of_nonneg_right hb2 (norm_nonneg (X n))
    have hchain : 16 / 3 * ‖X n‖ ≤ 2 * ‖X n‖ + ‖X (n - 1)‖ + ‖X (n + 1)‖ := by
      calc 16 / 3 * ‖X n‖ ≤ (ε ^ 2 * M) * ‖X n‖ := hb2'
        _ = ε ^ 2 * (M * ‖X n‖) := by ring
        _ ≤ ε ^ 2 * ‖gradient U (X n)‖ := hgn'
        _ ≤ 2 * ‖X n‖ + ‖X (n - 1)‖ + ‖X (n + 1)‖ := hbound
    linarith
  have hpow3 : ∀ k : ℕ, (1 : ℝ) ≤ (3 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ m ih =>
      change (1 : ℝ) ≤ (3 : ℝ) ^ (m + 1)
      rw [pow_succ]
      have h3m : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (3 : ℝ) ^ m * 1 := mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ (3 : ℝ) ^ m * 3 := mul_le_mul_of_nonneg_left (by norm_num) h3m
  have hkey : ∀ n, n ≤ L →
      ((∀ j, 1 ≤ j → j ≤ n → ‖X j‖ ≥ 3 * ‖X (j - 1)‖) ∧ ‖X n‖ ≥ (3 : ℝ) ^ n * ‖x0‖) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · intro j hj1 hj0
        exfalso
        omega
      · simp [hX0]
    | succ n ih =>
      intro hnL
      have hPn := ih (by omega : n ≤ L)
      obtain ⟨hA, hB⟩ := hPn
      have hstep : ‖X (n + 1)‖ ≥ 3 * ‖X n‖ := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          simpa using hstep0
        · have hR1n : R₁ ≤ ‖X n‖ := by
            have h3n : (1 : ℝ) ≤ (3 : ℝ) ^ n := hpow3 n
            have hnn : (0 : ℝ) ≤ ‖x0‖ := norm_nonneg x0
            calc R₁ ≤ ‖x0‖ := hx0R1
              _ ≤ (3 : ℝ) ^ n * ‖x0‖ := by nlinarith [h3n, hnn]
              _ ≤ ‖X n‖ := hB
          have hgradn : M * ‖X n‖ ≤ ‖gradient U (X n)‖ := hgrad (X n) hR1n
          have hprevn : ‖X (n - 1)‖ ≤ ‖X n‖ / 3 := by
            have hAn : ‖X n‖ ≥ 3 * ‖X (n - 1)‖ := hA n hnpos le_rfl
            linarith
          exact hstepN n hnpos hgradn hprevn
      refine ⟨?_, ?_⟩
      · intro j hj1 hjn1
        rcases lt_or_ge n j with hlt | hge
        · have hjn : j = n + 1 := by omega
          subst hjn
          simpa using hstep
        · exact hA j hj1 hge
      · calc ‖X (n + 1)‖ ≥ 3 * ‖X n‖ := hstep
          _ ≥ 3 * ((3 : ℝ) ^ n * ‖x0‖) := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 3)
          _ = (3 : ℝ) ^ (n + 1) * ‖x0‖ := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hiL
    exact (hkey i hiL).1 i hi1 le_rfl
  · intro i hi1 hiL
    exact (hkey i hiL).2
  · intro i hiL
    refine ⟨?_, hx0⟩
    show ‖X i‖ ≥ ‖x0‖
    have h3i : (1 : ℝ) ≤ (3 : ℝ) ^ i := hpow3 i
    have hB := (hkey i hiL).2
    have hnn : (0 : ℝ) ≤ ‖x0‖ := norm_nonneg x0
    calc ‖X i‖ ≥ (3 : ℝ) ^ i * ‖x0‖ := hB
      _ ≥ ‖x0‖ := by simpa using mul_le_mul_of_nonneg_right h3i hnn
  · exact (hkey L le_rfl).2
  · have h23 : ∀ k : ℕ, (2 : ℝ) ^ k ≤ (3 : ℝ) ^ k := by
      intro k
      induction k with
      | zero => norm_num
      | succ m ih =>
        change (2 : ℝ) ^ (m + 1) ≤ (3 : ℝ) ^ (m + 1)
        rw [pow_succ, pow_succ]
        have h3m : (0 : ℝ) ≤ (3 : ℝ) ^ m := by positivity
        calc (2 : ℝ) ^ m * 2 ≤ (3 : ℝ) ^ m * 2 := mul_le_mul_of_nonneg_right ih (by norm_num)
          _ ≤ (3 : ℝ) ^ m * 3 := mul_le_mul_of_nonneg_left (by norm_num) h3m
    exact mul_le_mul_of_nonneg_right (h23 L) (norm_nonneg x0)
  /- @proof-region region.target-node.session.2d62eecba50e118f end -/

end Statlib.Imported
end

