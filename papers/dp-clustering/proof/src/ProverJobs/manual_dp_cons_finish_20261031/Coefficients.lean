import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Vocabulary
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_1209751647_2591ad5a_a2d27e60
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2358914211_b4f8e1dc_5ae14418
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2588147038_c72f539f_bf0a8a81
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_2617779308_f5c0b9ed_355a9ee0
open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1865983872_fc33fb01 : ∀ (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) (lab : Fin n → Fin t)
    (E : Finset (Finset (Fin t))) (hE : ∀ e ∈ E, e.card = 2)
    (lam kappa : ℝ) (hlam : 0 < lam) (hkappa_nonneg : 0 ≤ kappa)
    (hkappa_lt : kappa < 1)
    (w : Finset (Fin n) → ℝ)
    (hw_nonneg : ∀ B : Finset (Fin n), B.Nonempty → 0 ≤ w B)
    (hpure : ∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) →
      w B ≤ lam * ((B.card.factorial : ℝ) / ((B.card : ℝ)) ^ 2))
    (hcross : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      ({l, k} : Finset (Fin t)) ∈ E → B.Nonempty →
      B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
            (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) →
      (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty →
      (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty →
      w B / (((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card.factorial : ℝ) *
             ((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card.factorial : ℝ))
        ≤ kappa ^ ((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card +
                   (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card) /
          (((B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card +
            (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).card : ℕ) : ℝ))
    (hother : ∀ B : Finset (Fin n), B.Nonempty →
      (∀ l : Fin t, ¬ B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)) →
      (∀ (l k : Fin t), l ≠ k → ({l, k} : Finset (Fin t)) ∈ E →
        ¬ (B ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l) ∪
              (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k) ∧
           (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).Nonempty ∧
           (B ∩ (Finset.univ : Finset (Fin n)).filter (fun i => lab i = k)).Nonempty)) →
      w B = 0)
    (hnclass : ∀ l : Fin t,
      1 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card)
    (C0 H B0 K5 : ℝ)
    (hC0 : C0 = max 1 (8 * dpZetaTwo))
    (hH : H = max 1 (⨆ a : Set.Ici (1 : ℝ),
      (a : ℝ) ^ ((3 : ℝ) / 2) * kappa ^ (a : ℝ)))
    (hB0 : B0 = C0 * H)
    (hK5 : K5 = max 1 (B0 * ((t : ℝ) * lam + B0 * (E.card : ℝ) / 2))),
    1 ≤ B0 ∧ 0 < K5 ∧
      ∀ k : ℕ, 1 ≤ k →
        (∑ A ∈ dpTau n k, ∏ B ∈ A, w B) ≤
          (∏ l : Fin t,
              ((((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card.factorial : ℝ)) /
              ((((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card : ℝ) ^ 2)) *
            K5 ^ k / (k.factorial : ℝ) := by
  /- @proof-region region.target-node.session.509875d34fbb2c17 begin -/
  intro t ht n hn lab E hE lam kappa hlam hkappa_nonneg hkappa_lt w hw_nonneg hpure hcross
    hother hnclass C0 H B0 K5 hC0def hHdef hB0def hK5def
  have hC0ge : (1 : ℝ) ≤ C0 := by rw [hC0def]; exact le_max_left _ _
  have hHge : (1 : ℝ) ≤ H := by rw [hHdef]; exact le_max_left _ _
  have hB0ge : (1 : ℝ) ≤ B0 := by rw [hB0def]; nlinarith
  have hB0pos : (0 : ℝ) < B0 := lt_of_lt_of_le zero_lt_one hB0ge
  have hEcard : (0 : ℝ) ≤ (E.card : ℝ) := by positivity
  have hK5pos : (0 : ℝ) < K5 := by
    rw [hK5def]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK5main : B0 * ((t : ℝ) * lam + B0 * (E.card : ℝ) / 2) ≤ K5 := by
    rw [hK5def]
    exact le_max_right _ _
  refine ⟨hB0ge, hK5pos, ?_⟩
  intro k hk
  have hS : ∀ M : ℕ, (∑ b ∈ Finset.range M, (1:ℝ) / (((b : ℝ) + 1) ^ 2)) ≤ 2 - 1 / (M : ℝ) := by
    intro M
    induction M with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      cases N with
      | zero => norm_num
      | succ m =>
        push_cast
        have ih' : (∑ b ∈ Finset.range (m + 1), (1:ℝ) / (((b : ℝ) + 1) ^ 2))
            ≤ 2 - 1 / ((m : ℝ) + 1) := by
          simpa using ih
        have hkey : (1:ℝ) / (((m : ℝ) + 1) + 1) ^ 2
            ≤ 1 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) + 1) := by
          have h1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
          have h2 : (0:ℝ) < ((m : ℝ) + 1) + 1 := by positivity
          field_simp
          nlinarith
        linarith
  have hpartial : ∀ N : ℕ, 3 ≤ N →
      (5:ℝ)/4 ≤ ∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) ^ 2) := by
    intro N hN
    refine Nat.le_induction ?_ ?_ N hN
    · norm_num [Finset.sum_range_succ]
    · intro m hm ih
      rw [Finset.sum_range_succ]
      have hnn : (0:ℝ) ≤ (1:ℝ) / ((m : ℝ) ^ 2) := by positivity
      linarith
  have hU4 : ∀ N : ℕ, 4 ≤ N →
      (∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) ^ 2)) ≤ 2 - 2 / ((N : ℝ) + 1) := by
    intro N hN
    refine Nat.le_induction ?_ ?_ N hN
    · norm_num [Finset.sum_range_succ]
    · intro m hm ih
      rw [Finset.sum_range_succ]
      push_cast
      have hm4 : (4:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hkey : (1:ℝ) / ((m : ℝ) ^ 2) ≤ 2 / ((m : ℝ) + 1) - 2 / (((m : ℝ) + 1) + 1) := by
        have hm1 : (0:ℝ) < (m:ℝ) := by linarith
        field_simp
        nlinarith
      linarith
  have hU : ∀ N : ℕ, (∑ i ∈ Finset.range N, (1:ℝ) / ((i : ℝ) ^ 2)) ≤ 2 := by
    intro N
    rcases lt_or_ge N 4 with h | h
    · interval_cases N <;> norm_num [Finset.sum_range_succ]
    · have h4 := hU4 N h
      have hpos : (0:ℝ) ≤ 2 / ((N : ℝ) + 1) := by positivity
      linarith
  have hsumm : Summable (fun i : ℕ => (1:ℝ) / ((i : ℝ) ^ 2)) :=
    summable_of_sum_range_le (fun i => by positivity) hU
  have hzeta : (5:ℝ)/4 ≤ dpZetaTwo := by
    have htend : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (1:ℝ) / ((i : ℝ) ^ 2))
        atTop (𝓝 dpZetaTwo) :=
      hsumm.hasSum.tendsto_sum_nat
    have hev : ∀ᶠ m : ℕ in atTop, (5:ℝ)/4 ≤ ∑ i ∈ Finset.range m, (1:ℝ) / ((i : ℝ) ^ 2) :=
      eventually_atTop.2 ⟨3, fun m hm => hpartial m hm⟩
    exact le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (5:ℝ)/4) atTop (𝓝 ((5:ℝ)/4))) htend hev
  have hC0nine : (9:ℝ) ≤ C0 := by
    have h8 : 8 * dpZetaTwo ≤ C0 := by
      rw [hC0def]
      exact le_max_right _ _
    linarith
  set PHI : ℕ → ℝ := fun a => if a = 0 then (1:ℝ) else ((a.factorial : ℝ) / ((a : ℝ) ^ 2)) with hPHI
  have hPHI_nonneg : ∀ a : ℕ, 0 ≤ PHI a := by
    intro a
    simp only [hPHI]
    split_ifs with h
    · norm_num
    · positivity
  have hkap : ∀ p : ℕ, 1 ≤ p → kappa ^ p / Real.sqrt ((p : ℝ)) ≤ H / ((p : ℝ) ^ 2) := by
    intro p hp
    have hp0 : (0:ℝ) < (p:ℝ) := by
      have h1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have hs : (0:ℝ) < Real.sqrt ((p:ℝ)) := Real.sqrt_pos.2 hp0
    have hs2 : Real.sqrt ((p:ℝ)) * Real.sqrt ((p:ℝ)) = (p:ℝ) := Real.mul_self_sqrt (le_of_lt hp0)
    have hsup : ((p:ℝ)) ^ ((3:ℝ)/2) * kappa ^ ((p:ℝ)) ≤ H := by
      have hsb := statopia_math_node_2617779308_f5c0b9ed kappa hkappa_nonneg hkappa_lt
        (⨆ a : Set.Ici (1 : ℝ), (a : ℝ) ^ ((3 : ℝ) / 2) * kappa ^ (a : ℝ)) rfl p hp
      rw [hHdef]
      exact le_trans hsb (le_max_right _ _)
    have hpow : ((p:ℝ)) ^ ((3:ℝ)/2) = (p:ℝ) * Real.sqrt ((p:ℝ)) := by
      rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hp0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hkappow : kappa ^ ((p:ℝ)) = kappa ^ p := Real.rpow_natCast kappa p
    have hkey : (p:ℝ) * Real.sqrt ((p:ℝ)) * kappa ^ p ≤ H := by
      rw [← hpow, ← hkappow]
      exact hsup
    have h2 : (p:ℝ) * Real.sqrt ((p:ℝ)) * kappa ^ p * Real.sqrt ((p:ℝ))
        ≤ H * Real.sqrt ((p:ℝ)) :=
      mul_le_mul_of_nonneg_right hkey (le_of_lt hs)
    have h4 : (p:ℝ) * (Real.sqrt ((p:ℝ)) * Real.sqrt ((p:ℝ))) * kappa ^ p
        ≤ H * Real.sqrt ((p:ℝ)) := by
      calc (p:ℝ) * (Real.sqrt ((p:ℝ)) * Real.sqrt ((p:ℝ))) * kappa ^ p
          = (p:ℝ) * Real.sqrt ((p:ℝ)) * kappa ^ p * Real.sqrt ((p:ℝ)) := by ring
        _ ≤ H * Real.sqrt ((p:ℝ)) := h2
    rw [hs2] at h4
    have hden : (0:ℝ) < Real.sqrt ((p:ℝ)) * (p:ℝ)^2 := mul_pos hs (by positivity)
    have e1 : kappa ^ p / Real.sqrt ((p:ℝ))
        = (kappa ^ p * (p:ℝ)^2) / (Real.sqrt ((p:ℝ)) * (p:ℝ)^2) := by
      field_simp
    have e2 : H / ((p:ℝ)^2)
        = (H * Real.sqrt ((p:ℝ))) / (Real.sqrt ((p:ℝ)) * (p:ℝ)^2) := by
      field_simp
    rw [e1, e2, div_le_iff₀ hden]
    have hcancel : (H * Real.sqrt ((p:ℝ))) / (Real.sqrt ((p:ℝ)) * (p:ℝ)^2)
        * (Real.sqrt ((p:ℝ)) * (p:ℝ)^2) = H * Real.sqrt ((p:ℝ)) := by
      field_simp
    rw [hcancel]
    nlinarith [h4]
  have hconv : ∀ m : ℕ, 2 ≤ m →
      (∑ a ∈ Finset.range m, (1:ℝ) / (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))) ≤ 8 / ((m:ℝ)^2) := by
    intro m hm
    have hmpos : (0:ℝ) < (m:ℝ) := by
      have h2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      linarith
    have hrefl : (∑ a ∈ Finset.range m, (1:ℝ) / (((m:ℝ) - (a:ℝ))^2)) ≤ 2 := by
      have heq : (∑ a ∈ Finset.range m, (1:ℝ) / (((m:ℝ) - (a:ℝ))^2))
          = ∑ c ∈ Finset.range m, (1:ℝ) / (((c:ℝ) + 1)^2) := by
        refine Finset.sum_bij (fun a _ => m - 1 - a) ?_ ?_ ?_ ?_
        · intro a ha
          simp only [Finset.mem_range] at ha ⊢
          omega
        · intro a1 ha1 a2 ha2 h
          simp only [Finset.mem_range] at ha1 ha2
          have h' : m - 1 - a1 = m - 1 - a2 := h
          omega
        · intro b hb
          simp only [Finset.mem_range] at hb
          have hlt : m - 1 - b ∈ Finset.range m := by
            simp only [Finset.mem_range]
            omega
          refine ⟨m - 1 - b, hlt, ?_⟩
          show m - 1 - (m - 1 - b) = b
          omega
        · intro a ha
          simp only [Finset.mem_range] at ha
          have harith : ((m - 1 - a : ℕ) : ℝ) + 1 = (m:ℝ) - (a:ℝ) := by
            have h1 : ((m - a : ℕ) : ℝ) = (m:ℝ) - (a:ℝ) := by
              rw [Nat.cast_sub (le_of_lt ha)]
            have h2 : m - 1 - a + 1 = m - a := by omega
            rw [← h1, ← h2]
            push_cast
            ring
          rw [harith]
      rw [heq]
      have h1 : (∑ c ∈ Finset.range m, (1:ℝ) / (((c:ℝ) + 1)^2)) ≤ 2 - 1 / (m:ℝ) := hS m
      have h2 : (0:ℝ) ≤ 1 / (m:ℝ) := div_nonneg (by norm_num) (le_of_lt hmpos)
      linarith
    have hterm : ∀ a ∈ Finset.range m,
        (m:ℝ)^2 / (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))
          ≤ 2 / ((a:ℝ)^2) + 2 / (((m:ℝ) - (a:ℝ))^2) := by
      intro a ha
      simp only [Finset.mem_range] at ha
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        simp only [Nat.cast_zero]
        have hL : ((m:ℝ)^2) / (((0:ℝ)^2) * (((m:ℝ) - (0:ℝ))^2)) = 0 := by simp
        rw [hL]
        have hp1 : (0:ℝ) ≤ 2 / ((0:ℝ)^2) := by simp
        have hp2 : (0:ℝ) ≤ 2 / (((m:ℝ) - (0:ℝ))^2) :=
          div_nonneg (by norm_num) (by positivity)
        linarith
      · have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast hpos
        have hbR : (0:ℝ) < (m:ℝ) - (a:ℝ) := by
          have hlt : (a:ℝ) < (m:ℝ) := by exact_mod_cast ha
          linarith
        have ha2 : (0:ℝ) < (a:ℝ)^2 := pow_pos haR 2
        have hb2 : (0:ℝ) < ((m:ℝ) - (a:ℝ))^2 := pow_pos hbR 2
        have hden : (0:ℝ) < ((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2) := mul_pos ha2 hb2
        rw [div_le_iff₀ hden]
        have hkey : (m:ℝ)^2 ≤ 2 * (((m:ℝ) - (a:ℝ))^2 + (a:ℝ)^2) := by
          nlinarith [sq_nonneg ((m:ℝ) - 2*(a:ℝ))]
        have hexp : (2 / ((a:ℝ)^2) + 2 / (((m:ℝ) - (a:ℝ))^2))
            * (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))
            = 2 * (((m:ℝ) - (a:ℝ))^2) + 2 * ((a:ℝ)^2) := by
          field_simp
        rw [hexp]
        linarith
    rw [le_div_iff₀ (pow_pos hmpos 2)]
    have hmul : (∑ a ∈ Finset.range m, (1:ℝ) / (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))) * (m:ℝ)^2
        = ∑ a ∈ Finset.range m, ((m:ℝ)^2 / (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a ha => by ring)
    rw [hmul]
    have hsum1 : (∑ a ∈ Finset.range m, (1:ℝ) / ((a:ℝ)^2)) ≤ 2 := hU m
    calc (∑ a ∈ Finset.range m, ((m:ℝ)^2 / (((a:ℝ)^2) * (((m:ℝ) - (a:ℝ))^2))))
        ≤ ∑ a ∈ Finset.range m, (2 / ((a:ℝ)^2) + 2 / (((m:ℝ) - (a:ℝ))^2)) := Finset.sum_le_sum hterm
      _ = ∑ a ∈ Finset.range m,
            (2 * ((1:ℝ) / ((a:ℝ)^2)) + 2 * ((1:ℝ) / (((m:ℝ) - (a:ℝ))^2))) :=
          Finset.sum_congr rfl (fun a ha => by ring)
      _ = 2 * (∑ a ∈ Finset.range m, (1:ℝ) / ((a:ℝ)^2))
            + 2 * (∑ a ∈ Finset.range m, (1:ℝ) / (((m:ℝ) - (a:ℝ))^2)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * 2 + 2 * 2 := by linarith [hsum1, hrefl]
      _ = 8 := by norm_num
  have hblock : ∀ S : Finset (Fin n),
      (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
          w B * ∏ l : Fin t, PHI (((S \ B).filter (fun i => lab i = l)).card))
        ≤ (∏ l : Fin t, PHI ((S.filter (fun i => lab i = l)).card)) * K5 := by
    intro S
    have h := statopia_math_node_1209751647_2591ad5a t ht n lab E hE lam kappa hlam hkappa_nonneg
      hkappa_lt w hw_nonneg hpure hcross hother C0 H B0 K5 hC0nine hHge hB0def hkap hconv hK5main S
    simpa only [hPHI] using h
  have hpeel : ∀ (S : Finset (Fin n)) (j : ℕ), 1 ≤ j →
      (∑ f ∈ (Finset.univ : Finset (Fin j → Finset (Fin n))).filter (fun f =>
          (∀ i : Fin j, (f i).Nonempty) ∧
          (∀ i : Fin j, f i ⊆ S) ∧
          (∀ i : Fin j, ∀ i' : Fin j, i ≠ i' → Disjoint (f i) (f i')) ∧
          (∀ x ∈ S, ∃ i : Fin j, x ∈ f i)),
        ∏ i : Fin j, w (f i))
      = ∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
          w B * (∑ g ∈ (Finset.univ : Finset (Fin (j - 1) → Finset (Fin n))).filter (fun g =>
            (∀ i : Fin (j - 1), (g i).Nonempty) ∧
            (∀ i : Fin (j - 1), g i ⊆ S \ B) ∧
            (∀ i : Fin (j - 1), ∀ i' : Fin (j - 1), i ≠ i' → Disjoint (g i) (g i')) ∧
            (∀ x ∈ S \ B, ∃ i : Fin (j - 1), x ∈ g i)),
          ∏ i : Fin (j - 1), w (g i)) := by
    intro S j hj
    exact statopia_math_node_2358914211_b4f8e1dc n w S j hj
  have hTTbound : ∀ (j : ℕ) (S : Finset (Fin n)),
      (∑ f ∈ (Finset.univ : Finset (Fin j → Finset (Fin n))).filter (fun f =>
          (∀ i : Fin j, (f i).Nonempty) ∧
          (∀ i : Fin j, f i ⊆ S) ∧
          (∀ i : Fin j, ∀ i' : Fin j, i ≠ i' → Disjoint (f i) (f i')) ∧
          (∀ x ∈ S, ∃ i : Fin j, x ∈ f i)),
        ∏ i : Fin j, w (f i))
        ≤ (∏ l : Fin t, PHI ((S.filter (fun i => lab i = l)).card)) * K5 ^ j := by
    intro j
    induction j with
    | zero =>
      intro S
      rw [pow_zero, mul_one]
      set F : Finset (Fin 0 → Finset (Fin n)) := (Finset.univ : Finset (Fin 0 → Finset (Fin n))).filter (fun f =>
          (∀ i : Fin 0, (f i).Nonempty) ∧
          (∀ i : Fin 0, f i ⊆ S) ∧
          (∀ i : Fin 0, ∀ i' : Fin 0, i ≠ i' → Disjoint (f i) (f i')) ∧
          (∀ x ∈ S, ∃ i : Fin 0, x ∈ f i)) with hF
      have hL : (∑ f ∈ F, ∏ i : Fin 0, w (f i)) = (F.card : ℝ) := by
        have h1 : ∀ f ∈ F, ∏ i : Fin 0, w (f i) = (1:ℝ) := fun f hf => by simp
        rw [Finset.sum_congr rfl h1]
        simp
      rw [hL]
      rcases Finset.eq_empty_or_nonempty S with hS | hS
      · rw [hS]
        have hprod1 : (∏ l : Fin t, PHI (((∅ : Finset (Fin n)).filter (fun i => lab i = l)).card)) = 1 := by
          refine Finset.prod_eq_one (fun l _ => ?_)
          have hc : (((∅ : Finset (Fin n)).filter (fun i => lab i = l)).card) = 0 := by simp
          rw [hc, hPHI]
          simp
        rw [hprod1]
        have hcard1 : F.card ≤ 1 := by
          have hle : F.card ≤ (Finset.univ : Finset (Fin 0 → Finset (Fin n))).card := by
            rw [hF]
            exact Finset.card_le_card (Finset.filter_subset _ _)
          have h1 : (Finset.univ : Finset (Fin 0 → Finset (Fin n))).card = 1 := by simp
          omega
        have hcast : ((F.card : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcard1
        simp only [Nat.cast_one] at hcast
        exact hcast
      · have hFempty : F = ∅ := by
          rw [hF]
          ext f
          constructor
          · intro hf
            obtain ⟨-, hP⟩ := Finset.mem_filter.1 hf
            obtain ⟨x, hx⟩ := hS
            obtain ⟨i, hi⟩ := hP.2.2.2 x hx
            exact Fin.elim0 i
          · intro hf
            exact absurd hf (by simp)
        rw [hFempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact Finset.prod_nonneg (fun l _ => hPHI_nonneg _)
    | succ j ih =>
      intro S
      rw [hpeel S (j + 1) (by omega)]
      have hstep : (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
            w B * (∑ g ∈ (Finset.univ : Finset (Fin ((j + 1) - 1) → Finset (Fin n))).filter (fun g =>
              (∀ i : Fin ((j + 1) - 1), (g i).Nonempty) ∧
              (∀ i : Fin ((j + 1) - 1), g i ⊆ S \ B) ∧
              (∀ i : Fin ((j + 1) - 1), ∀ i' : Fin ((j + 1) - 1), i ≠ i' → Disjoint (g i) (g i')) ∧
              (∀ x ∈ S \ B, ∃ i : Fin ((j + 1) - 1), x ∈ g i)),
            ∏ i : Fin ((j + 1) - 1), w (g i)))
          ≤ (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
            w B * ((∏ l : Fin t, PHI (((S \ B).filter (fun i => lab i = l)).card)) * K5 ^ j)) := by
        refine Finset.sum_le_sum ?_
        intro B hB
        have hnon : B.Nonempty := (Finset.mem_filter.1 hB).2.1
        have hsub : (j + 1) - 1 = j := by omega
        rw [hsub]
        exact mul_le_mul_of_nonneg_left (ih (S \ B)) (hw_nonneg B hnon)
      refine le_trans hstep ?_
      have hfactor : (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
            w B * ((∏ l : Fin t, PHI (((S \ B).filter (fun i => lab i = l)).card)) * K5 ^ j))
          = (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
            w B * ∏ l : Fin t, PHI (((S \ B).filter (fun i => lab i = l)).card)) * K5 ^ j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun B hB => (mul_assoc _ _ _).symm)
      rw [hfactor]
      calc (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => B.Nonempty ∧ B ⊆ S),
            w B * ∏ l : Fin t, PHI (((S \ B).filter (fun i => lab i = l)).card)) * K5 ^ j
          ≤ ((∏ l : Fin t, PHI ((S.filter (fun i => lab i = l)).card)) * K5) * K5 ^ j :=
            mul_le_mul_of_nonneg_right (hblock S) (pow_nonneg (le_of_lt hK5pos) j)
        _ = (∏ l : Fin t, PHI ((S.filter (fun i => lab i = l)).card)) * K5 ^ (j + 1) := by
            rw [pow_succ]
            ring
  have hkfact := statopia_math_node_2588147038_c72f539f n k w
  have hbound := hTTbound k (Finset.univ : Finset (Fin n))
  rw [hkfact] at hbound
  have hPHIval : ∀ a : ℕ, a ≠ 0 → PHI a = ((a.factorial : ℝ) / ((a : ℝ) ^ 2)) := by
    intro a ha
    rw [hPHI]
    exact if_neg ha
  have hprod : (∏ l : Fin t, PHI (((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card))
      = ∏ l : Fin t,
          ((((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card.factorial : ℝ) /
           ((((Finset.univ : Finset (Fin n)).filter (fun i => lab i = l)).card : ℝ) ^ 2)) :=
    Finset.prod_congr rfl (fun l _ => hPHIval _ (by
      have hl := hnclass l
      omega))
  rw [hprod] at hbound
  have hkpos : (0:ℝ) < (k.factorial : ℝ) := by
    have h : (0:ℕ) < k.factorial := Nat.factorial_pos k
    exact_mod_cast h
  rw [div_eq_mul_inv]
  have h := mul_le_mul_of_nonneg_right hbound (le_of_lt (inv_pos.mpr hkpos))
  have hleft : ((k.factorial : ℝ) * (∑ A ∈ dpTau n k, ∏ B ∈ A, w B)) * (k.factorial : ℝ)⁻¹
      = (∑ A ∈ dpTau n k, ∏ B ∈ A, w B) := by
    rw [mul_comm (k.factorial : ℝ) (∑ A ∈ dpTau n k, ∏ B ∈ A, w B), mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hkpos), mul_one]
  rw [hleft] at h
  exact h
  /- @proof-region region.target-node.session.509875d34fbb2c17 end -/

end

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_1865983872_fc33fb01
