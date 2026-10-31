import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Vocabulary
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
import ProverJobs.manual_dp_cons_finish_20261031.WindowMass
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_3968451938_9cda8590_a46b8445
open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_921397988_70fc5704 : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (thetaStar : Fin t → ℝ) (m U : ℝ)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ x : ℝ, g x ∂volume = 1)
    (hq0_meas : Measurable q0)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_int : ∫ θ : ℝ, q0 θ ∂volume = 1)
    (hT3 : ∀ j : Fin t, ∀ y ∈ Set.Icc (0 : ℝ) (2 * c),
      q0 (thetaStar j + y) + q0 (thetaStar j - y) ≤ U)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (hm : 0 < m) (hU : 0 < U)
    (hcm : 2 * c * m ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (lab : Fin n → Fin t),
    let G : Fin t → ℝ → ℝ := fun l θ =>
      ∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - θ) ∂volume
    let w : Finset (Fin n) → ℝ := fun B =>
      ((B.card - 1).factorial : ℝ) *
        ∫ θ : ℝ,
          (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ ∂volume
    ∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty → (∀ i ∈ B, lab i = l) →
      w B ≤ (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ∧
      (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ≤
        (U / m) * ((B.card.factorial : ℝ) / ((B.card : ℝ) ^ 2)) := by
  /- @proof-region region.target-node.session.ffd8a7b25aa46cf1 begin -/
  intro t ht c hc g q0 thetaStar m U hg_meas hg_nonneg hg_zero hg_lower hg_int
    hq0_meas hq0_nonneg hq0_int hT3 hsep hm hU hcm n hn lab
  intro G w B l hB hsub
  have ha1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hprod : ∀ θ : ℝ,
      (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) = (G l θ) ^ B.card := by
    intro θ
    have hk : ∀ l' ∈ (Finset.univ : Finset (Fin t)), l' ≠ l →
        (G l' θ) ^ (B.filter (fun i => lab i = l')).card = 1 := by
      intro b _ hb
      have hfilt : B.filter (fun i => lab i = b) = ∅ :=
        Finset.filter_false_of_mem (fun i hi => by rw [hsub i hi]; exact Ne.symm hb)
      simp [hfilt]
    have hmain := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin t)))
      (f := fun l' => (G l' θ) ^ (B.filter (fun i => lab i = l')).card) (a := l) hk
      (fun h => (h (Finset.mem_univ l)).elim)
    rw [hmain]
    simp only [Finset.filter_true_of_mem hsub]
  have hw1 : w B = ((B.card - 1).factorial : ℝ) *
      (∫ θ, (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ ∂volume) :=
    rfl
  rw [hw1]
  have hw2 : (∫ θ, (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ ∂volume)
      = ∫ θ, (G l θ) ^ B.card * q0 θ ∂volume := by
    simp only [hprod]
  rw [hw2]
  constructor
  · have hwin : ∀ θ : ℝ, 0 ≤ G l θ ∧ G l θ ≤ max 0 (1 - m * |θ - thetaStar l|) ∧
        (2 * c ≤ |θ - thetaStar l| → G l θ = 0) := by
      intro θ
      exact statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm
        hg_meas hg_nonneg hg_zero hg_lower hg_int l θ
    have hE := statopia_math_node_3968451938_9cda8590 c m U hc hm hU B.card ha1
      (thetaStar l) (G l) q0 (fun θ => (hwin θ).1) (fun θ => (hwin θ).2.1)
      (fun θ hθ => (hwin θ).2.2 hθ) hq0_nonneg (fun y hy => hT3 l y hy) hcm
    calc ((B.card - 1).factorial : ℝ) * ∫ θ, (G l θ) ^ B.card * q0 θ ∂volume
        ≤ ((B.card - 1).factorial : ℝ) * (U / (m * ((B.card : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) := by
          have hbc : (1:ℝ) ≤ (B.card : ℝ) := by exact_mod_cast ha1
          have hm0 : m ≠ 0 := ne_of_gt hm
          have hk0 : ((B.card : ℝ) + 1) ≠ 0 := ne_of_gt (by linarith)
          have hk1 : m * ((B.card : ℝ) + 1) ≠ 0 := mul_ne_zero hm0 hk0
          field_simp
  · have hA : (0:ℝ) ≤ ((B.card - 1).factorial : ℝ) := by positivity
    have hcard : 0 < B.card := lt_of_lt_of_le Nat.zero_lt_one ha1
    have haf : (0:ℝ) < (B.card : ℝ) := by exact_mod_cast hcard
    have haf0 : (B.card : ℝ) ≠ 0 := ne_of_gt haf
    have hsq0 : (B.card : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 haf0
    have haf1 : (0:ℝ) < (B.card : ℝ) + 1 := by linarith
    have haf10 : (B.card : ℝ) + 1 ≠ 0 := ne_of_gt haf1
    have hUpos : 0 < U / m := div_pos hU hm
    have hfac : (B.card.factorial : ℝ) = (B.card : ℝ) * ((B.card - 1).factorial : ℝ) := by
      obtain ⟨k, hk⟩ : ∃ k, B.card = k + 1 := ⟨B.card - 1, by omega⟩
      rw [hk, Nat.factorial_succ]
      push_cast
      simp
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hUpos)
    rw [hfac]
    rw [← sub_nonneg]
    have hd : (B.card : ℝ) * ((B.card - 1).factorial : ℝ) / (B.card : ℝ) ^ 2
        - ((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)
        = ((B.card - 1).factorial : ℝ) * (B.card : ℝ)
            / ((B.card : ℝ) ^ 2 * ((B.card : ℝ) + 1)) := by
      field_simp <;> ring
    rw [hd]
    positivity
  /- @proof-region region.target-node.session.ffd8a7b25aa46cf1 end -/

end

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_921397988_70fc5704
