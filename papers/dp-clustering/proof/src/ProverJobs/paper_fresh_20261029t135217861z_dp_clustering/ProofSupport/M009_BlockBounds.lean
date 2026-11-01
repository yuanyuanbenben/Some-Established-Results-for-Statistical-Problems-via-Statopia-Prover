import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M000_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M001_Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M003_WindowMass
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M006_CrossBlocks
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M008_PureBlocks

/- Original module ProverJobs.manual_dp_cons_finish_20261031.BlockBounds; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_1011772921_00d6fbb2 : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g q0 : ℝ → ℝ) (thetaStar : Fin t → ℝ) (m U : ℝ)
    (hm : 0 < m) (hU : 0 < U)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ x : ℝ, g x ∂volume = 1)
    (hq0_meas : Measurable q0)
    (hq0_nonneg : ∀ θ : ℝ, 0 ≤ q0 θ)
    (hq0_int : ∫ θ : ℝ, q0 θ ∂volume = 1)
    (hT3 : ∀ j : Fin t, ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) (2 * c) →
      q0 (thetaStar j + y) + q0 (thetaStar j - y) ≤ U)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|),
    2 * c * m ≤ 1 ∧
    (0 ≤ dpKappa c m thetaStar ∧ dpKappa c m thetaStar < 1) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (lab : Fin n → Fin t),
      let G : Fin t → ℝ → ℝ := fun l θ =>
        ∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - θ) ∂volume
      let w : Finset (Fin n) → ℝ := fun B =>
        ((B.card - 1).factorial : ℝ) *
          ∫ θ, (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ
            ∂volume
      (∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty → (∀ i ∈ B, lab i = l) →
        w B ≤ (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ∧
        (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ≤
          (U / m) * ((B.card.factorial : ℝ) / ((B.card : ℝ) ^ 2))) ∧
      (∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
        (B.filter (fun i => lab i = l)).Nonempty →
        (B.filter (fun i => lab i = k)).Nonempty →
        (∀ i ∈ B, lab i = l ∨ lab i = k) →
        (let p : ℕ := (B.filter (fun i => lab i = l)).card
         let q : ℕ := (B.filter (fun i => lab i = k)).card
         w B ≤ (dpKappa c m thetaStar) ^ (p + q) * ((p + q - 1).factorial : ℝ) *
             (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
             (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) ∧
         w B / ((p.factorial : ℝ) * (q.factorial : ℝ)) ≤
             (dpKappa c m thetaStar) ^ (p + q) / ((p + q : ℕ) : ℝ))) ∧
      (∀ (B : Finset (Fin n)), 3 ≤ (B.image lab).card → w B = 0) ∧
      (∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
        (B.filter (fun i => lab i = l)).Nonempty →
        (B.filter (fun i => lab i = k)).Nonempty →
        (∀ i ∈ B, lab i = l ∨ lab i = k) →
        4 * c ≤ |thetaStar l - thetaStar k| → w B = 0)) := by
  /- @proof-region region.target-node.session.bfac555b7597a6df begin -/
  intro t ht c hc g q0 thetaStar m U hm hU hg_meas hg_nonneg hg_zero hg_lower hg_int
    hq0_meas hq0_nonneg hq0_int hT3 hsep
  classical
  let G : Fin t → ℝ → ℝ :=
    fun l θ => ∫ x in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - θ)
  let Eord : Finset (Fin t × Fin t) :=
    Finset.univ.filter (fun jk : Fin t × Fin t =>
      jk.1 ≠ jk.2 ∧ |thetaStar jk.1 - thetaStar jk.2| < 4 * c)
  let kappa : ℝ :=
    if h : Eord.Nonempty then
      Eord.sup' h (fun jk => 1 - m * (|thetaStar jk.1 - thetaStar jk.2| - 2 * c))
    else 0
  have hA : 2 * c * m ≤ 1 := by
    have hg_intble : Integrable g volume := by
      by_contra h
      rw [MeasureTheory.integral_undef h] at hg_int
      norm_num at hg_int
    have hvol : volume.real (Set.Icc (-c) c) = 2 * c := by
      simp only [MeasureTheory.Measure.real]
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    have hconst : ∫ x in Set.Icc (-c) c, (m : ℝ) ∂volume = 2 * c * m := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    have hnonneg_ind : ∀ x : ℝ, (0 : ℝ) ≤ (Set.Icc (-c) c).indicator (fun _ : ℝ => m) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (-c) c
      · rw [Set.indicator_of_mem hx]
        exact hm.le
      · rw [Set.indicator_of_notMem hx]
    have hpt : ∀ x : ℝ, (Set.Icc (-c) c).indicator (fun _ : ℝ => m) x ≤ g x := by
      intro x
      by_cases hx : x ∈ Set.Icc (-c) c
      · rw [Set.indicator_of_mem hx]
        exact hg_lower x hx
      · rw [Set.indicator_of_notMem hx]
        exact hg_nonneg x
    have hmono : ∫ x : ℝ, (Set.Icc (-c) c).indicator (fun _ : ℝ => m) x ∂volume ≤
        ∫ x : ℝ, g x ∂volume :=
      MeasureTheory.integral_mono_of_nonneg
        (f := (Set.Icc (-c) c).indicator (fun _ : ℝ => m)) (g := g)
        (Filter.Eventually.of_forall hnonneg_ind) hg_intble
        (Filter.Eventually.of_forall hpt)
    have hind : ∫ x : ℝ, (Set.Icc (-c) c).indicator (fun _ : ℝ => m) x ∂volume = 2 * c * m := by
      rw [MeasureTheory.integral_indicator (f := fun _ : ℝ => m) measurableSet_Icc, hconst]
    calc 2 * c * m = ∫ x : ℝ, (Set.Icc (-c) c).indicator (fun _ : ℝ => m) x ∂volume :=
          hind.symm
      _ ≤ ∫ x : ℝ, g x ∂volume := hmono
      _ = 1 := hg_int
  have hEord_mem : ∀ jk : Fin t × Fin t, jk ∈ Eord ↔
      (jk.1 ≠ jk.2 ∧ |thetaStar jk.1 - thetaStar jk.2| < 4 * c) := by
    intro jk
    show jk ∈ (Finset.univ.filter (fun jk : Fin t × Fin t =>
      jk.1 ≠ jk.2 ∧ |thetaStar jk.1 - thetaStar jk.2| < 4 * c)) ↔
      (jk.1 ≠ jk.2 ∧ |thetaStar jk.1 - thetaStar jk.2| < 4 * c)
    simp
  have hkappa_def : kappa = if h : Eord.Nonempty then
      Eord.sup' h (fun jk => 1 - m * (|thetaStar jk.1 - thetaStar jk.2| - 2 * c)) else 0 := rfl
  have hB : 0 ≤ kappa := by
    rw [hkappa_def]
    by_cases h : Eord.Nonempty
    · obtain ⟨jk, hjk⟩ := h
      rw [dif_pos ⟨jk, hjk⟩]
      refine le_trans ?_ (Finset.le_sup' (fun jk : Fin t × Fin t =>
        1 - m * (|thetaStar jk.1 - thetaStar jk.2| - 2 * c)) hjk)
      have hmem := (hEord_mem jk).mp hjk
      have h1 : |thetaStar jk.1 - thetaStar jk.2| - 2 * c < 2 * c := by linarith [hmem.2]
      have h2 : m * (|thetaStar jk.1 - thetaStar jk.2| - 2 * c) < m * (2 * c) :=
        mul_lt_mul_of_pos_left h1 hm
      nlinarith [h2, hA]
    · simp [dif_neg h]
  have hC : kappa < 1 := by
    rw [hkappa_def]
    by_cases h : Eord.Nonempty
    · rw [dif_pos h, Finset.sup'_lt_iff]
      intro jk hjk
      have hmem := (hEord_mem jk).mp hjk
      have hpos : 0 < |thetaStar jk.1 - thetaStar jk.2| - 2 * c := by
        linarith [hsep jk.1 jk.2 hmem.1]
      nlinarith [mul_pos hm hpos]
    · simp only [dif_neg h]
      norm_num
  have hg_intble : Integrable g volume := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hg_int
    norm_num at hg_int
  have hG_nonneg : ∀ (l : Fin t) (θ : ℝ), 0 ≤ G l θ := by
    intro l θ
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => hg_nonneg (x - θ))
  have hG_bound : ∀ (l : Fin t) (θ : ℝ), G l θ ≤ max 0 (1 - m * |θ - thetaStar l|) := by
    intro l θ
    exact (statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm hg_meas hg_nonneg
      hg_zero hg_lower hg_int l θ).2.1
  have hG_supp : ∀ (l : Fin t) (θ : ℝ), 2 * c ≤ |θ - thetaStar l| → G l θ = 0 := by
    intro l θ h
    exact (statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm hg_meas hg_nonneg
      hg_zero hg_lower hg_int l θ).2.2 h
  have hBd : 0 ≤ dpKappa c m thetaStar := hB
  have hCd : dpKappa c m thetaStar < 1 := hC
  have hUdiv : 0 < U / m := div_pos hU hm
  refine ⟨hA, ⟨hBd, hCd⟩, ?_⟩
  intro n hn lab
  let w : Finset (Fin n) → ℝ :=
    fun B => ((B.card - 1).factorial : ℝ) *
      ∫ θ : ℝ, (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ ∂volume
  have hD : ∀ B : Finset (Fin n), B.Nonempty → 0 ≤ w B := by
    intro B _
    have hprod : ∀ θ : ℝ,
        0 ≤ (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ := by
      intro θ
      exact mul_nonneg (Finset.prod_nonneg (fun l _ => pow_nonneg (hG_nonneg l θ) _))
        (hq0_nonneg θ)
    have hint : 0 ≤ ∫ θ : ℝ,
        (∏ l : Fin t, (G l θ) ^ (B.filter (fun i => lab i = l)).card) * q0 θ ∂volume :=
      MeasureTheory.integral_nonneg hprod
    exact mul_nonneg (Nat.cast_nonneg _) hint
  have hE : ∀ (B : Finset (Fin n)) (l : Fin t), B.Nonempty → (∀ i ∈ B, lab i = l) →
      w B ≤ (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ∧
      (U / m) * (((B.card - 1).factorial : ℝ) / ((B.card : ℝ) + 1)) ≤
        (U / m) * ((B.card.factorial : ℝ) / ((B.card : ℝ) ^ 2)) :=
    statopia_math_node_921397988_70fc5704 t ht c hc g q0 thetaStar m U hg_meas hg_nonneg
      hg_zero hg_lower hg_int hq0_meas hq0_nonneg hq0_int hT3 hsep hm hU hA n hn lab
  have hF : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      (B.filter (fun i => lab i = l)).Nonempty →
      (B.filter (fun i => lab i = k)).Nonempty →
      (∀ i ∈ B, lab i = l ∨ lab i = k) →
      let p := (B.filter (fun i => lab i = l)).card
      let q := (B.filter (fun i => lab i = k)).card
      w B ≤ (dpKappa c m thetaStar) ^ (p + q) * ((p + q - 1).factorial : ℝ) *
          (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p) *
          (((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) ∧
        w B / ((p.factorial : ℝ) * (q.factorial : ℝ)) ≤
          (dpKappa c m thetaStar) ^ (p + q) / ((p + q : ℕ) : ℝ) :=
    fun B l k hlk hBl hBk hB =>
      statopia_math_node_3703788458_48052a86 t ht c hc g q0 thetaStar m U hm hU hg_meas
        hg_nonneg hg_zero hg_lower hg_int hq0_meas hq0_nonneg hq0_int hT3 hsep hA n hn lab
        B l k hlk hBl hBk hB
  have three_pt : ∀ x1 x2 x3 : ℝ, |x1| < 2 * c → |x2| < 2 * c → |x3| < 2 * c →
      2 * c < |x1 - x2| → 2 * c < |x2 - x3| → 2 * c < |x1 - x3| → False := by
    intro x1 x2 x3 h1 h2 h3 h12 h23 h13
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    have key : ∀ u v : ℝ, -(2 * c) < u → u < 2 * c → -(2 * c) < v → v < 2 * c →
        ((0 ≤ u ∧ 0 ≤ v) ∨ (u < 0 ∧ v < 0)) → |u - v| < 2 * c := by
      intro u v ua ub va vb hs
      rw [abs_lt]
      rcases hs with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · constructor <;> linarith
      · constructor <;> linarith
    by_cases s1 : 0 ≤ x1
    · by_cases s2 : 0 ≤ x2
      · have := key x1 x2 h1a h1b h2a h2b (Or.inl ⟨s1, s2⟩)
        linarith
      · push_neg at s2
        by_cases s3 : 0 ≤ x3
        · have := key x1 x3 h1a h1b h3a h3b (Or.inl ⟨s1, s3⟩)
          linarith
        · push_neg at s3
          have := key x2 x3 h2a h2b h3a h3b (Or.inr ⟨s2, s3⟩)
          linarith
    · push_neg at s1
      by_cases s2 : 0 ≤ x2
      · by_cases s3 : 0 ≤ x3
        · have := key x2 x3 h2a h2b h3a h3b (Or.inl ⟨s2, s3⟩)
          linarith
        · push_neg at s3
          have := key x1 x3 h1a h1b h3a h3b (Or.inr ⟨s1, s3⟩)
          linarith
      · push_neg at s2
        have := key x1 x2 h1a h1b h2a h2b (Or.inr ⟨s1, s2⟩)
        linarith
  have hG_pos_supp : ∀ (l : Fin t) (θ : ℝ), 0 < G l θ → |θ - thetaStar l| < 2 * c := by
    intro l θ h
    by_contra hcon
    push_neg at hcon
    exact absurd (hG_supp l θ hcon) (ne_of_gt h)
  have hG : ∀ (B : Finset (Fin n)),
      3 ≤ ((Finset.univ : Finset (Fin t)).filter
            (fun l => (B.filter (fun i => lab i = l)).Nonempty)).card →
        w B = 0 := by
    intro B hcard
    have hprod0 : ∀ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) = 0 := by
      intro θ
      by_contra hne
      let S : Finset (Fin t) := (Finset.univ : Finset (Fin t)).filter
        (fun l => (B.filter (fun i => lab i = l)).Nonempty)
      have hcardS : 3 ≤ S.card := hcard
      let T : Finset (Fin t) := Finset.univ.filter (fun l' => G l' θ ≠ 0)
      have hSsub : S ⊆ T := by
        intro l' hl'
        have hkne : (B.filter (fun i => lab i = l')).Nonempty :=
          (Finset.mem_filter.mp hl').2
        have hG0 : G l' θ ≠ 0 := by
          intro hz
          refine hne (Finset.prod_eq_zero (Finset.mem_univ l') ?_)
          rw [hz]
          exact zero_pow (Finset.card_pos.mpr hkne).ne'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l', hG0⟩
      have hTcard3 : 3 ≤ T.card := le_trans hcardS (Finset.card_le_card hSsub)
      have hthree : ∃ a ∈ T, ∃ b ∈ T, ∃ c' ∈ T, a ≠ b ∧ a ≠ c' ∧ b ≠ c' := by
        have h1 : 0 < T.card := by omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp h1
        have hca : (T.erase a).card = T.card - 1 := Finset.card_erase_of_mem ha
        have h2 : 0 < (T.erase a).card := by rw [hca]; omega
        obtain ⟨b, hb⟩ := Finset.card_pos.mp h2
        have hbT : b ∈ T := Finset.mem_of_mem_erase hb
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        have hcb : ((T.erase a).erase b).card = (T.erase a).card - 1 :=
          Finset.card_erase_of_mem hb
        have h3 : 0 < ((T.erase a).erase b).card := by rw [hcb, hca]; omega
        obtain ⟨c', hc'⟩ := Finset.card_pos.mp h3
        have hc'T : c' ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc')
        have hc'b : c' ≠ b := (Finset.mem_erase.mp hc').1
        have hc'a : c' ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hc')).1
        exact ⟨a, ha, b, hbT, c', hc'T, hba.symm, hc'a.symm, hc'b.symm⟩
      obtain ⟨a, haT, b, hbT, c', hc'T, hab, hac, hbc⟩ := hthree
      have hGa : 0 < G a θ :=
        lt_of_le_of_ne (hG_nonneg a θ) (Ne.symm (Finset.mem_filter.mp haT).2)
      have hGb : 0 < G b θ :=
        lt_of_le_of_ne (hG_nonneg b θ) (Ne.symm (Finset.mem_filter.mp hbT).2)
      have hGc : 0 < G c' θ :=
        lt_of_le_of_ne (hG_nonneg c' θ) (Ne.symm (Finset.mem_filter.mp hc'T).2)
      have ba : |θ - thetaStar a| < 2 * c := hG_pos_supp a θ hGa
      have bb : |θ - thetaStar b| < 2 * c := hG_pos_supp b θ hGb
      have bc : |θ - thetaStar c'| < 2 * c := hG_pos_supp c' θ hGc
      refine three_pt (thetaStar a - θ) (thetaStar b - θ) (thetaStar c' - θ)
        ?_ ?_ ?_ ?_ ?_ ?_
      · rwa [abs_sub_comm]
      · rwa [abs_sub_comm]
      · rwa [abs_sub_comm]
      · have hEq : (thetaStar a - θ) - (thetaStar b - θ) = thetaStar a - thetaStar b := by
          ring
        rw [hEq]
        exact hsep a b hab
      · have hEq : (thetaStar b - θ) - (thetaStar c' - θ) = thetaStar b - thetaStar c' := by
          ring
        rw [hEq]
        exact hsep b c' hbc
      · have hEq : (thetaStar a - θ) - (thetaStar c' - θ) = thetaStar a - thetaStar c' := by
          ring
        rw [hEq]
        exact hsep a c' hac
    have hzero : ∀ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ = 0 := by
      intro θ
      rw [hprod0 θ, zero_mul]
    have hint : ∫ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ
          ∂volume = 0 := by
      rw [show (fun θ : ℝ =>
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ) =
          (fun _ => (0 : ℝ)) from funext hzero]
      simp
    show ((B.card - 1).factorial : ℝ) * ∫ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ ∂volume = 0
    rw [hint, mul_zero]
  have hH : ∀ (B : Finset (Fin n)) (l k : Fin t), l ≠ k →
      (B.filter (fun i => lab i = l)).Nonempty →
      (B.filter (fun i => lab i = k)).Nonempty →
      (∀ i ∈ B, lab i = l ∨ lab i = k) →
      4 * c ≤ |thetaStar l - thetaStar k| → w B = 0 := by
    intro B l k hlk hBl hBk hBsub hfar
    have hpe : 0 < (B.filter (fun i => lab i = l)).card := Finset.card_pos.mpr hBl
    have hqk : 0 < (B.filter (fun i => lab i = k)).card := Finset.card_pos.mpr hBk
    have hzero : ∀ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ = 0 := by
      intro θ
      have hpair : G l θ = 0 ∨ G k θ = 0 := by
        by_contra hc
        push_neg at hc
        obtain ⟨hl1, hl2⟩ := hc
        have b1 : |θ - thetaStar l| < 2 * c :=
          hG_pos_supp l θ (lt_of_le_of_ne (hG_nonneg l θ) (Ne.symm hl1))
        have b2 : |θ - thetaStar k| < 2 * c :=
          hG_pos_supp k θ (lt_of_le_of_ne (hG_nonneg k θ) (Ne.symm hl2))
        obtain ⟨hb1a, hb1b⟩ := abs_lt.mp b1
        obtain ⟨hb2a, hb2b⟩ := abs_lt.mp b2
        have hlt : |thetaStar l - thetaStar k| < 4 * c := by
          rw [abs_lt]
          constructor <;> linarith
        linarith
      rcases hpair with hz | hz
      · have hfac : (G l θ) ^ (B.filter (fun i => lab i = l)).card = 0 := by
          rw [hz]
          exact zero_pow hpe.ne'
        have hprod0 : (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ l) hfac
        rw [hprod0]
        ring
      · have hfac : (G k θ) ^ (B.filter (fun i => lab i = k)).card = 0 := by
          rw [hz]
          exact zero_pow hqk.ne'
        have hprod0 : (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) hfac
        rw [hprod0]
        ring
    have hint : ∫ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ
          ∂volume = 0 := by
      rw [show (fun θ : ℝ =>
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ) =
          (fun _ => (0 : ℝ)) from funext hzero]
      simp
    show ((B.card - 1).factorial : ℝ) * ∫ θ : ℝ,
        (∏ l' : Fin t, (G l' θ) ^ (B.filter (fun i => lab i = l')).card) * q0 θ ∂volume = 0
    rw [hint, mul_zero]
  have hcard_image : ∀ B : Finset (Fin n),
      ((Finset.univ : Finset (Fin t)).filter
        (fun l => (B.filter (fun i => lab i = l)).Nonempty)) = B.image lab := by
    intro B
    ext l
    constructor
    · intro hl
      obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hl).2
      exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    · intro hl
      obtain ⟨i, hiB, hil⟩ := Finset.mem_image.mp hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, ⟨i, Finset.mem_filter.mpr ⟨hiB, hil⟩⟩⟩
  have hG' : ∀ B : Finset (Fin n), 3 ≤ (B.image lab).card → w B = 0 := by
    intro B hB3
    exact hG B (by rw [hcard_image B]; exact hB3)
  exact ⟨hE, hF, hG', hH⟩
  /- @proof-region region.target-node.session.bfac555b7597a6df end -/

end

end Statlib.Imported

end DPCompletedProof
