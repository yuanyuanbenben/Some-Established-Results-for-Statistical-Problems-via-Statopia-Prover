import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Vocabulary
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base
import ProverJobs.manual_dp_cons_finish_20261031.WindowMass
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.ProvedNodes.Node_4208862229_4f2341a0_322e10ba
open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_247103928_dcf533aa : ∀ (t : ℕ) (ht : 1 ≤ t) (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ) (thetaStar : Fin t → ℝ) (m : ℝ) (hm : 0 < m)
    (hg_meas : Measurable g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_zero : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_lower : ∀ x ∈ Set.Icc (-c) c, m ≤ g x)
    (hg_int : ∫ (x : ℝ), g x ∂volume = 1)
    (hg_intble : Integrable g volume)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (hA : 2 * c * m ≤ 1)
    (l k : Fin t) (hlk : l ≠ k)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (theta : ℝ),
    (∫ (x : ℝ) in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - theta) ∂volume) ^ p *
        (∫ (x : ℝ) in Set.Icc (thetaStar k - c) (thetaStar k + c),
            g (x - theta) ∂volume) ^ q
      ≤ (dpKappa c m thetaStar) ^ (p + q) *
        ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q := by
  /- @proof-region region.target-node.session.9afcfb38320e05f9 begin -/
  intro t ht c hc g thetaStar m hm hg_meas hg_nonneg hg_zero hg_lower hg_int hg_intble hsep hA l k hlk p q hp hq θ
  have amgm : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
      a ^ p * c ^ q
        ≤ ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q
          * (a + c) ^ (p + q) := by
    intro a c ha hc
    have hpR : (0 : ℝ) < (p : ℝ) := by
      have h : 0 < p := by omega
      exact_mod_cast h
    have hqR : (0 : ℝ) < (q : ℝ) := by
      have h : 0 < q := by omega
      exact_mod_cast h
    have hbr : (0 : ℝ) < ((p + q : ℕ) : ℝ) := by
      have h : 0 < p + q := by omega
      exact_mod_cast h
    have hbcast : ((p + q : ℕ) : ℝ) = (p : ℝ) + (q : ℝ) := by push_cast; ring
    have hcancel : ∀ e b d : ℝ, 0 < e → e * b ≤ e * d → b ≤ d := by
      intro e b d he hbd
      by_contra hcon
      push_neg at hcon
      nlinarith [he, hbd, hcon]
    have key : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A + B = ((p + q : ℕ) : ℝ) →
        A ^ p * B ^ q ≤ (p : ℝ) ^ p * (q : ℝ) ^ q := by
      intro A B hA hB hAB
      have hpos2 : 0 < (p : ℝ) ^ p * (q : ℝ) ^ q :=
        mul_pos (pow_pos hpR p) (pow_pos hqR q)
      rcases eq_or_lt_of_le hA with hA0 | hAp
      · rw [← hA0, zero_pow (by omega : p ≠ 0), zero_mul]
        exact mul_nonneg (pow_nonneg (le_of_lt hpR) p) (pow_nonneg (le_of_lt hqR) q)
      rcases eq_or_lt_of_le hB with hB0 | hBp
      · rw [← hB0, zero_pow (by omega : q ≠ 0), mul_zero]
        exact mul_nonneg (pow_nonneg (le_of_lt hpR) p) (pow_nonneg (le_of_lt hqR) q)
      have hpA : (p : ℝ) * (A / (p : ℝ)) = A := by
        field_simp
        try ring
      have hqB : (q : ℝ) * (B / (q : ℝ)) = B := by
        field_simp
        try ring
      have h1 : Real.log (A / (p : ℝ)) ≤ A / (p : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (B / (q : ℝ)) ≤ B / (q : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : (p : ℝ) * Real.log (A / (p : ℝ)) + (q : ℝ) * Real.log (B / (q : ℝ)) ≤ 0 := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hpR),
          mul_le_mul_of_nonneg_left h2 (le_of_lt hqR), hAB, hbcast, hpA, hqB]
      have hla : Real.log (A / (p : ℝ)) = Real.log A - Real.log (p : ℝ) :=
        Real.log_div (ne_of_gt hAp) (ne_of_gt hpR)
      have hlb : Real.log (B / (q : ℝ)) = Real.log B - Real.log (q : ℝ) :=
        Real.log_div (ne_of_gt hBp) (ne_of_gt hqR)
      have h4 : (p : ℝ) * Real.log A + (q : ℝ) * Real.log B
          ≤ (p : ℝ) * Real.log (p : ℝ) + (q : ℝ) * Real.log (q : ℝ) := by
        rw [hla, hlb] at h3
        linarith
      have hpos1 : 0 < A ^ p * B ^ q := mul_pos (pow_pos hAp p) (pow_pos hBp q)
      have hl1 : Real.log (A ^ p * B ^ q) = (p : ℝ) * Real.log A + (q : ℝ) * Real.log B := by
        rw [Real.log_mul (ne_of_gt (pow_pos hAp p)) (ne_of_gt (pow_pos hBp q)),
          Real.log_pow, Real.log_pow]
      have hl2 : Real.log ((p : ℝ) ^ p * (q : ℝ) ^ q)
          = (p : ℝ) * Real.log (p : ℝ) + (q : ℝ) * Real.log (q : ℝ) := by
        rw [Real.log_mul (ne_of_gt (pow_pos hpR p)) (ne_of_gt (pow_pos hqR q)),
          Real.log_pow, Real.log_pow]
      calc A ^ p * B ^ q = Real.exp (Real.log (A ^ p * B ^ q)) := (Real.exp_log hpos1).symm
        _ = Real.exp ((p : ℝ) * Real.log A + (q : ℝ) * Real.log B) := by rw [hl1]
        _ ≤ Real.exp ((p : ℝ) * Real.log (p : ℝ) + (q : ℝ) * Real.log (q : ℝ)) :=
            Real.exp_le_exp.mpr h4
        _ = Real.exp (Real.log ((p : ℝ) ^ p * (q : ℝ) ^ q)) := by rw [hl2]
        _ = (p : ℝ) ^ p * (q : ℝ) ^ q := Real.exp_log hpos2
    have hsum0 : (0 : ℝ) ≤ a + c := by linarith
    rcases eq_or_lt_of_le hsum0 with hs0 | hspos
    · have ha0 : a = 0 := by linarith
      have hc0 : c = 0 := by linarith
      rw [ha0, hc0, zero_pow (by omega : p ≠ 0), zero_mul, zero_add,
        zero_pow (by omega : p + q ≠ 0), mul_zero]
    · set U : ℝ := a / (a + c) with hU
      set V : ℝ := c / (a + c) with hV
      have hUnn : 0 ≤ U := by rw [hU]; exact div_nonneg ha (le_of_lt hspos)
      have hVnn : 0 ≤ V := by rw [hV]; exact div_nonneg hc (le_of_lt hspos)
      have hUV1 : U + V = 1 := by rw [hU, hV, ← add_div, div_self (ne_of_gt hspos)]
      set A : ℝ := ((p + q : ℕ) : ℝ) * U with hAdef
      set B : ℝ := ((p + q : ℕ) : ℝ) * V with hBdef
      have hAnn : 0 ≤ A := by rw [hAdef]; exact mul_nonneg (le_of_lt hbr) hUnn
      have hBnn : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (le_of_lt hbr) hVnn
      have hAB : A + B = ((p + q : ℕ) : ℝ) := by
        rw [hAdef, hBdef, ← mul_add, hUV1, mul_one]
      have hkey := key A B hAnn hBnn hAB
      have hpowA : A ^ p * B ^ q = ((p + q : ℕ) : ℝ) ^ (p + q) * (U ^ p * V ^ q) := by
        rw [hAdef, hBdef, mul_pow, mul_pow, pow_add]
        ring
      have hbpne : ((p + q : ℕ) : ℝ) ^ p ≠ 0 := ne_of_gt (pow_pos hbr p)
      have hbqne : ((p + q : ℕ) : ℝ) ^ q ≠ 0 := ne_of_gt (pow_pos hbr q)
      have hPQ : ((p + q : ℕ) : ℝ) ^ (p + q)
            * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q)
          = (p : ℝ) ^ p * (q : ℝ) ^ q := by
        rw [div_pow, div_pow, pow_add]
        field_simp
      rw [hpowA, ← hPQ] at hkey
      have hUVle : U ^ p * V ^ q
          ≤ ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q :=
        hcancel _ _ _ (pow_pos hbr _) hkey
      have hstep : (a + c) ^ (p + q) * (U ^ p * V ^ q) = a ^ p * c ^ q := by
        have hapne : (a + c) ^ p ≠ 0 := ne_of_gt (pow_pos hspos p)
        have haqne : (a + c) ^ q ≠ 0 := ne_of_gt (pow_pos hspos q)
        rw [hU, hV, div_pow, div_pow, pow_add]
        field_simp
        try ring
      calc a ^ p * c ^ q = (a + c) ^ (p + q) * (U ^ p * V ^ q) := hstep.symm
        _ ≤ (a + c) ^ (p + q)
              * (((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q) :=
            mul_le_mul_of_nonneg_left hUVle (pow_nonneg (le_of_lt hspos) _)
        _ = ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p * ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q
              * (a + c) ^ (p + q) := by ring
  set u : ℝ := ∫ (x : ℝ) in Set.Icc (thetaStar l - c) (thetaStar l + c), g (x - θ) with hudef
  set v : ℝ := ∫ (x : ℝ) in Set.Icc (thetaStar k - c) (thetaStar k + c), g (x - θ) with hvdef
  set κ : ℝ := dpKappa c m thetaStar with hκdef
  set P : ℝ := ((p : ℝ) / ((p + q : ℕ) : ℝ)) ^ p with hPdef
  set Q : ℝ := ((q : ℝ) / ((p + q : ℕ) : ℝ)) ^ q with hQdef
  have hpq : (0 : ℝ) < ((p + q : ℕ) : ℝ) := by
    have h0 : 0 < p + q := by omega
    exact_mod_cast h0
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hPK : 0 ≤ P * Q := mul_nonneg hPnn hQnn
  have hκnn : 0 ≤ κ := by
    rw [hκdef]
    unfold dpKappa
    split_ifs with hne
    · obtain ⟨q, hq⟩ := hne
      simp only [dpClosePair] at hq
      have hq' : q.1 ≠ q.2 ∧ |thetaStar q.1 - thetaStar q.2| < 4 * c := (Finset.mem_filter.mp hq).2
      have hlt : 2 * c < |thetaStar q.1 - thetaStar q.2| := hsep q.1 q.2 hq'.1
      have h2 : 0 < 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c) := by
        nlinarith [hlt, hq'.2, hm, hA]
      have hle := Finset.le_sup' (fun q : Fin t × Fin t => 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c)) hq
      exact le_trans (le_of_lt h2) hle
    · exact le_refl 0
  have hWl := statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm hg_meas hg_nonneg hg_zero hg_lower hg_int l θ
  have hWk := statopia_math_node_1091114221_9ffd4ba6 t ht c hc g thetaStar m hm hg_meas hg_nonneg hg_zero hg_lower hg_int k θ
  obtain ⟨hunn, _, hul0⟩ := hWl
  obtain ⟨hvnn, _, huk0⟩ := hWk
  rcases eq_or_lt_of_le hunn with hu0 | hupos
  · have hu0' : u = 0 := hudef.trans hu0.symm
    rw [hu0', zero_pow (by omega : p ≠ 0), zero_mul]
    exact mul_nonneg (mul_nonneg (pow_nonneg hκnn (p + q)) hPnn) hQnn
  rcases eq_or_lt_of_le hvnn with hv0 | hvpos
  · have hv0' : v = 0 := hvdef.trans hv0.symm
    rw [hv0', zero_pow (by omega : q ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg hκnn (p + q)) hPnn) hQnn
  have hdl : |θ - thetaStar l| < 2 * c := by
    rcases lt_or_ge (|θ - thetaStar l|) (2 * c) with h | h
    · exact h
    · exact absurd (hul0 h) (ne_of_gt hupos)
  have hdk : |θ - thetaStar k| < 2 * c := by
    rcases lt_or_ge (|θ - thetaStar k|) (2 * c) with h | h
    · exact h
    · exact absurd (huk0 h) (ne_of_gt hvpos)
  have hδ4 : |thetaStar l - thetaStar k| < 4 * c := by
    have h1 : |thetaStar l - θ| < 2 * c := by rw [abs_sub_comm]; exact hdl
    have h2 := abs_add_le (thetaStar l - θ) (θ - thetaStar k)
    have h3 : thetaStar l - θ + (θ - thetaStar k) = thetaStar l - thetaStar k := by ring
    rw [h3] at h2
    linarith
  have hmem : (l, k) ∈ dpClosePair c thetaStar := by
    simp only [dpClosePair, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hlk, hδ4⟩
  have hκsup : 1 - m * (|thetaStar l - thetaStar k| - 2 * c) ≤ κ := by
    rw [hκdef]
    unfold dpKappa
    split_ifs with hne
    · exact Finset.le_sup'_of_le (fun q : Fin t × Fin t => 1 - m * (|thetaStar q.1 - thetaStar q.2| - 2 * c)) hmem le_rfl
    · exact absurd ⟨(l, k), hmem⟩ hne
  have huvnn : 0 ≤ u + v := by linarith
  have hsur : u + v ≤ 1 - m * (|thetaStar l - thetaStar k| - 2 * c) := by
    have hc2 := statopia_math_node_4208862229_4f2341a0 c g m θ (thetaStar l) (thetaStar k) hc hm hg_meas hg_nonneg hg_zero hg_lower hg_int hdl hdk (hsep l k hlk)
    simpa [hudef, hvdef] using hc2
  have hsum : u + v ≤ κ := le_trans hsur hκsup
  have hamgm : u ^ p * v ^ q ≤ P * Q * (u + v) ^ (p + q) := by
    have h := amgm u v hunn hvnn
    simpa [hPdef, hQdef] using h
  have hpow : (u + v) ^ (p + q) ≤ κ ^ (p + q) := pow_le_pow_left₀ huvnn hsum (p + q)
  calc u ^ p * v ^ q ≤ P * Q * (u + v) ^ (p + q) := hamgm
    _ ≤ P * Q * κ ^ (p + q) := mul_le_mul_of_nonneg_left hpow hPK
    _ = κ ^ (p + q) * P * Q := by ring
  /- @proof-region region.target-node.session.9afcfb38320e05f9 end -/

end

end Statlib.Imported

#print axioms Statlib.Imported.statopia_math_node_247103928_dcf533aa
