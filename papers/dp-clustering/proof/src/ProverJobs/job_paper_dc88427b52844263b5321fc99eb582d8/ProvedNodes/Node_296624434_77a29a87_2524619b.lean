import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Vocabulary
import ProverJobs.job_paper_dc88427b52844263b5321fc99eb582d8.Base

open Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

set_option autoImplicit false in
theorem statopia_math_node_296624434_77a29a87 : ∀ (t : ℕ) (ht : 1 ≤ t) (nu : ℝ) (hnu : 0 < nu) (q : ℝ)
    (hq_pos : 0 < q) (hq_le : q ≤ 1 / 2),
    let a : ℕ → ℝ := fun s : ℕ =>
      (s : ℝ) * Real.Gamma (nu + (t : ℝ) + (s : ℝ)) * q ^ s / ((t + s).factorial : ℝ)
    Summable a ∧
      ∃ S : ℝ, 0 ≤ S ∧ (∑' s : ℕ, a s) = S ∧
        ∀ N : ℕ, 0 ≤ ∑ s ∈ Finset.Icc 1 N, a s ∧ ∑ s ∈ Finset.Icc 1 N, a s ≤ S := by
  /- @proof-region region.target-node.session.e691b600c4a3855c begin -/
  intro t ht nu hnu q hq_pos hq_half
  set a : ℕ → ℝ := fun s => (s : ℝ) * Real.Gamma (nu + (t : ℝ) + (s : ℝ)) * q ^ s / ((t + s).factorial : ℝ) with ha
  have ha_val : ∀ s, a s = (s : ℝ) * Real.Gamma (nu + (t : ℝ) + (s : ℝ)) * q ^ s / ((t + s).factorial : ℝ) := fun s => by rw [ha]
  have hgamma_pos : ∀ s : ℕ, 0 < Real.Gamma (nu + (t : ℝ) + (s : ℝ)) := by
    intro s
    apply Real.Gamma_pos_of_pos
    have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
    linarith
  have ha_nonneg : ∀ s, 0 ≤ a s := by
    intro s
    rw [ha_val s]
    apply div_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (Nat.cast_nonneg s) (hgamma_pos s).le
      · exact pow_nonneg hq_pos.le s
    · exact Nat.cast_nonneg _
  have hsum : Summable a := by
    have hq_lt_one : q < 1 := by linarith
    set c : ℝ := (1 + q) / 2 with hcdef
    have hc_nonneg : 0 ≤ c := by rw [hcdef]; linarith
    have hc_lt_one : c < 1 := by rw [hcdef]; linarith
    obtain ⟨S0, hS0⟩ := exists_nat_gt (2 * q * (1 + 2 * nu) / (1 - q))
    have hS0_ge : 1 ≤ S0 := by
      have hpos : (0:ℝ) ≤ 2 * q * (1 + 2 * nu) / (1 - q) := by
        apply div_nonneg
        · nlinarith [hq_pos, hnu]
        · linarith
      have : (0:ℝ) < (S0:ℝ) := lt_of_le_of_lt hpos hS0
      have h0 : 0 < S0 := by exact_mod_cast this
      omega
    have hcond : ∀ s : ℕ, S0 ≤ s → 2*q*(1+2*nu) ≤ (s:ℝ)*(1-q) := by
      intro s hs
      have h1 : 2*q*(1+2*nu) < (S0:ℝ)*(1-q) := by
        rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 - q)] at hS0
        exact hS0
      have h2 : (S0:ℝ)*(1-q) ≤ (s:ℝ)*(1-q) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 1 - q)
        exact_mod_cast hs
      linarith
    have hstep : ∀ s : ℕ, S0 ≤ s → a (s+1) ≤ c * a s := by
      intro s hs
      have hs1 : 1 ≤ s := le_trans hS0_ge hs
      have hpos_arg : (0:ℝ) < nu + (t:ℝ) + (s:ℝ) := by
        have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
        have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
        linarith
      have hDpos : (0:ℝ) < (t:ℝ) + (s:ℝ) + 1 := by positivity
      have hcond_s : 2*q*(1+2*nu) ≤ (s:ℝ)*(1-q) := hcond s hs
      have hq1 : (0:ℝ) ≤ (1-q)*(s:ℝ) - 2*q := by nlinarith [hcond_s, hnu, hq_pos]
      have hq2 : (0:ℝ) ≤ (1-q)*(s:ℝ) - 2*nu*q := by nlinarith [hcond_s, hnu, hq_pos]
      have hD : (1+q)*(s:ℝ)*((t:ℝ)+(s:ℝ)+1) - 2*((s:ℝ)+1)*(nu+(t:ℝ)+(s:ℝ))*q
          = (t:ℝ)*((1-q)*(s:ℝ)-2*q) + ((s:ℝ)+1)*((1-q)*(s:ℝ)-2*nu*q) := by ring
      have hp1 : (0:ℝ) ≤ (t:ℝ)*((1-q)*(s:ℝ)-2*q) := mul_nonneg (by positivity) hq1
      have hp2 : (0:ℝ) ≤ ((s:ℝ)+1)*((1-q)*(s:ℝ)-2*nu*q) := mul_nonneg (by positivity) hq2
      have hkey : 2*((s:ℝ)+1)*(nu+(t:ℝ)+(s:ℝ))*q ≤ (1+q)*(s:ℝ)*((t:ℝ)+(s:ℝ)+1) := by
        nlinarith [hp1, hp2, hD]
      have hXle : ((s:ℝ)+1)*(nu+(t:ℝ)+(s:ℝ))*q/((t:ℝ)+(s:ℝ)+1) ≤ c*(s:ℝ) := by
        rw [hcdef, div_le_iff₀ hDpos]
        nlinarith [hkey]
      have hfac_s : a s = (Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ)) * (s:ℝ) := by
        rw [ha_val s]; ring
      have hKpos : (0:ℝ) < Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ) := by
        apply div_pos
        · exact mul_pos (hgamma_pos s) (pow_pos hq_pos s)
        · exact_mod_cast Nat.factorial_pos (t+s)
      have hfac_s1 : a (s+1) = (Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ)) * (((s:ℝ)+1)*(nu+(t:ℝ)+(s:ℝ))*q/((t:ℝ)+(s:ℝ)+1)) := by
        rw [ha_val (s+1)]
        have hF : ((t + s).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t+s)
        have hD2 : ((t:ℝ)+(s:ℝ)+1) ≠ 0 := ne_of_gt (by positivity : (0:ℝ) < (t:ℝ)+(s:ℝ)+1)
        have hcast1 : ((s+1 : ℕ) : ℝ) = (s:ℝ) + 1 := by push_cast; ring
        have harg : nu + (t:ℝ) + ((s:ℝ) + 1) = (nu + (t:ℝ) + (s:ℝ)) + 1 := by ring
        have hcast2 : (t + (s+1) : ℕ) = t + s + 1 := by omega
        rw [hcast1, harg, Real.Gamma_add_one (ne_of_gt hpos_arg), pow_succ, hcast2, Nat.factorial_succ]
        push_cast
        field_simp
      calc a (s+1) = (Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ)) * (((s:ℝ)+1)*(nu+(t:ℝ)+(s:ℝ))*q/((t:ℝ)+(s:ℝ)+1)) := hfac_s1
        _ ≤ (Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ)) * (c*(s:ℝ)) := mul_le_mul_of_nonneg_left hXle hKpos.le
        _ = c * ((Real.Gamma (nu+(t:ℝ)+(s:ℝ)) * q^s / ((t+s).factorial:ℝ)) * (s:ℝ)) := by ring
        _ = c * a s := by rw [hfac_s]
    set b : ℕ → ℝ := fun k => a (k + S0) with hb
    have hb_nonneg : ∀ k, 0 ≤ b k := fun k => by simpa only [hb] using ha_nonneg (k + S0)
    have hb_bound : ∀ k, b k ≤ a S0 * c ^ k := by
      intro k
      induction k with
      | zero =>
          have h0 : b 0 = a S0 := by simp [hb]
          rw [h0]; simp
      | succ n ih =>
          have hsh : (n+1) + S0 = (n + S0) + 1 := by omega
          have h1 : a ((n + S0) + 1) ≤ c * a (n + S0) := hstep (n + S0) (by omega)
          have h2 : c * a (n + S0) ≤ c * (a S0 * c ^ n) := by
            apply mul_le_mul_of_nonneg_left _ hc_nonneg
            simpa only [hb] using ih
          have h3 : c * (a S0 * c ^ n) = a S0 * c ^ (n+1) := by rw [pow_succ]; ring
          calc b (n+1) = a ((n+1) + S0) := by simp only [hb]
            _ = a ((n + S0) + 1) := by rw [hsh]
            _ ≤ c * a (n + S0) := h1
            _ ≤ c * (a S0 * c ^ n) := h2
            _ = a S0 * c ^ (n+1) := h3
    have hgeo : Summable (fun k => a S0 * c ^ k) := by
      have hsm := Summable.const_smul (a S0) (summable_geometric_of_lt_one hc_nonneg hc_lt_one)
      simpa only [smul_eq_mul] using hsm
    have hbsumm : Summable b := Summable.of_nonneg_of_le hb_nonneg hb_bound hgeo
    have hbsumm' : Summable (fun k => a (k + S0)) := by simpa only [hb] using hbsumm
    exact (summable_nat_add_iff S0).mp hbsumm'
  refine ⟨hsum, ∑' s, a s, ?_, rfl, ?_⟩
  · exact tsum_nonneg ha_nonneg
  · intro N
    exact ⟨Finset.sum_nonneg (fun s _ => ha_nonneg s), hsum.sum_le_tsum (Finset.Icc 1 N) (fun i _ => ha_nonneg i)⟩
  /- @proof-region region.target-node.session.e691b600c4a3855c end -/

end

end Statlib.Imported
