import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes.Node_3098194069_fe6a3bdb_4ab109ad
open IMO2026P6

namespace IMO2026P6

set_option autoImplicit false in
theorem statopia_math_node_3572779525_bbb7c22f : ∀ (a : Nat → Nat) (ha : IsValidSeq a)
    (n : Nat) (hn : 1 ≤ n) (q : Nat) (hq : Nat.Prime q) (hqB : a 0 < q) (m : Nat)
    (han : a n = q * m) (hgcd : ∀ j, j < n → 1 < Nat.gcd m (a j)),
    ∃ ell, ell < n ∧ ∀ p, Nat.Prime p → p ∣ a ell → p ∣ a n := by
  /- @proof-region region.target-node.session.dcda819ef828622a begin -/
  intro a ha n hn q hq hqB m han hgcd
  have ha_pos := ha.1
  have ha_step := ha.2
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have han0 : a n = 0 := by rw [han, h]; exact Nat.mul_zero q
      have := ha_pos n
      omega
    · exact h
  have hm_ne1 : m ≠ 1 := by
    intro hm1
    have h0 := hgcd 0 (by omega)
    rw [hm1] at h0
    simp at h0
  have hm_gt1 : 1 < m := by omega
  have hm_lt_an : m < a n := by
    rw [han]
    calc m = m * 1 := (Nat.mul_one m).symm
      _ < m * q := Nat.mul_lt_mul_of_pos_left hq.one_lt hm_pos
      _ = q * m := Nat.mul_comm m q
  have hm_le_A : m ≤ a (n - 1) := by
    by_contra h
    push_neg at h
    have hlt : m < a ((n - 1) + 1) := by rw [hn1]; exact hm_lt_an
    obtain ⟨i, hi_le, hi_gcd⟩ := (ha_step (n - 1)).2.2 m h hlt
    have hi_lt : i < n := by omega
    have := hgcd i hi_lt
    omega
  by_cases hB : a 0 ≤ m
  · have hgcd' : ∀ j, j ≤ n - 1 → 1 < Nat.gcd m (a j) := by
      intro j hj
      exact hgcd j (by omega)
    obtain ⟨k, hk_le, hk_eq⟩ :=
      statopia_math_node_3098194069_fe6a3bdb a ha (n - 1) m hB hm_le_A hgcd'
    refine ⟨k, by omega, ?_⟩
    intro p hp hpdvd
    have hpm : p ∣ m := by rw [hk_eq]; exact hpdvd
    rw [han]
    exact dvd_mul_of_dvd_right hpm q
  · push_neg at hB
    have hex : ∃ t, a (n - 1) < m ^ (t + 1) := by
      refine ⟨a (n - 1), ?_⟩
      have h2 : a (n - 1) + 1 < m ^ (a (n - 1) + 1) := Nat.lt_pow_self hm_gt1
      exact lt_trans (Nat.lt_succ_self _) h2
    let T := Nat.find hex
    have hTspec : a (n - 1) < m ^ (T + 1) := Nat.find_spec hex
    have hT_ne0 : T ≠ 0 := by
      intro hT0
      have hspec := hTspec
      rw [hT0] at hspec
      simp only [Nat.zero_add, pow_one] at hspec
      omega
    have hTge1 : 1 ≤ T := by omega
    have hTmin : m ^ T ≤ a (n - 1) := by
      have h1 := Nat.find_min hex (show T - 1 < T by omega)
      rw [Nat.sub_add_cancel hTge1] at h1
      omega
    have hpow_adm : ∀ t, 1 ≤ t → ∀ j, j < n → 1 < Nat.gcd (m ^ t) (a j) := by
      intro t ht j hj
      have hdvd1 : Nat.gcd m (a j) ∣ m ^ t :=
        dvd_trans (Nat.gcd_dvd_left m (a j)) (dvd_pow_self m (by omega))
      have hdvd2 : Nat.gcd m (a j) ∣ a j := Nat.gcd_dvd_right m (a j)
      have hdiv : Nat.gcd m (a j) ∣ Nat.gcd (m ^ t) (a j) := Nat.dvd_gcd hdvd1 hdvd2
      have hgt : 1 < Nat.gcd m (a j) := hgcd j hj
      have hNpos : 0 < Nat.gcd (m ^ t) (a j) := by
        rw [Nat.pos_iff_ne_zero]
        intro hz
        exact absurd (Nat.gcd_eq_zero_iff.mp hz).1 (pow_pos hm_pos t).ne'
      have := Nat.le_of_dvd hNpos hdiv
      omega
    have han_le : a n ≤ m ^ (T + 1) := by
      by_contra h
      push_neg at h
      have hlt : m ^ (T + 1) < a ((n - 1) + 1) := by rw [hn1]; exact h
      obtain ⟨i, hi_le, hi_gcd⟩ := (ha_step (n - 1)).2.2 (m ^ (T + 1)) hTspec hlt
      have hi_lt : i < n := by omega
      have := hpow_adm (T + 1) (by omega) i hi_lt
      omega
    have hq_le : q ≤ m ^ T := by
      have hmul : q * m ≤ m ^ T * m := by
        calc q * m = a n := han.symm
          _ ≤ m ^ (T + 1) := han_le
          _ = m ^ T * m := by rw [pow_succ]
      exact Nat.le_of_mul_le_mul_right hmul hm_pos
    have hgcd'' : ∀ j, j ≤ n - 1 → 1 < Nat.gcd (m ^ T) (a j) := by
      intro j hj
      exact hpow_adm T hTge1 j (by omega)
    obtain ⟨k, hk_le, hk_eq⟩ :=
      statopia_math_node_3098194069_fe6a3bdb a ha (n - 1) (m ^ T)
        (le_trans hqB.le hq_le) hTmin hgcd''
    refine ⟨k, by omega, ?_⟩
    intro p hp hpdvd
    have hpdvd' : p ∣ m ^ T := by rw [hk_eq]; exact hpdvd
    have hpm : p ∣ m := hp.dvd_of_dvd_pow hpdvd'
    rw [han]
    exact dvd_mul_of_dvd_right hpm q
  /- @proof-region region.target-node.session.dcda819ef828622a end -/

end IMO2026P6
