import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_1231998112_26c8ceab_5b4097d6
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_2755318678_16f2be55_fa9b4632
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_835102445_1358d677_25013d58





set_option autoImplicit false in
theorem statopia_math_node_2246720384_db986540 : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a),
    let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
    let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
    {p : ℕ | Nat.Prime p ∧ ∃ m ∈ M, p ∣ m}.Finite := by
  /- @proof-region region.target-node.session.2617c00811cf237c begin -/
  intro a ha
  classical
  let good : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
  let M : Set ℕ := {m : ℕ | good m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ good d}
  change {p : ℕ | Nat.Prime p ∧ ∃ m ∈ M, p ∣ m}.Finite
  have descent_cofactor : ∀ p : ℕ, Nat.Prime p → (∃ m ∈ M, p ∣ m) →
      ∃ c : ℕ, 1 ≤ c ∧ c ≤ a 0 ∧ ¬ good c ∧ p * c ∈ M := by
    intro p hp hex
    obtain ⟨m, hmM, hpm⟩ := hex
    have hmM' : good m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ good d := hmM
    obtain ⟨m', hm'good, hm'min, hpm', hle'⟩ :=
      statopia_math_node_835102445_1358d677 a ha m p hmM'.1 hmM'.2 hp hpm
    have hm'M : m' ∈ M := ⟨hm'good, hm'min⟩
    have hp2 : 2 ≤ p := hp.two_le
    let c := m' / p
    have hpc : p * c = m' := Nat.mul_div_cancel' hpm'
    have hm'pos : 0 < m' := hm'good.1
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · rw [h0, Nat.mul_zero] at hpc
        omega
      · exact hpos
    have hcdvd : c ∣ m' := ⟨p, by rw [Nat.mul_comm c p]; exact hpc.symm⟩
    have hclt : c < m' := by
      rw [← hpc]
      have h1 : 2 * c ≤ p * c := Nat.mul_le_mul_right c hp2
      have h2 : c < 2 * c := by omega
      omega
    have hcng : ¬ good c := hm'min c hcdvd hclt
    refine ⟨c, ?_, ?_, hcng, ?_⟩
    · omega
    · exact hle'
    · rw [hpc]; exact hm'M
  have exists_coprime_index : ∀ c : ℕ, 0 < c → ¬ good c → ∃ j : ℕ, Nat.gcd c (a j) = 1 := by
    intro c hc hnc
    have hnot : ¬ ∀ i : ℕ, 1 < Nat.gcd c (a i) := by
      intro h
      exact hnc ⟨hc, h⟩
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    refine ⟨j, ?_⟩
    have hgp : 0 < Nat.gcd c (a j) := Nat.gcd_pos_of_pos_left (a j) hc
    omega
  let cfun : ℕ → ℕ := fun p =>
    if h : ∃ c : ℕ, 1 ≤ c ∧ c ≤ a 0 ∧ ¬ good c ∧ p * c ∈ M then Classical.choose h else 0
  have cfun_spec : ∀ p (h : ∃ c : ℕ, 1 ≤ c ∧ c ≤ a 0 ∧ ¬ good c ∧ p * c ∈ M),
      1 ≤ cfun p ∧ cfun p ≤ a 0 ∧ ¬ good (cfun p) ∧ p * cfun p ∈ M := by
    intro p h
    have hcf : cfun p = Classical.choose h := by
      simp only [cfun]
      rw [dif_pos h]
    rw [hcf]
    exact Classical.choose_spec h
  let jfun : ℕ → ℕ := fun c =>
    if h : ∃ j : ℕ, Nat.gcd c (a j) = 1 then Classical.choose h else 0
  have jfun_spec : ∀ c (h : ∃ j : ℕ, Nat.gcd c (a j) = 1),
      Nat.gcd c (a (jfun c)) = 1 := by
    intro c h
    have hjf : jfun c = Classical.choose h := by
      simp only [jfun]
      rw [dif_pos h]
    rw [hjf]
    exact Classical.choose_spec h
  have prime_dvd_of_good : ∀ p c j : ℕ, Nat.Prime p → p * c ∈ M →
      Nat.gcd c (a j) = 1 → p ∣ a j := by
    intro p c j hp hpcm hgcd
    obtain ⟨-, -, -, -, -, haterm, -, -⟩ := statopia_math_node_3776635361_5eaf0306 a ha
    have hpcgood : good (p * c) := hpcm.1
    have hgcd_gt : 1 < Nat.gcd (a j) (p * c) :=
      statopia_math_node_2755318678_16f2be55 a ha (a j) (p * c) (haterm j) hpcgood
    have hgne : Nat.gcd (a j) (p * c) ≠ 1 := by omega
    obtain ⟨r, hrprime, hrgcd⟩ := Nat.exists_prime_and_dvd hgne
    have hraj : r ∣ a j := dvd_trans hrgcd (Nat.gcd_dvd_left (a j) (p * c))
    have hrpc : r ∣ p * c := dvd_trans hrgcd (Nat.gcd_dvd_right (a j) (p * c))
    have hnotrc : ¬ r ∣ c := by
      intro hrc
      have hrgcd2 : r ∣ Nat.gcd c (a j) := Nat.dvd_gcd hrc hraj
      rw [hgcd] at hrgcd2
      exact hrprime.not_dvd_one hrgcd2
    have hrp : r ∣ p := by
      rcases (Nat.Prime.dvd_mul hrprime).mp hrpc with h | h
      · exact h
      · exact absurd h hnotrc
    have hreq : r = p := (Nat.prime_dvd_prime_iff_eq hrprime hp).mp hrp
    rw [hreq] at hraj
    exact hraj
  let N : ℕ := ∏ c ∈ Finset.Icc 1 (a 0), a (jfun c)
  have hNpos : 0 < N := by
    apply Finset.prod_pos
    intro c hc
    have h1 : 1 < a (jfun c) := ha.1 (jfun c)
    omega
  have hsub : {p : ℕ | Nat.Prime p ∧ ∃ m ∈ M, p ∣ m} ⊆ (Nat.primeFactors N : Set ℕ) := by
    intro p hp
    obtain ⟨hpprime, hpex⟩ := hp
    have hexc : ∃ c : ℕ, 1 ≤ c ∧ c ≤ a 0 ∧ ¬ good c ∧ p * c ∈ M :=
      descent_cofactor p hpprime hpex
    obtain ⟨hc1, hcle, hcng, hpcm⟩ := cfun_spec p hexc
    have hcpos : 0 < cfun p := by omega
    have hexj : ∃ j : ℕ, Nat.gcd (cfun p) (a j) = 1 :=
      exists_coprime_index (cfun p) hcpos hcng
    have hgj : Nat.gcd (cfun p) (a (jfun (cfun p))) = 1 := jfun_spec (cfun p) hexj
    have hpdiv : p ∣ a (jfun (cfun p)) :=
      prime_dvd_of_good p (cfun p) (jfun (cfun p)) hpprime hpcm hgj
    have hmem : cfun p ∈ Finset.Icc 1 (a 0) := Finset.mem_Icc.mpr ⟨hc1, hcle⟩
    have hfac : a (jfun (cfun p)) ∣ ∏ c ∈ Finset.Icc 1 (a 0), a (jfun c) :=
      Finset.dvd_prod_of_mem (fun c => a (jfun c)) hmem
    have hdvdN : p ∣ N := dvd_trans hpdiv hfac
    exact Nat.mem_primeFactors.mpr ⟨hpprime, hdvdN, hNpos.ne'⟩
  exact Set.Finite.subset (Nat.primeFactors N).finite_toSet hsub
  /- @proof-region region.target-node.session.2617c00811cf237c end -/
