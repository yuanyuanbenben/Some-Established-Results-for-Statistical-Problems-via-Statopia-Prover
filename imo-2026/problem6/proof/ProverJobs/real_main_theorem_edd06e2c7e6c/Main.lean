import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base

theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L
:= by
  /- @proof-region region.root.0877d6e4cecb begin -/
  classical
  set S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i) with hS
  set M : ℕ → Prop := fun m => S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d with hM
  have ha1 : ∀ n, 1 < a n := ha.1
  have hstep : ∀ n, a n < a (n + 1) := fun n => (ha.2 n).1
  have hnext : ∀ n, ∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i) := fun n => (ha.2 n).2.1
  have hgap : ∀ n, ∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1 :=
    fun n => (ha.2 n).2.2
  have hmono : ∀ m n : ℕ, m < n → a m < a n := by
    intro m n
    induction n with
    | zero => intro h; omega
    | succ k ih =>
      intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact lt_trans (ih h') (hstep k)
      · rw [h']
        exact hstep k
  have hle : ∀ m n : ℕ, m ≤ n → a m ≤ a n := by
    intro m n h
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · exact le_of_lt (hmono m n h')
    · subst h'
      exact le_rfl
  have hinj : Function.Injective a := by
    intro m n h
    rcases Nat.lt_trichotomy m n with h' | h' | h'
    · exact absurd h (ne_of_lt (hmono m n h'))
    · exact h'
    · exact absurd h.symm (ne_of_lt (hmono n m h'))
  have hgood : ∀ n, S (a n) := by
    intro n
    refine ⟨by have := ha1 n; omega, ?_⟩
    intro i
    rcases lt_trichotomy i n with h | h | h
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact hnext k i (by omega)
    · rw [h]
      simpa using ha1 n
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hh := hnext k n (by omega)
      rwa [Nat.gcd_comm] at hh
  have hunb : ∀ N, ∃ n, N ≤ a n := by
    intro N
    have hge : ∀ k, k ≤ a k := by
      intro k
      induction k with
      | zero => exact Nat.zero_le _
      | succ j ih => have := hstep j; omega
    exact ⟨N, hge N⟩
  have hup : ∀ x y : ℕ, S x → x ∣ y → 0 < y → S y := by
    intro x y hx hdvd hy
    refine ⟨hy, fun i => ?_⟩
    have h1 : 1 < Nat.gcd x (a i) := hx.2 i
    have hd : Nat.gcd x (a i) ∣ Nat.gcd y (a i) :=
      Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left x (a i)) hdvd) (Nat.gcd_dvd_right x (a i))
    have hne : Nat.gcd y (a i) ≠ 0 := by
      intro h0
      have hdv : 0 ∣ a i := h0 ▸ Nat.gcd_dvd_right y (a i)
      obtain ⟨c, hc⟩ := hdv
      rw [Nat.zero_mul] at hc
      have hai : 1 < a i := ha1 i
      omega
    have hpos : 0 < Nat.gcd y (a i) := Nat.pos_of_ne_zero hne
    have h2 : Nat.gcd x (a i) ≤ Nat.gcd y (a i) := Nat.le_of_dvd hpos hd
    omega
  have hone : ¬ S 1 := by
    intro h
    have h1 := h.2 0
    simp at h1
  have henum : ∀ x : ℕ, (∃ n, a n = x) ↔ S x ∧ a 0 ≤ x := by
    intro x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨hgood n, hle 0 n (Nat.zero_le n)⟩
    · rintro ⟨hx, hAx⟩
      by_contra hcon
      push_neg at hcon
      have hAx' : a 0 < x := lt_of_le_of_ne hAx (hcon 0)
      have hex : ∃ n, x ≤ a n := hunb x
      have hn : x ≤ a (Nat.find hex) := Nat.find_spec hex
      have hfinder : ∀ m, m < Nat.find hex → a m < x := by
        intro m hm
        have hnm : ¬ (x ≤ a m) := by
          intro hle'
          have hmin := Nat.find_min' hex hle'
          omega
        omega
      have hpos : 0 < Nat.find hex := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
        · rw [h] at hn
          omega
        · exact h
      obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      rw [hk] at hn hfinder
      have h1 : a k < x := hfinder k (by omega)
      have h2 : x < a (k + 1) := by
        have hne : x ≠ a (k + 1) := fun h => hcon (k + 1) h.symm
        omega
      obtain ⟨i, hi, hg⟩ := hgap k x h1 h2
      have hgx : 1 < Nat.gcd x (a i) := hx.2 i
      rw [hg] at hgx
      omega
  have hcover : ∀ x : ℕ, S x → ∃ m, M m ∧ m ∣ x := by
    intro x hx
    have hex : ∃ e, e ∣ x ∧ S e := ⟨x, dvd_refl x, hx⟩
    have hsp1 : Nat.find hex ∣ x := (Nat.find_spec hex).1
    have hsp2 : S (Nat.find hex) := (Nat.find_spec hex).2
    refine ⟨Nat.find hex, ⟨hsp2, ?_⟩, hsp1⟩
    intro d hd hlt hSd
    have hmin := Nat.find_min' hex ⟨Nat.dvd_trans hd hsp1, hSd⟩
    omega
  have hpair : ∀ x y : ℕ, S x → S y → 1 < Nat.gcd x y := by
    intro x y hx hy
    by_contra hcon
    have hg1 : Nat.gcd x y = 1 := by
      have hpos : 0 < Nat.gcd x y := by
        rcases Nat.eq_zero_or_pos (Nat.gcd x y) with h | h
        · exfalso
          have h0 : 0 ∣ x := h ▸ Nat.gcd_dvd_left x y
          obtain ⟨c, hc⟩ := h0
          rw [Nat.zero_mul] at hc
          have := hx.1
          omega
        · exact h
      omega
    have hg1' : Nat.gcd y x = 1 := by rw [Nat.gcd_comm]; exact hg1
    set k : ℕ := 1 + a 0 * y with hk
    have hkpos : 0 < k := by rw [hk]; omega
    have hky : Nat.gcd y k = 1 := by
      have hc : y.Coprime k := by
        rw [hk, mul_comm (a 0) y]
        refine (Nat.coprime_add_mul_left_right y 1 (a 0)).mpr ?_
        exact Nat.dvd_one.mp (Nat.gcd_dvd_right y 1)
      exact hc
    have hSkx : S (k * x) := by
      refine hup x (k * x) hx ⟨k, mul_comm k x⟩ ?_
      exact Nat.mul_pos hkpos hx.1
    have hA : a 0 ≤ k * x := by
      have h1 : a 0 * 1 ≤ a 0 * y := Nat.mul_le_mul_left (a 0) hy.1
      have h2 : k * 1 ≤ k * x := Nat.mul_le_mul_left k hx.1
      rw [Nat.mul_one] at h1 h2
      have h3 : a 0 * y ≤ k := by rw [hk]; omega
      omega
    obtain ⟨n, hn⟩ := (henum (k * x)).mpr ⟨hSkx, hA⟩
    have hgy : 1 < Nat.gcd y (a n) := hy.2 n
    rw [hn] at hgy
    have hne : Nat.gcd y (k * x) ≠ 1 := by omega
    obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hr1 : r ∣ y := Nat.dvd_trans hrd (Nat.gcd_dvd_left y (k * x))
    have hr2 : r ∣ k * x := Nat.dvd_trans hrd (Nat.gcd_dvd_right y (k * x))
    rcases (hrp.dvd_mul).mp hr2 with h | h
    · have hcontra : r ∣ 1 := by
        have hgg := Nat.dvd_gcd hr1 h
        rwa [hky] at hgg
      exact absurd hcontra hrp.not_dvd_one
    · have hcontra : r ∣ 1 := by
        have hgg := Nat.dvd_gcd hr1 h
        rwa [hg1'] at hgg
      exact absurd hcontra hrp.not_dvd_one
  have hmiss : ∀ x : ℕ, a 0 < x → ¬ S x → ∃ i, a i < x ∧ Nat.gcd x (a i) = 1 := by
    intro x hx0 hxns
    have hne : ∀ n, a n ≠ x := by
      intro n hn
      exact hxns (hn ▸ hgood n)
    have hex : ∃ n, x ≤ a n := hunb x
    have hs : x ≤ a (Nat.find hex) := Nat.find_spec hex
    have hf : ∀ m, m < Nat.find hex → a m < x := by
      intro m hm
      have hnm : ¬ (x ≤ a m) := by
        intro hle'
        have hmin := Nat.find_min' hex hle'
        omega
      omega
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h] at hs
        omega
      · exact h
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    rw [hk] at hs hf
    have h1 : a k < x := hf k (by omega)
    have h2 : x < a (k + 1) := by
      have hxn : x ≠ a (k + 1) := fun h => hne (k + 1) h.symm
      omega
    obtain ⟨i, hi, hg⟩ := hgap k x h1 h2
    exact ⟨i, lt_of_le_of_lt (hle i k hi) h1, hg⟩
  have hsqfree : ∀ m, M m → Squarefree m := by
    intro m hm
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    have hp2 : 2 ≤ p := hp.two_le
    have hm0 : 0 < m := hm.1.1
    obtain ⟨c, hc⟩ : ∃ c, m = p * (p * c) := by
      obtain ⟨d, hd⟩ := hpp
      exact ⟨d, by rw [hd]; ring⟩
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exfalso
        rw [h] at hc
        rw [hc] at hm0
        simp at hm0
      · exact h
    have hd0 : 0 < p * c := Nat.mul_pos (by omega) hc0
    have hdvd : p * c ∣ m := ⟨p, by rw [hc, mul_comm p (p * c)]⟩
    have hlt : p * c < m := by
      rw [hc]
      exact lt_mul_of_one_lt_left hd0 (by omega)
    have hS : S (p * c) := by
      refine ⟨hd0, fun i => ?_⟩
      have hmi : 1 < Nat.gcd m (a i) := hm.1.2 i
      have hne1 : Nat.gcd m (a i) ≠ 1 := by omega
      obtain ⟨r, hrp, hrg⟩ := Nat.exists_prime_and_dvd hne1
      have hrm : r ∣ m := Nat.dvd_trans hrg (Nat.gcd_dvd_left m (a i))
      have hra : r ∣ a i := Nat.dvd_trans hrg (Nat.gcd_dvd_right m (a i))
      have hrd : r ∣ p * c := by
        rw [hc] at hrm
        rcases (hrp.dvd_mul).mp hrm with h | h
        · have hreq : r = p := (Nat.prime_dvd_prime_iff_eq hrp hp).mp h
          rw [hreq]
          exact dvd_mul_right p c
        · exact h
      have hgd : r ∣ Nat.gcd (p * c) (a i) := Nat.dvd_gcd hrd hra
      have hpos : 0 < Nat.gcd (p * c) (a i) := by
        rcases Nat.eq_zero_or_pos (Nat.gcd (p * c) (a i)) with h | h
        · exfalso
          have h0 : 0 ∣ a i := h ▸ Nat.gcd_dvd_right (p * c) (a i)
          obtain ⟨w, hw⟩ := h0
          rw [Nat.zero_mul] at hw
          have hai : 1 < a i := ha1 i
          omega
        · exact h
      have h2 : r ≤ Nat.gcd (p * c) (a i) := Nat.le_of_dvd hpos hgd
      have hr2 : 2 ≤ r := hrp.two_le
      omega
    exact hm.2 (p * c) hdvd hlt hS
  have hdescent : ∀ m, M m → ∀ q : ℕ, Nat.Prime q → q ∣ m →
      ∃ m' c : ℕ, M m' ∧ q ∣ m' ∧ m' = q * c ∧ c ≤ a 0 := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hmM q hq hqm
    have hm0 : 0 < m := hmM.1.1
    set x : ℕ := m / q with hx
    have hxq : x * q = m := by rw [hx]; exact Nat.div_mul_cancel hqm
    have hmq : m = q * x := by rw [← hxq, mul_comm]
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exfalso
        rw [h, Nat.mul_zero] at hmq
        omega
      · exact h
    by_cases hxA : x ≤ a 0
    · exact ⟨m, x, hmM, hqm, hmq, hxA⟩
    · push_neg at hxA
      have hxm : x < m := by
        rw [hmq]
        exact lt_mul_of_one_lt_left hxpos (by have := hq.two_le; omega)
      have hxdvd : x ∣ m := ⟨q, by rw [hmq, mul_comm q x]⟩
      have hxns : ¬ S x := hmM.2 x hxdvd hxm
      obtain ⟨i, hai, hgcd⟩ := hmiss x hxA hxns
      obtain ⟨m1, hm1M, hm1dvd⟩ := hcover (a i) (hgood i)
      have hgxm : Nat.gcd x m1 = 1 := by
        have hdd : Nat.gcd x m1 ∣ Nat.gcd x (a i) :=
          Nat.dvd_gcd (Nat.gcd_dvd_left x m1) (Nat.dvd_trans (Nat.gcd_dvd_right x m1) hm1dvd)
        rw [hgcd] at hdd
        exact Nat.dvd_one.mp hdd
      have hgm1m : 1 < Nat.gcd m m1 := hpair m m1 hmM.1 hm1M.1
      have hgm1mne : Nat.gcd m m1 ≠ 1 := by omega
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgm1mne
      have hpm : p ∣ m := Nat.dvd_trans hpd (Nat.gcd_dvd_left m m1)
      have hpm1 : p ∣ m1 := Nat.dvd_trans hpd (Nat.gcd_dvd_right m m1)
      have hpx : ¬ p ∣ x := by
        intro hpx
        have hgg : p ∣ Nat.gcd x m1 := Nat.dvd_gcd hpx hpm1
        rw [hgxm] at hgg
        exact absurd hgg hp.not_dvd_one
      have hpq : p ∣ q := by
        rcases (hp.dvd_mul).mp (hmq ▸ hpm) with h | h
        · exact h
        · exact absurd h hpx
      have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      have hqm1 : q ∣ m1 := hpeq ▸ hpm1
      have hm1lt : m1 < m := by
        have h1 : m1 ≤ a i := Nat.le_of_dvd (by have := ha1 i; omega) hm1dvd
        omega
      exact ih m1 hm1lt hm1M q hq hqm1
  have hexwit : ∀ c : ℕ, ∃ i : ℕ, (∃ j : ℕ, Nat.gcd c (a j) = 1) → Nat.gcd c (a i) = 1 := by
    intro c
    by_cases h : ∃ j : ℕ, Nat.gcd c (a j) = 1
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose cc2 hcc2 using hexwit
  set N0 : ℕ := ∏ c ∈ Finset.Icc 1 (a 0), a (cc2 c) with hN0
  have hN0pos : 0 < N0 := by
    rw [hN0]
    refine Finset.prod_pos ?_
    intro c _
    have h4 : 1 < a (cc2 c) := ha1 (cc2 c)
    omega
  have hprime_bound : ∀ p, Nat.Prime p → (∃ m, M m ∧ p ∣ m) → p ∣ N0 := by
    intro p hp hpM
    obtain ⟨m, hmM, hpm⟩ := hpM
    obtain ⟨m', c, hm'M, hpm', hm'eq, hcA⟩ := hdescent m hmM p hp hpm
    have hm'0 : 0 < m' := hm'M.1.1
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exfalso
        rw [h, Nat.mul_zero] at hm'eq
        omega
      · exact h
    have hcm' : c ∣ m' := ⟨p, by rw [hm'eq, mul_comm c p]⟩
    have hclt : c < m' := by
      rw [hm'eq]
      exact lt_mul_of_one_lt_left hc0 (by have := hp.two_le; omega)
    have hcns : ¬ S c := hm'M.2 c hcm' hclt
    have hexc : ∃ i : ℕ, Nat.gcd c (a i) = 1 := by
      by_contra hcon
      apply hcns
      refine ⟨hc0, fun i => ?_⟩
      have hne1 : Nat.gcd c (a i) ≠ 1 := fun h => hcon ⟨i, h⟩
      have hpos : 0 < Nat.gcd c (a i) := by
        rcases Nat.eq_zero_or_pos (Nat.gcd c (a i)) with h | h
        · exfalso
          have h0 : 0 ∣ a i := h ▸ Nat.gcd_dvd_right c (a i)
          obtain ⟨w, hw⟩ := h0
          rw [Nat.zero_mul] at hw
          have hai : 1 < a i := ha1 i
          omega
        · exact h
      omega
    have hwit : Nat.gcd c (a (cc2 c)) = 1 := hcc2 c hexc
    have hg1 : 1 < Nat.gcd m' (a (cc2 c)) := hm'M.1.2 (cc2 c)
    have hgne : Nat.gcd m' (a (cc2 c)) ≠ 1 := by omega
    obtain ⟨r, hrp, hrg⟩ := Nat.exists_prime_and_dvd hgne
    have hrm' : r ∣ m' := Nat.dvd_trans hrg (Nat.gcd_dvd_left m' (a (cc2 c)))
    have hra : r ∣ a (cc2 c) := Nat.dvd_trans hrg (Nat.gcd_dvd_right m' (a (cc2 c)))
    have hrc : ¬ r ∣ c := by
      intro hrc
      have hgg : r ∣ Nat.gcd c (a (cc2 c)) := Nat.dvd_gcd hrc hra
      rw [hwit] at hgg
      exact absurd hgg hrp.not_dvd_one
    have hrp_dvd : r ∣ p := by
      rw [hm'eq] at hrm'
      rcases (hrp.dvd_mul).mp hrm' with h | h
      · exact h
      · exact absurd h hrc
    have hrpeq : r = p := (Nat.prime_dvd_prime_iff_eq hrp hp).mp hrp_dvd
    have hpa : p ∣ a (cc2 c) := hrpeq ▸ hra
    have hmem : c ∈ Finset.Icc 1 (a 0) := by
      simp only [Finset.mem_Icc]
      exact ⟨hc0, hcA⟩
    rw [hN0]
    exact Nat.dvd_trans hpa (Finset.dvd_prod_of_mem (fun c => a (cc2 c)) hmem)
  obtain ⟨L, hL0, hLdvd⟩ : ∃ L : ℕ, 0 < L ∧ ∀ m, M m → m ∣ L := by
    set P : Finset ℕ := N0.primeFactors with hP
    refine ⟨∏ p ∈ P, p, ?_, ?_⟩
    · refine Finset.prod_pos ?_
      intro p hp
      rw [hP] at hp
      exact (Nat.prime_of_mem_primeFactors hp).pos
    · intro m hmM
      have hsq : Squarefree m := hsqfree m hmM
      have hmeq : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsq
      have hsub : m.primeFactors ⊆ P := by
        intro p hp
        rw [hP]
        have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
        have hpd : p ∣ N0 := hprime_bound p hpp ⟨m, hmM, hpm⟩
        exact Nat.Prime.mem_primeFactors hpp hpd (by omega)
      rw [← hmeq]
      exact Finset.prod_dvd_prod_of_subset m.primeFactors P id hsub
  have hper : ∀ x : ℕ, 0 < x → (S x ↔ S (x + L)) := by
    intro x hx
    exact statopia_math_node_223591304_f93b617c a ha L hL0 hLdvd x hx
  have hSL : S L := by
    obtain ⟨m, hmM, _⟩ := hcover (a 0) (hgood 0)
    exact hup m L hmM.1 (hLdvd m hmM) hL0
  set T : ℕ := ((Finset.Icc 1 L).filter S).card with hT
  have hTpos : 0 < T := by
    rw [hT]
    refine Finset.card_pos.mpr ⟨L, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hL0, le_rfl⟩, hSL⟩
  have hcount : ∀ x : ℕ, ((Finset.Ioc x (x + L)).filter S).card = T := by
    intro x
    induction x with
    | zero =>
      have hI : Finset.Ioc 0 (0 + L) = Finset.Icc 1 L := by
        ext y
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hI, ← hT]
    | succ k ih =>
      have hsplit1 : Finset.Ioc k (k + L) = insert (k + 1) (Finset.Ioc (k + 1) (k + L)) := by
        ext y
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hsplit2 : Finset.Ioc (k + 1) (k + 1 + L) =
          insert (k + 1 + L) (Finset.Ioc (k + 1) (k + L)) := by
        ext y
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hb1 : k + 1 ∉ Finset.Ioc (k + 1) (k + L) := by
        simp only [Finset.mem_Ioc]
        omega
      have hb2 : k + 1 + L ∉ Finset.Ioc (k + 1) (k + L) := by
        simp only [Finset.mem_Ioc]
        omega
      have hcard : ∀ b : ℕ, b ∉ Finset.Ioc (k + 1) (k + L) →
          ((insert b (Finset.Ioc (k + 1) (k + L))).filter S).card
            = (if S b then ((Finset.Ioc (k + 1) (k + L)).filter S).card + 1
               else ((Finset.Ioc (k + 1) (k + L)).filter S).card) := by
        intro b hb
        by_cases hSb : S b
        · have hfil : (insert b (Finset.Ioc (k + 1) (k + L))).filter S
              = insert b ((Finset.Ioc (k + 1) (k + L)).filter S) := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with rfl | h1
              · exact Or.inl rfl
              · exact Or.inr ⟨h1, h2⟩
            · rintro (rfl | ⟨h1, h2⟩)
              · exact ⟨Or.inl rfl, hSb⟩
              · exact ⟨Or.inr h1, h2⟩
          have hnb : b ∉ (Finset.Ioc (k + 1) (k + L)).filter S := by
            intro h
            rw [Finset.mem_filter] at h
            exact hb h.1
          rw [hfil, if_pos hSb, Finset.card_insert_of_notMem hnb]
        · have hfil : (insert b (Finset.Ioc (k + 1) (k + L))).filter S
              = (Finset.Ioc (k + 1) (k + L)).filter S := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h1 with rfl | h1
              · exact absurd h2 hSb
              · exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨Or.inr h1, h2⟩
          rw [hfil, if_neg hSb]
      rw [hsplit2, hcard (k + 1 + L) hb2, ← ih, hsplit1, hcard (k + 1) hb1]
      by_cases h : S (k + 1)
      · have h' : S (k + 1 + L) := (hper (k + 1) (Nat.succ_pos k)).mp h
        rw [if_pos h', if_pos h]
      · have h' : ¬ S (k + 1 + L) := fun hh => h ((hper (k + 1) (Nat.succ_pos k)).mpr hh)
        rw [if_neg h', if_neg h]
  refine ⟨T, L, hTpos, hL0, ?_⟩
  intro n
  have hexK : ∃ k, a k = a n + L := by
    have hxn : 0 < a n := (hgood n).1
    have h1 : S (a n + L) := (hper (a n) hxn).mp (hgood n)
    have h2 : a 0 ≤ a n + L := by
      have h3 := hle 0 n (Nat.zero_le n)
      omega
    exact (henum (a n + L)).mpr ⟨h1, h2⟩
  set K : ℕ := Nat.find hexK with hK
  have hKspec : a K = a n + L := Nat.find_spec hexK
  have hKne : K = n + T := by
    have hKgt : n < K := by
      by_contra hcon
      push_neg at hcon
      have h1 : a K ≤ a n := hle K n hcon
      have h2 : a n < a K := by rw [hKspec]; omega
      omega
    obtain ⟨d, hd⟩ : ∃ d, K = n + 1 + d := ⟨K - (n + 1), by omega⟩
    have hIcc : ∀ e : ℕ, (Finset.Icc (n + 1) (n + 1 + e)).card = e + 1 := by
      intro e
      induction e with
      | zero =>
        have h1 : Finset.Icc (n + 1) (n + 1 + 0) = insert (n + 1) (∅ : Finset ℕ) := by
          ext y
          simp
        rw [h1, Finset.card_insert_of_notMem (by simp)]
        simp
      | succ j ih =>
        have h2 : Finset.Icc (n + 1) (n + 1 + (j + 1)) =
            insert (n + 1 + (j + 1)) (Finset.Icc (n + 1) (n + 1 + j)) := by
          ext y
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnm : n + 1 + (j + 1) ∉ Finset.Icc (n + 1) (n + 1 + j) := by
          simp only [Finset.mem_Icc]
          omega
        rw [h2, Finset.card_insert_of_notMem hnm, ih]
    rw [hd] at hKspec
    have hset : (Finset.Ioc (a n) (a n + L)).filter S =
        (Finset.Icc (n + 1) (n + 1 + d)).image a := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy1, hy2⟩, hyS⟩
        have hAy : a 0 ≤ y := by
          have h0 := hle 0 n (Nat.zero_le n)
          omega
        obtain ⟨i, hi⟩ := (henum y).mpr ⟨hyS, hAy⟩
        have hni : n < i := by
          by_contra hc
          push_neg at hc
          have h1 := hle i n hc
          omega
        have hik : i ≤ n + 1 + d := by
          by_contra hc
          push_neg at hc
          have h1 : a (n + 1 + d) < a i := hmono (n + 1 + d) i hc
          omega
        exact ⟨i, ⟨by omega, hik⟩, hi⟩
      · rintro ⟨i, ⟨hi1, hi2⟩, hiy⟩
        have h1 : a n < y := by
          rw [← hiy]
          exact hmono n i (by omega)
        have h2 : y ≤ a n + L := by
          rw [← hiy]
          have h3 : a i ≤ a (n + 1 + d) := hle i (n + 1 + d) hi2
          omega
        exact ⟨⟨h1, h2⟩, hiy ▸ hgood i⟩
    have hcard1 : ((Finset.Ioc (a n) (a n + L)).filter S).card = T := hcount (a n)
    have hcard2 : ((Finset.Ioc (a n) (a n + L)).filter S).card = d + 1 := by
      rw [hset, Finset.card_image_of_injective (Finset.Icc (n + 1) (n + 1 + d)) hinj]
      exact hIcc d
    have hTeq : T = d + 1 := by
      rw [← hcard1]
      exact hcard2
    omega
  rw [← hKne, hKspec]
  /- @proof-region region.root.0877d6e4cecb end -/
