import ProverJobs.real_main_theorem_f979009c9fbd.Vocabulary
import ProverJobs.real_main_theorem_f979009c9fbd.Base


set_option autoImplicit false in
theorem statopia_math_node_1799194065_328e73c0 : ∀ (B B' : Board) (h : Move B B')
    (p : ℕ) (hp : p.Prime), gExp p B' = gExp p B := by
  /- @proof-region region.target-node.session.bf1943962f5305da begin -/
  intro B B' h p hp
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := h
  subst hB
  subst hB'
  unfold gExp
  simp only [Multiset.map_cons, Multiset.gcd_cons]
  have euc : ∀ a b : ℕ, Nat.gcd a b = Nat.gcd (min a b) (max a b - min a b) := by
    intro a b
    rcases le_total a b with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]
      have hb : b = (b - a) + a := by omega
      conv_lhs => rw [hb]
      exact Nat.gcd_add_self_right a (b - a)
    · rw [min_eq_right hle, max_eq_left hle]
      have ha : a = (a - b) + b := by omega
      rw [Nat.gcd_comm a b]
      conv_lhs => rw [ha]
      exact Nat.gcd_add_self_right b (a - b)
  have hd : padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
    have h1 : (Nat.gcd m n).factorization p = min (m.factorization p) (n.factorization p) := by
      rw [Nat.factorization_gcd (by omega : m ≠ 0) (by omega : n ≠ 0)]
      simp
    rwa [Nat.factorization_def (Nat.gcd m n) hp, Nat.factorization_def m hp,
      Nat.factorization_def n hp] at h1
  have hl : padicValNat p (Nat.lcm m n) = max (padicValNat p m) (padicValNat p n) := by
    have h1 : (Nat.lcm m n).factorization p = max (m.factorization p) (n.factorization p) := by
      rw [Nat.factorization_lcm (by omega : m ≠ 0) (by omega : n ≠ 0)]
      simp
    rwa [Nat.factorization_def (Nat.lcm m n) hp, Nat.factorization_def m hp,
      Nat.factorization_def n hp] at h1
  have hlpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
  have hgl : Nat.gcd m n ∣ Nat.lcm m n :=
    dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_lcm_left m n)
  have hm0 : Nat.gcd m n ≠ 0 := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m n
    intro h
    rw [h] at hk
    simp at hk
    omega
  have hq0 : Nat.lcm m n / Nat.gcd m n ≠ 0 := by
    intro h
    have h1 : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
      Nat.mul_div_cancel' hgl
    rw [h, mul_zero] at h1
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hprod : padicValNat p (Nat.gcd m n) + padicValNat p (Nat.lcm m n / Nat.gcd m n)
      = padicValNat p (Nat.lcm m n) := by
    rw [← padicValNat.mul hm0 hq0, Nat.mul_div_cancel' hgl]
  have hq : padicValNat p (Nat.lcm m n / Nat.gcd m n)
      = max (padicValNat p m) (padicValNat p n)
        - min (padicValNat p m) (padicValNat p n) := by
    omega
  have key : Nat.gcd (padicValNat p (Nat.gcd m n))
        (padicValNat p (Nat.lcm m n / Nat.gcd m n))
      = Nat.gcd (padicValNat p m) (padicValNat p n) := by
    rw [hd, hq]
    exact (euc (padicValNat p m) (padicValNat p n)).symm
  have fin : ∀ a b c e G : ℕ, Nat.gcd a b = Nat.gcd c e →
      Nat.gcd a (Nat.gcd b G) = Nat.gcd c (Nat.gcd e G) := by
    intro a b c e G hk
    rw [← Nat.gcd_assoc, ← Nat.gcd_assoc, hk]
  exact fin _ _ _ _ _ key
  /- @proof-region region.target-node.session.bf1943962f5305da end -/
