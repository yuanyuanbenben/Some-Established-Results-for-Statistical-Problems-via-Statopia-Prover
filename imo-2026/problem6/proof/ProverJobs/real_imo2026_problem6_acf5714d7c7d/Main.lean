import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Vocabulary
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.ProvedNodes
import ProverJobs.real_imo2026_problem6_acf5714d7c7d.Base

namespace IMO2026P6

theorem imo2026_problem6 (a : Nat -> Nat) (ha : IsValidSeq a) :
    exists T L : Nat, 0 < T ∧ 0 < L ∧
      forall n, a (n + T) = a n + L
:= by
  /- @proof-region region.root.74da9e54ef86 begin -/
  have hmono : ∀ i j, i ≤ j → a i ≤ a j := by
    intro i j hij
    induction hij with
    | refl => exact le_refl (a i)
    | step _ ih => exact le_trans ih (le_of_lt (ha.2 _).1)
  have hbnd : ∀ n, a 0 + n ≤ a n := by
    intro n
    induction n with
    | zero => exact le_refl (a 0)
    | succ n ih => exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (ha.2 n).1)
  have hbound : ∀ n, n ≤ a n := by
    intro n
    have := hbnd n
    omega
  have hgcd_pairs : ∀ n m, 1 < Nat.gcd (a n) (a m) := by
    intro n m
    rcases lt_trichotomy n m with h | h | h
    · have hrec := (ha.2 (m - 1)).2.1 n (by omega)
      have hm : m - 1 + 1 = m := by omega
      rw [hm, Nat.gcd_comm] at hrec
      exact hrec
    · subst h
      rw [Nat.gcd_self]
      exact ha.1 n
    · have hrec := (ha.2 (n - 1)).2.1 m (by omega)
      have hn : n - 1 + 1 = n := by omega
      rw [hn] at hrec
      exact hrec
  have hgood : ∀ n, 1 < a n ∧ ∀ m, 1 < Nat.gcd (a n) (a m) :=
    fun n => ⟨ha.1 n, fun m => hgcd_pairs n m⟩
  have henumerate : ∀ b, a 0 ≤ b → (1 < b ∧ ∀ n, 1 < Nat.gcd b (a n)) → ∃ k, a k = b := by
    intro b hb hV
    have hex : ∃ k, b ≤ a k := ⟨b, hbound b⟩
    have hk : b ≤ a (Nat.find hex) := Nat.find_spec hex
    have hkmin : ∀ m, m < Nat.find hex → ¬ b ≤ a m := by
      intro m hm hle
      exact absurd (Nat.find_min' hex hle) (not_le.mpr hm)
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hkpos
    · rw [hk0] at hk
      exact ⟨0, le_antisymm hb hk⟩
    · by_cases hbeq : b = a (Nat.find hex)
      · exact ⟨Nat.find hex, hbeq.symm⟩
      · have hblt : b < a (Nat.find hex) := lt_of_le_of_ne hk hbeq
        have hprev : a (Nat.find hex - 1) < b :=
          Nat.lt_of_not_le (hkmin (Nat.find hex - 1) (by omega))
        have hk1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        have hblt' : b < a (Nat.find hex - 1 + 1) := by rw [hk1]; exact hblt
        obtain ⟨i, _, higcd⟩ := (ha.2 (Nat.find hex - 1)).2.2 b hprev hblt'
        have h1 := hV.2 i
        rw [higcd] at h1
        exact absurd h1 (Nat.lt_irrefl 1)
  obtain ⟨L, hLpos, htrans⟩ := statopia_math_node_2415587922_861ebcd7 a ha
  have hBplus : 1 < a 0 + L ∧ ∀ n, 1 < Nat.gcd (a 0 + L) (a n) :=
    (htrans (a 0) (le_refl _)).1 (hgood 0)
  obtain ⟨T, hT⟩ := henumerate (a 0 + L) (by omega) hBplus
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · exfalso
      rw [h0] at hT
      omega
    · exact hpos
  have hperiod : ∀ n, a (n + T) = a n + L := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih =>
      have hle_n1 : a 0 ≤ a (n + 1) := hmono 0 (n + 1) (Nat.zero_le _)
      have hxgood : 1 < a (n + 1) + L ∧ ∀ m, 1 < Nat.gcd (a (n + 1) + L) (a m) :=
        (htrans (a (n + 1)) hle_n1).1 (hgood (n + 1))
      have hxge : a 0 ≤ a (n + 1) + L := by omega
      obtain ⟨k, hk⟩ := henumerate (a (n + 1) + L) hxge hxgood
      have hA : a (n + T) < a (n + 1) + L := by
        rw [ih]
        have := (ha.2 n).1
        omega
      have hlt : a (n + T) < a k := by rw [hk]; exact hA
      have hkgt : n + T < k := by
        by_contra hcon
        push_neg at hcon
        exact absurd hlt (not_lt.mpr (hmono k (n + T) hcon))
      have hle_ak : a (n + T + 1) ≤ a k := hmono (n + T + 1) k (by omega)
      have hgoal_eq : a (n + T + 1) = a (n + 1) + L := by
        rcases lt_or_eq_of_le hle_ak with hlt2 | heq2
        · exfalso
          have hltx : a (n + T + 1) < a (n + 1) + L := by rw [hk] at hlt2; exact hlt2
          have hbig : a n + L < a (n + T + 1) := by
            rw [← ih]
            exact (ha.2 (n + T)).1
          have hLle : L ≤ a (n + T + 1) := by omega
          have hbeq : (a (n + T + 1) - L) + L = a (n + T + 1) := Nat.sub_add_cancel hLle
          have han : a 0 ≤ a n := hmono 0 n (Nat.zero_le n)
          have hbge : a 0 ≤ a (n + T + 1) - L := by omega
          have hblt : a (n + T + 1) - L < a (n + 1) := by omega
          have hbgt : a n < a (n + T + 1) - L := by omega
          have hTgood : 1 < a (n + T + 1) ∧ ∀ m, 1 < Nat.gcd (a (n + T + 1)) (a m) :=
            hgood (n + T + 1)
          rw [← hbeq] at hTgood
          have hbg : 1 < a (n + T + 1) - L ∧ ∀ m, 1 < Nat.gcd (a (n + T + 1) - L) (a m) :=
            (htrans (a (n + T + 1) - L) hbge).2 hTgood
          obtain ⟨j, hj⟩ := henumerate (a (n + T + 1) - L) hbge hbg
          have h1 : a n < a j := by rw [hj]; exact hbgt
          have h2 : a j < a (n + 1) := by rw [hj]; exact hblt
          have hnj : n < j := by
            by_contra hc
            push_neg at hc
            exact absurd h1 (not_lt.mpr (hmono j n hc))
          have hjn : j < n + 1 := by
            by_contra hc
            push_neg at hc
            exact absurd h2 (not_lt.mpr (hmono (n + 1) j hc))
          omega
        · rw [hk] at heq2; exact heq2
      have hidx : Nat.succ n + T = n + T + 1 := by omega
      rw [hidx]; exact hgoal_eq
  exact ⟨T, L, hTpos, hLpos, hperiod⟩
  /- @proof-region region.root.74da9e54ef86 end -/

end IMO2026P6
