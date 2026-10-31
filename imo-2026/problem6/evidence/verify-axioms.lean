import ProverJobs.real_main_theorem_edd06e2c7e6c.Main

example : IsValidSeq = (fun a : ℕ → ℕ =>
    (∀ n, 1 < a n) ∧
    (∀ n, a n < a (n + 1) ∧
      (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
      (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))) := rfl

example (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L :=
  main_theorem a ha

#print axioms main_theorem
