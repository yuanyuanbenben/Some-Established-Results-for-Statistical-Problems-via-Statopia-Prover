import ProverJobs.real_main_theorem_edd06e2c7e6c.Vocabulary
import ProverJobs.real_main_theorem_edd06e2c7e6c.Base
import ProverJobs.real_main_theorem_edd06e2c7e6c.ProvedNodes.Node_3776635361_5eaf0306_47c63d95


set_option autoImplicit false in
theorem statopia_math_node_1231998112_26c8ceab : ∀ (a : ℕ → ℕ) (ha : IsValidSeq a),
    let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
    let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
    M.Nonempty ∧
    (∀ x : ℕ, S x → ∃ m ∈ M, m ∣ x) ∧
    (∀ x : ℕ, 0 < x → (S x ↔ ∃ m ∈ M, m ∣ x)) := by
  /- @proof-region region.target-node.session.de34ec3f6c9fb93b begin -/
  intro a ha
  obtain ⟨-, -, -, -, -, hgood, hup, -⟩ := statopia_math_node_3776635361_5eaf0306 a ha
  let S : ℕ → Prop := fun x => 0 < x ∧ ∀ i : ℕ, 1 < Nat.gcd x (a i)
  let M : Set ℕ := {m : ℕ | S m ∧ ∀ d : ℕ, d ∣ m → d < m → ¬ S d}
  have key : ∀ x : ℕ, S x → ∃ m ∈ M, m ∣ x := by
    intro x
    refine Nat.strong_induction_on (p := fun n => S n → ∃ m ∈ M, m ∣ n) x ?_
    intro n ih hx
    by_cases h : ∃ d : ℕ, d ∣ n ∧ d < n ∧ S d
    · obtain ⟨d, hdn, hdlt, hSd⟩ := h
      obtain ⟨m, hmM, hmd⟩ := ih d hdlt hSd
      exact ⟨m, hmM, dvd_trans hmd hdn⟩
    · exact ⟨n, ⟨hx, fun d hdn hdlt hSd => h ⟨d, hdn, hdlt, hSd⟩⟩, dvd_refl n⟩
  refine ⟨?_, key, ?_⟩
  · obtain ⟨m, hmM, -⟩ := key (a 0) (hgood 0)
    exact ⟨m, hmM⟩
  · intro x hxpos
    constructor
    · intro hx
      exact key x hx
    · rintro ⟨m, hmM, hmx⟩
      exact hup m x hmM.1 hmx hxpos
  /- @proof-region region.target-node.session.de34ec3f6c9fb93b end -/
