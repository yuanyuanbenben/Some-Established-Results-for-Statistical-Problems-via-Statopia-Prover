import ProverJobs.real_main_theorem_d734bdb6a642.Vocabulary
import ProverJobs.real_main_theorem_d734bdb6a642.Base
import ProverJobs.real_main_theorem_d734bdb6a642.ProvedNodes.Node_894036796_c5e882c6_f47ff87a

set_option autoImplicit false in
theorem statopia_math_node_1648340497_660d8830 : ∀ (f : PositiveReal → PositiveReal)
    (hf : IsAdmissible f) (t : PositiveReal), (f t : ℝ) ≥ (t : ℝ) := by
  /- @proof-region region.target-node.session.a13d7dadb6ec7dd1 begin -/
  intro f hf t
  let d : ℝ := (f t : ℝ) - (t : ℝ)
  have hd : d = (f t : ℝ) - (t : ℝ) := rfl
  let z : ℕ → PositiveReal := fun n => Nat.rec t (fun _ w => f w) n
  have hz0 : z 0 = t := rfl
  have hzsucc : ∀ n : ℕ, z (n + 1) = f (z n) := fun n => rfl
  have hrec : ∀ s : PositiveReal, (f (f s) : ℝ) = 2 * (f s : ℝ) - (s : ℝ) :=
    fun s => statopia_math_node_894036796_c5e882c6 f hf s
  have hdiff : ∀ n : ℕ, (z (n + 1)).val - (z n).val = d := by
    intro n
    induction n with
    | zero =>
        rw [hzsucc 0, hz0, hd]
    | succ k ih =>
        show (z (k + 1 + 1)).val - (z (k + 1)).val = d
        have hr : (f (f (z k))).val = 2 * (f (z k)).val - (z k).val := hrec (z k)
        calc (z (k + 1 + 1)).val - (z (k + 1)).val
            = (f (f (z k))).val - (f (z k)).val := by rw [hzsucc (k + 1), hzsucc k]
          _ = (2 * (f (z k)).val - (z k).val) - (f (z k)).val := by rw [hr]
          _ = (f (z k)).val - (z k).val := by ring
          _ = (z (k + 1)).val - (z k).val := by rw [hzsucc k]
          _ = d := ih
  have hform : ∀ n : ℕ, (z n).val = (t : ℝ) + (n : ℝ) * d := by
    intro n
    induction n with
    | zero =>
        rw [hz0]
        simp
    | succ k ih =>
        show (z (k + 1)).val = (t : ℝ) + (↑(k + 1) : ℝ) * d
        have hk : (z (k + 1)).val = (z k).val + d := by linarith [hdiff k]
        rw [hk, ih]
        push_cast
        ring
  have hdnn : 0 ≤ d := by
    by_contra h
    have hneg : d < 0 := not_le.mp h
    have hpos : 0 < -d := by linarith
    have htpos : 0 < (t : ℝ) := t.2
    obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / (-d))
    have hlt : (t : ℝ) < (n : ℝ) * (-d) := by
      have h1 := mul_lt_mul_of_pos_right hn hpos
      rwa [div_mul_cancel₀ (t : ℝ) (ne_of_gt hpos)] at h1
    have hzn : (z n).val < 0 := by
      rw [hform n]
      nlinarith [hlt]
    have hzpos : 0 < (z n).val := (z n).2
    linarith
  linarith [hdnn, hd]
  /- @proof-region region.target-node.session.a13d7dadb6ec7dd1 end -/
