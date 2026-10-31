import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Vocabulary
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.ProvedNodes
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Base

open scoped BigOperators
namespace Statlib.Imported

theorem paper_26cf7ed67549489c93e7ce6890ea6ef9
    (p : ℝ) (hp : 1 < p) (s : ℕ) (hs : 2 ≤ s) (n : ℕ) (hn : s ≤ n) :
    Finset.sum (Fs s n)
        (fun a => ((n : ℝ) / ∏ i : Fin s, (((a i : ℕ) : ℝ) + 1)) ^ p)
      < (Cp p) ^ (s - 1)
:= by
  /- @proof-region region.root.fe29c1112c8d begin -/
  obtain ⟨-, hζpos, -, -⟩ := statopia_math_node_424820995_9497e1fc p hp
  have hC : 0 < Cp p := by
    unfold Cp
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) p) hζpos
  have hbase := statopia_math_node_3049368524_c5ddb727 p hp
  have hrec := statopia_math_node_376226592_f56e194e p
  let T : ℕ → ℕ → ℝ := fun k m =>
    Finset.sum (Fs k m) (fun a => ((m : ℝ) / ∏ i : Fin k, (((a i : ℕ) : ℝ) + 1)) ^ p)
  have hT1 : ∀ m : ℕ, 1 ≤ m → T 1 m = 1 := by
    intro m hm
    have hFs : Fs 1 m = {fun _ => (⟨m - 1, by omega⟩ : Fin m)} := by
      ext a
      simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        funext i
        obtain rfl : i = 0 := Subsingleton.elim i 0
        have h2 : (a 0 : ℕ) + 1 = m := by simpa [Fin.sum_univ_one] using h
        have h3 : (a 0 : ℕ) = m - 1 := by omega
        exact Fin.ext (by simpa using h3)
      · intro h
        rw [h]
        simpa [Fin.sum_univ_one] using Nat.sub_add_cancel hm
    show Finset.sum (Fs 1 m) (fun a : Fin 1 → Fin m => ((m : ℝ) / ∏ i : Fin 1, (((a i : ℕ) : ℝ) + 1)) ^ p) = 1
    rw [hFs, Finset.sum_singleton]
    have hprod : (∏ i : Fin 1, ((((fun _ : Fin 1 => (⟨m - 1, by omega⟩ : Fin m)) i : ℕ) : ℝ) + 1)) = (m : ℝ) := by
      rw [Fin.prod_univ_one]
      show (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ)
      have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
        have h2 : (m - 1) + 1 = m := Nat.sub_add_cancel hm
        exact_mod_cast h2
      simpa using hcast
    rw [hprod]
    have hm0 : (m : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
      exact h.ne'
    rw [div_self hm0]
    simp
  have key : ∀ e n : ℕ, 2 + e ≤ n → T (2 + e) n < (Cp p) ^ (2 + e - 1) := by
    intro e
    induction e with
    | zero =>
        intro n hn
        have hn2 : 2 ≤ n := by omega
        have hrec1 := hrec 1 (by norm_num) n (by omega)
        have hbase' := hbase n hn2
        calc T (2 + 0) n
            = Finset.sum (Finset.Icc 1 (n - 1)) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p * T 1 (n - b)) := hrec1.1
          _ = Finset.sum (Finset.Icc 1 (n - 1)) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p) := by
                apply Finset.sum_congr rfl
                intro b hb
                rw [Finset.mem_Icc] at hb
                rw [hT1 (n - b) (by omega), mul_one]
          _ = Finset.sum (Finset.Icc 1 (n - 1)) (fun b => ((n : ℝ) / ((b : ℝ) * ((n - b : ℕ) : ℝ))) ^ p) := by
                apply Finset.sum_congr rfl
                intro b _
                rw [mul_comm ((n - b : ℕ) : ℝ) (b : ℝ)]
          _ < Cp p := hbase'
          _ = (Cp p) ^ (2 + 0 - 1) := by
                rw [show 2 + 0 - 1 = 1 by norm_num, pow_one]
    | succ e ih =>
        intro n hn
        have hW : Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p) < Cp p := by
          calc Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p)
              = Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / ((b : ℝ) * ((n - b : ℕ) : ℝ))) ^ p) := by
                  apply Finset.sum_congr rfl
                  intro b _
                  rw [mul_comm ((n - b : ℕ) : ℝ) (b : ℝ)]
            _ ≤ Finset.sum (Finset.Icc 1 (n - 1)) (fun a => ((n : ℝ) / ((a : ℝ) * ((n - a : ℕ) : ℝ))) ^ p) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro x hx
                    rw [Finset.mem_Icc] at hx ⊢
                    omega
                  · intro x _ _
                    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg n) (mul_nonneg (Nat.cast_nonneg x) (Nat.cast_nonneg (n - x)))) p
            _ < Cp p := hbase n (by omega)
        have hrec' := hrec (2 + e) (by omega) n (by omega)
        calc T (2 + (e + 1)) n
            = Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p * T (2 + e) (n - b)) := hrec'.1
          _ < Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p * (Cp p) ^ (2 + e - 1)) := by
                apply Finset.sum_lt_sum_of_nonempty
                · exact ⟨1, by rw [Finset.mem_Icc]; omega⟩
                · intro b hb
                  rw [Finset.mem_Icc] at hb
                  have hIH : T (2 + e) (n - b) < (Cp p) ^ (2 + e - 1) := ih (n - b) (by omega)
                  have hw : 0 < ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p := hrec'.2 b (by rw [Finset.mem_Icc]; exact hb)
                  exact mul_lt_mul_of_pos_left hIH hw
          _ = (Cp p) ^ (2 + e - 1) * Finset.sum (Finset.Icc 1 (n - (2 + e))) (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro b _
                ring
          _ < (Cp p) ^ (2 + e - 1) * Cp p := mul_lt_mul_of_pos_left hW (pow_pos hC _)
          _ = (Cp p) ^ (2 + (e + 1) - 1) := by
                rw [show 2 + (e + 1) - 1 = 2 + e - 1 + 1 by omega, pow_succ]
  have hfin := key (s - 2) n (by omega)
  rw [show 2 + (s - 2) = s by omega] at hfin
  exact hfin
  /- @proof-region region.root.fe29c1112c8d end -/

end Statlib.Imported
