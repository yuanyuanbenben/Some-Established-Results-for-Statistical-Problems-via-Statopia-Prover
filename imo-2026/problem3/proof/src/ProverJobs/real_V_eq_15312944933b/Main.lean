import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.MainSupport
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
namespace LiuBangXiangYu

theorem V_eq (n : ℕ) (hn : 0 < n) : V n = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)
:= by
  /- @proof-region region.root.f13d7bc3ef09 begin -/
  have hEmpty : AdmissibleMark n (∅ : Finset ℝ) := by simp [AdmissibleMark]
  haveI : Nonempty {A : Finset ℝ // AdmissibleMark n A} := ⟨⟨∅, hEmpty⟩⟩
  have hLnn : ∀ (A B : Finset ℝ), AdmissibleMark n A → AdmissibleMark n B → 0 ≤ L A B :=
    statopia_math_node_1288731108_fe11829c n
  have hbddBelow : ∀ A : {A : Finset ℝ // AdmissibleMark n A},
      BddBelow (Set.range (fun B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1)) := by
    intro A
    exact ⟨0, by rintro x ⟨B, rfl⟩; exact hLnn A.1 B.1 A.2 B.2.1⟩
  have hn1 : 1 ≤ n := by omega
  have hle_all : ∀ A : {A : Finset ℝ // AdmissibleMark n A},
      (⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) ≤
        (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
    intro A
    obtain ⟨BA, hBA, hBdisj, hLB⟩ := statopia_math_node_1763956908_225d779d n hn1 A.1 A.2
    calc (⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1)
        ≤ L A.1 BA := ciInf_le (hbddBelow A) ⟨BA, hBA, hBdisj⟩
      _ ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := hLB
  have hupper : V n ≤ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by
    unfold V
    apply ciSup_le
    intro A
    exact hle_all A
  let A0 : Finset ℝ := (Finset.Icc 1 n).image (fun j : ℕ => (1 / ((2 : ℝ) ^ (n + 1) - 1)) * ((2 : ℝ) ^ j - 1))
  have key := statopia_math_node_3641882566_571fb3c0 n hn
  have hA0adm : AdmissibleMark n A0 := key.1
  have hA0lower : ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A0 B →
      L A0 B ≥ (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := key.2
  haveI : Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A0 B} :=
    ⟨⟨∅, hEmpty, by simp [Disjoint]⟩⟩
  have hlow_inf : (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 ≤
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A0 B}, L A0 B.1 := by
    apply le_ciInf
    intro B
    exact hA0lower B.1 B.2.1 B.2.2
  have hsup_up : BddAbove (Set.range (fun A : {A : Finset ℝ // AdmissibleMark n A} =>
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1)) :=
    ⟨(1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2,
      by rintro x ⟨A, rfl⟩; exact hle_all A⟩
  have hlow : (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 ≤ V n := by
    calc (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2
        ≤ ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A0 B}, L A0 B.1 := hlow_inf
      _ ≤ V n := le_ciSup hsup_up ⟨A0, hA0adm⟩
  have hV : V n = (1 + (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := le_antisymm hupper hlow
  rw [hV]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) - 1 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [pow_succ]
  rw [pow_succ] at hpos
  field_simp
  ring
  /- @proof-region region.root.f13d7bc3ef09 end -/

end LiuBangXiangYu
