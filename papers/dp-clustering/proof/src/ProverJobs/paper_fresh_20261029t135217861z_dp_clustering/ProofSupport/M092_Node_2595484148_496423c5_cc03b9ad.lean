import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M091_Node_4081398995_d2b977a1_d7f763cf

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_2595484148_496423c5_cc03b9ad; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2595484148_496423c5 : ∀ (n t : ℕ) (ht : 0 < t) (htn : t + 1 ≤ n)
    (m M rho : ℝ) (hm : 0 < m) (hmM : m ≤ M) (hrho : 0 ≤ rho)
    (mb : Finset (Fin n) → ℝ)
    (hnonneg : ∀ B : Finset (Fin n), 0 ≤ mb B)
    (hdom : ∀ (B : Finset (Fin n)) (i : Fin n), i ∈ B → mb B ≤ M * mb (B.erase i))
    (hpoint : ∀ i : Fin n, m * rho ≤ mb {i}),
    (m * rho / M) *
        (∑ A ∈ tau n t, (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, mb B))
      ≤ ((t : ℝ) * ((t : ℝ) + 1)) *
        (∑ A' ∈ tau n (t + 1),
          (∏ B ∈ A', ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A', mb B)) := by
  /- @proof-region region.target-node.session.42e5bc16b430d4c5 begin -/
  intro n t ht htn m M rho hm hmM hrho mb hnonneg hdom hpoint
  classical
  let wb : Finset (Fin n) → ℝ := fun B => ((B.card - 1).factorial : ℝ) * mb B
  have hwb : wb = fun B => ((B.card - 1).factorial : ℝ) * mb B := rfl
  let W : Finset (Finset (Fin n)) → ℝ := fun A => ∏ B ∈ A, wb B
  have hW : W = fun A => ∏ B ∈ A, wb B := rfl
  have hWform : ∀ A : Finset (Finset (Fin n)),
      (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, mb B) = W A := by
    intro A
    rw [hW, hwb]
    simp only [Finset.prod_mul_distrib]
  simp only [hWform]
  have hWnn : ∀ A : Finset (Finset (Fin n)), 0 ≤ W A := by
    intro A
    rw [hW]
    exact Finset.prod_nonneg (fun B _ => mul_nonneg (by positivity) (hnonneg B))
  have hmem_tau : ∀ {s : ℕ} {A : Finset (Finset (Fin n))}, A ∈ tau n s → IsPartitionOf n s A := by
    intro s A hA
    simp only [tau, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at hA
    exact hA
  have hcard_tau : ∀ {s : ℕ} {A : Finset (Finset (Fin n))}, A ∈ tau n s → A.card = s := by
    intro s A hA
    exact (hmem_tau hA).1
  let splitBlk : Finset (Finset (Fin n)) → Finset (Fin n) → Fin n → Finset (Finset (Fin n)) :=
    fun A B i => insert {i} (insert (B.erase i) (A.erase B))
  have hsplitBlk : splitBlk = fun A B i => insert {i} (insert (B.erase i) (A.erase B)) := rfl
  have hwb_sing : ∀ i : Fin n, wb {i} = mb {i} := by
    intro i
    rw [hwb]
    simp
  have hW_erase : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)), B ∈ A →
      W A = wb B * ∏ D ∈ A.erase B, wb D := by
    intro A B hB
    rw [hW]
    exact (Finset.mul_prod_erase A wb hB).symm
  have hWsplit : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)) (i : Fin n),
      IsPartitionOf n t A → B ∈ A → i ∈ B → 2 ≤ B.card →
      W (splitBlk A B i) = mb {i} * (wb (B.erase i) * ∏ D ∈ A.erase B, wb D) := by
    intro A B i hpart hB hi h2
    have hBne : B.erase i ≠ B := by
      intro heq
      have h1 : (B.erase i).card = B.card := by rw [heq]
      rw [Finset.card_erase_of_mem hi] at h1
      omega
    have hBpos : 0 < (B.erase i).card := by
      rw [Finset.card_erase_of_mem hi]
      omega
    have hB'notin : B.erase i ∉ A.erase B := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hneB, hmemA⟩ := hmem
      have hdisj := hpart.2.2.1 (B.erase i) hmemA B hB hneB
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hBpos
      exact (Finset.disjoint_left.1 hdisj) hx (Finset.mem_erase.1 hx).2
    have hsing_ne : ({i} : Finset (Fin n)) ≠ B.erase i := by
      intro heq
      have hmem : i ∈ B.erase i := by rw [← heq]; exact Finset.mem_singleton_self i
      exact (Finset.mem_erase.1 hmem).1 rfl
    have hsing_notinA : ({i} : Finset (Fin n)) ∉ A.erase B := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hneB, hmemA⟩ := hmem
      have hdisj := hpart.2.2.1 ({i} : Finset (Fin n)) hmemA B hB hneB
      exact (Finset.disjoint_left.1 hdisj) (Finset.mem_singleton_self i) (by simpa using hi)
    have h1 : ({i} : Finset (Fin n)) ∉ insert (B.erase i) (A.erase B) := by
      rw [Finset.mem_insert]
      exact fun h => h.elim hsing_ne hsing_notinA
    have hgoal : (∏ D ∈ insert {i} (insert (B.erase i) (A.erase B)), wb D)
        = mb {i} * (wb (B.erase i) * ∏ D ∈ A.erase B, wb D) := by
      rw [Finset.prod_insert h1, Finset.prod_insert hB'notin, hwb_sing i]
    rw [hsplitBlk, hW]
    exact hgoal
  have hMi : 0 < M := lt_of_lt_of_le hm hmM
  have hMM : (m * rho / M) * M = m * rho := by
    have hMne : M ≠ 0 := hMi.ne'
    field_simp
  have hkey : ∀ (B : Finset (Fin n)) (i : Fin n), i ∈ B →
      (m * rho / M) * mb B ≤ mb {i} * mb (B.erase i) := by
    intro B i hi
    have hmn : 0 ≤ m * rho / M :=
      div_nonneg (mul_nonneg (le_of_lt hm) hrho) (le_of_lt hMi)
    have h3 : mb B ≤ M * mb (B.erase i) := hdom B i hi
    calc (m * rho / M) * mb B
        ≤ (m * rho / M) * (M * mb (B.erase i)) := mul_le_mul_of_nonneg_left h3 hmn
      _ = (m * rho) * mb (B.erase i) := by
            rw [← mul_assoc, hMM]
      _ ≤ mb {i} * mb (B.erase i) :=
            mul_le_mul_of_nonneg_right (hpoint i) (hnonneg (B.erase i))
  have hfact : ∀ (B : Finset (Fin n)), 2 ≤ B.card →
      ((B.card - 1).factorial : ℝ) = ((B.card : ℝ) - 1) * ((B.card - 2).factorial : ℝ) := by
    intro B h2
    have hcard : B.card - 2 + 1 = B.card - 1 := by omega
    have h1 : ((B.card - 1).factorial : ℝ)
        = (((B.card - 2 + 1) * (B.card - 2).factorial : ℕ) : ℝ) := by
      rw [← hcard, Nat.factorial_succ]
    have h2' : (((B.card - 2 + 1) * (B.card - 2).factorial : ℕ) : ℝ)
        = ((B.card - 2 + 1 : ℕ) : ℝ) * ((B.card - 2).factorial : ℝ) := by
      push_cast
      ring
    have h3 : ((B.card - 2 + 1 : ℕ) : ℝ) = (B.card : ℝ) - 1 := by
      have hc : ((B.card - 2 : ℕ) : ℝ) = (B.card : ℝ) - 2 := by
        have h := Nat.cast_sub (R := ℝ) h2
        simpa using h
      rw [Nat.cast_add, Nat.cast_one, hc]
      ring
    rw [h1, h2', h3]
  have hwbE : ∀ (B : Finset (Fin n)) (i : Fin n), i ∈ B →
      wb (B.erase i) = ((B.card - 2).factorial : ℝ) * mb (B.erase i) := by
    intro B i hi
    have hcard : (B.erase i).card = B.card - 1 := Finset.card_erase_of_mem hi
    have hc2 : B.card - 1 - 1 = B.card - 2 := by omega
    show (((B.erase i).card - 1).factorial : ℝ) * mb (B.erase i)
        = ((B.card - 2).factorial : ℝ) * mb (B.erase i)
    rw [hcard, hc2]
  have hWcmp : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)) (i : Fin n),
      IsPartitionOf n t A → B ∈ A → i ∈ B → 2 ≤ B.card →
      (m * rho / M) * W A ≤ ((B.card : ℝ) - 1) * W (splitBlk A B i) := by
    intro A B i hpart hB hi h2
    have hP : 0 ≤ ∏ D ∈ A.erase B, wb D :=
      Finset.prod_nonneg (f := wb) fun D _ => by
        rw [hwb]
        exact mul_nonneg (by positivity) (hnonneg D)
    have hb1 : (0:ℝ) ≤ (B.card : ℝ) - 1 := by
      have hc : (1:ℝ) ≤ (B.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ B.card)
      linarith
    have hK : 0 ≤ ((B.card : ℝ) - 1) * ((B.card - 2).factorial : ℝ) * (∏ D ∈ A.erase B, wb D) :=
      mul_nonneg (mul_nonneg hb1 (by positivity)) hP
    have hwbB : wb B = ((B.card - 1).factorial : ℝ) * mb B := by rw [hwb]
    calc (m * rho / M) * W A
        = ((m * rho / M) * mb B)
            * (((B.card : ℝ) - 1) * ((B.card - 2).factorial : ℝ) * (∏ D ∈ A.erase B, wb D)) := by
              rw [hW_erase A B hB, hwbB, hfact B h2]
              ring
      _ ≤ (mb {i} * mb (B.erase i))
            * (((B.card : ℝ) - 1) * ((B.card - 2).factorial : ℝ) * (∏ D ∈ A.erase B, wb D)) :=
              mul_le_mul_of_nonneg_right (hkey B i hi) hK
      _ = ((B.card : ℝ) - 1) * W (splitBlk A B i) := by
              rw [hWsplit A B i hpart hB hi h2, hwbE B i hi]
              ring
  have hblock : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)),
      IsPartitionOf n t A → B ∈ A → 2 ≤ B.card →
      (m * rho / M) * W A ≤ ∑ i ∈ B, W (splitBlk A B i) := by
    intro A B hpart hB h2
    have hstep1 : (B.card : ℝ) * ((m * rho / M) * W A)
        ≤ ((B.card : ℝ) - 1) * ∑ i ∈ B, W (splitBlk A B i) := by
      have h := Finset.sum_le_sum (fun i hi => hWcmp A B i hpart hB hi h2)
      rw [Finset.sum_const, ← Finset.mul_sum] at h
      simpa [nsmul_eq_mul] using h
    have hS : 0 ≤ ∑ i ∈ B, W (splitBlk A B i) :=
      Finset.sum_nonneg (fun i _ => hWnn _)
    have hbpos : 0 < (B.card : ℝ) := by
      have hpos : 0 < B.card := by omega
      exact_mod_cast hpos
    have hstep2 : ((B.card : ℝ) - 1) * (∑ i ∈ B, W (splitBlk A B i))
        ≤ (B.card : ℝ) * (∑ i ∈ B, W (splitBlk A B i)) := by
      apply mul_le_mul_of_nonneg_right _ hS
      linarith
    have hfin : (B.card : ℝ) * ((m * rho / M) * W A)
        ≤ (B.card : ℝ) * (∑ i ∈ B, W (splitBlk A B i)) := le_trans hstep1 hstep2
    have hd : 0 ≤ (∑ i ∈ B, W (splitBlk A B i)) - ((m * rho / M) * W A) := by
      by_contra hneg
      have hneg' : (∑ i ∈ B, W (splitBlk A B i)) - ((m * rho / M) * W A) < 0 := not_le.mp hneg
      have hlt : (B.card : ℝ) * ((∑ i ∈ B, W (splitBlk A B i)) - ((m * rho / M) * W A)) < 0 := by
        nlinarith [hbpos, hneg']
      nlinarith [hfin, hlt]
    linarith
  have hbig : ∀ A : Finset (Finset (Fin n)), A ∈ tau n t → ∃ B ∈ A, 2 ≤ B.card := by
    intro A hA
    have hpart := hmem_tau hA
    have hAsum : ∑ B ∈ A, B.card = n := by
      have hcover : A.biUnion (fun B => B) = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro a
        obtain ⟨B, hB, ha⟩ := hpart.2.2.2 a
        exact Finset.mem_biUnion.2 ⟨B, hB, ha⟩
      have hpd : (A : Set (Finset (Fin n))).PairwiseDisjoint (fun B => B) :=
        fun B hB C hC hne => hpart.2.2.1 B hB C hC hne
      have h := Finset.card_biUnion hpd
      rw [hcover, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    by_contra hcon
    push_neg at hcon
    have hAll1 : ∀ B ∈ A, B.card = 1 := by
      intro B hB
      have h1 : 1 ≤ B.card := Finset.card_pos.2 (hpart.2.1 B hB)
      have h2 : B.card < 2 := hcon B hB
      omega
    have hsum1 : ∑ B ∈ A, B.card = A.card := by
      rw [Finset.sum_congr rfl (fun B hB => hAll1 B hB)]
      simp
    rw [hsum1, hcard_tau hA] at hAsum
    omega
  have hAstep : ∀ A : Finset (Finset (Fin n)), A ∈ tau n t →
      (m * rho / M) * W A
        ≤ ∑ B ∈ A.filter (fun B => 2 ≤ B.card), ∑ i ∈ B, W (splitBlk A B i) := by
    intro A hA
    have hpart := hmem_tau hA
    obtain ⟨B0, hB0, hB02⟩ := hbig A hA
    have hblk := hblock A B0 hpart hB0 hB02
    have hnonneg : ∀ B ∈ A.filter (fun B => 2 ≤ B.card), 0 ≤ ∑ i ∈ B, W (splitBlk A B i) :=
      fun B _ => Finset.sum_nonneg (fun i _ => hWnn _)
    have hmem : B0 ∈ A.filter (fun B => 2 ≤ B.card) := Finset.mem_filter.2 ⟨hB0, hB02⟩
    exact le_trans hblk (Finset.single_le_sum hnonneg hmem)
  have hLsum : (m * rho / M) * (∑ A ∈ tau n t, W A)
      ≤ ∑ A ∈ tau n t, ∑ B ∈ A.filter (fun B => 2 ≤ B.card), ∑ i ∈ B, W (splitBlk A B i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun A hA => hAstep A hA)
  have hsplit_mem : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)) (i : Fin n),
      IsPartitionOf n t A → B ∈ A → i ∈ B → 2 ≤ B.card →
      IsPartitionOf n (t + 1) (splitBlk A B i) := by
    intro A B i hpart hB hi h2
    have hEq : splitBlk A B i = insert {i} (insert (B.erase i) (A.erase B)) := by rw [hsplitBlk]
    rw [hEq]
    have hcardA : A.card = t := hpart.1
    have hcardB : (A.erase B).card = t - 1 := by
      rw [Finset.card_erase_of_mem hB, hcardA]
    have hBpos : 0 < (B.erase i).card := by
      rw [Finset.card_erase_of_mem hi]
      omega
    have hB'notin : B.erase i ∉ A.erase B := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hneB, hmemA⟩ := hmem
      have hdisj := hpart.2.2.1 (B.erase i) hmemA B hB hneB
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hBpos
      exact (Finset.disjoint_left.1 hdisj) hx (Finset.mem_erase.1 hx).2
    have hsing_ne : ({i} : Finset (Fin n)) ≠ B.erase i := by
      intro heq
      have hmem : i ∈ B.erase i := by rw [← heq]; exact Finset.mem_singleton_self i
      exact (Finset.mem_erase.1 hmem).1 rfl
    have hsing_notinA : ({i} : Finset (Fin n)) ∉ A.erase B := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hneB, hmemA⟩ := hmem
      have hdisj := hpart.2.2.1 ({i} : Finset (Fin n)) hmemA B hB hneB
      exact (Finset.disjoint_left.1 hdisj) (Finset.mem_singleton_self i) (by simpa using hi)
    have h1 : ({i} : Finset (Fin n)) ∉ insert (B.erase i) (A.erase B) := by
      rw [Finset.mem_insert]
      exact fun h => h.elim hsing_ne hsing_notinA
    have hcard : (insert {i} (insert (B.erase i) (A.erase B))).card = t + 1 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hB'notin, hcardB]
      omega
    have hsub : B.erase i ⊆ B := fun x hx => (Finset.mem_erase.1 hx).2
    have hdisjB : ∀ D ∈ A.erase B, Disjoint D B :=
      fun D hD => hpart.2.2.1 D (Finset.mem_erase.1 hD).2 B hB (Finset.mem_erase.1 hD).1
    refine ⟨hcard, ?_, ?_, ?_⟩
    · intro D hD
      rw [Finset.mem_insert, Finset.mem_insert] at hD
      rcases hD with rfl | rfl | hD
      · exact ⟨i, Finset.mem_singleton_self i⟩
      · exact Finset.card_pos.1 hBpos
      · exact hpart.2.1 D (Finset.mem_erase.1 hD).2
    · intro D hD E hE hne
      rw [Finset.mem_insert, Finset.mem_insert] at hD hE
      rcases hD with rfl | rfl | hD <;> rcases hE with rfl | rfl | hE
      · exact absurd rfl hne
      · rw [Finset.disjoint_left]
        intro x hx hx'
        have hxi : x = i := by simpa using hx
        exact (Finset.mem_erase.1 hx').1 hxi
      · rw [Finset.disjoint_left]
        intro x hx hx'
        have hxi : x = i := by simpa using hx
        exact (Finset.disjoint_left.1 (hdisjB E hE)) hx' (hxi ▸ hi)
      · rw [Finset.disjoint_left]
        intro x hx hx'
        have hxi : x = i := by simpa using hx'
        exact (Finset.mem_erase.1 hx).1 hxi
      · exact absurd rfl hne
      · rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.disjoint_left.1 (hdisjB E hE)) hx' (hsub hx)
      · rw [Finset.disjoint_left]
        intro x hx hx'
        have hxi : x = i := by simpa using hx'
        exact (Finset.disjoint_left.1 (hdisjB D hD)) hx (hxi ▸ hi)
      · rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.disjoint_left.1 (hdisjB D hD)) hx (hsub hx')
      · exact hpart.2.2.1 D (Finset.mem_erase.1 hD).2 E (Finset.mem_erase.1 hE).2 hne
    · intro a
      obtain ⟨D, hD, ha⟩ := hpart.2.2.2 a
      by_cases hDB : D = B
      · rw [hDB] at ha
        by_cases hai : a = i
        · exact ⟨{i}, Finset.mem_insert_self _ _, Finset.mem_singleton.2 hai⟩
        · exact ⟨B.erase i, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
            Finset.mem_erase.2 ⟨hai, ha⟩⟩
      · exact ⟨D, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hDB, hD⟩)), ha⟩
  have hsplitE : ∀ (A : Finset (Finset (Fin n))) (B : Finset (Fin n)) (i : Fin n),
      splitBlk A B i = insert {i} (insert (B.erase i) (A.erase B)) := by
    intro A B i
    rw [hsplitBlk]
  let inner : Finset (Finset (Fin n)) → Finset (Sigma (fun _ : Finset (Fin n) => Fin n)) :=
    fun A => (A.filter (fun B => 2 ≤ B.card)).sigma (fun B => B)
  let T : Finset (Sigma (fun _ : Finset (Finset (Fin n)) =>
      Sigma (fun _ : Finset (Fin n) => Fin n))) := (tau n t).sigma inner
  have hT : T = (tau n t).sigma inner := rfl
  have hinner : inner = fun A => (A.filter (fun B => 2 ≤ B.card)).sigma (fun B => B) := rfl
  have hTmem : ∀ p : Sigma (fun _ : Finset (Finset (Fin n)) => Sigma (fun _ : Finset (Fin n) => Fin n)),
      p ∈ T ↔ p.1 ∈ tau n t ∧ p.2.1 ∈ p.1 ∧ 2 ≤ p.2.1.card ∧ p.2.2 ∈ p.2.1 := by
    intro p
    have h1 : p ∈ T ↔ p.1 ∈ tau n t ∧ p.2 ∈ inner p.1 := by
      rw [hT]
      exact Finset.mem_sigma
    have h2 : (p.2 ∈ inner p.1) ↔ p.2.1 ∈ p.1.filter (fun B => 2 ≤ B.card) ∧ p.2.2 ∈ p.2.1 := by
      rw [hinner]
      exact Finset.mem_sigma
    rw [h1, h2, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩
    · intro h
      exact ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩
  have hmap : ∀ p ∈ T, splitBlk p.1 p.2.1 p.2.2 ∈ tau n (t + 1) := by
    intro p hp
    obtain ⟨hp1, hpB, hp2card, hpi⟩ := (hTmem p).1 hp
    have hI := hsplit_mem p.1 p.2.1 p.2.2 (hmem_tau hp1) hpB hpi hp2card
    simp only [tau, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hI⟩
  have hTeq : ∑ A ∈ tau n t, ∑ B ∈ A.filter (fun B => 2 ≤ B.card), ∑ i ∈ B, W (splitBlk A B i)
      = ∑ p ∈ T, W (splitBlk p.1 p.2.1 p.2.2) := by
    rw [hT, hinner]
    simp only [Finset.sum_sigma]
  have hfiber : ∀ A' ∈ tau n (t + 1),
      (T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card ≤ t * (t + 1) := by
    intro A' hA'
    have hexp : T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')
        = T.filter (fun p => insert ({p.2.2} : Finset (Fin n))
            (insert (p.2.1.erase p.2.2) (p.1.erase p.2.1)) = A') := by
      apply Finset.filter_congr
      intro p _
      rw [hsplitE p.1 p.2.1 p.2.2]
    rw [hexp]
    have hsub : T ⊆ (tau n t).sigma (fun A => A.sigma (fun B => B)) := by
      intro p hp
      obtain ⟨hp1, hpB, hp2card, hpi⟩ := (hTmem p).1 hp
      simp only [Finset.mem_sigma]
      exact ⟨hp1, hpB, hpi⟩
    have hcard_le : (T.filter (fun p => insert ({p.2.2} : Finset (Fin n))
          (insert (p.2.1.erase p.2.2) (p.1.erase p.2.1)) = A')).card
        ≤ (((tau n t).sigma (fun A => A.sigma (fun B => B))).filter
          (fun p => insert ({p.2.2} : Finset (Fin n))
            (insert (p.2.1.erase p.2.2) (p.1.erase p.2.1)) = A')).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hsub hp.1, hp.2⟩
    have hchild := statopia_math_node_4081398995_d2b977a1 n t A' (hcard_tau hA')
    omega
  have hfibsum : ∑ p ∈ T, W (splitBlk p.1 p.2.1 p.2.2)
      = ∑ A' ∈ tau n (t + 1), (T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card * W A' := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro A' hA'
    have hpt : ∀ p ∈ T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A'),
        W (splitBlk p.1 p.2.1 p.2.2) = W A' := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hp.2]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
  have hSbound : ∑ p ∈ T, W (splitBlk p.1 p.2.1 p.2.2)
      ≤ ((t : ℝ) * ((t : ℝ) + 1)) * (∑ A' ∈ tau n (t + 1), W A') := by
    rw [hfibsum]
    have h1 : ∀ A' ∈ tau n (t + 1),
        (T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card * W A'
          ≤ ((t : ℝ) * ((t : ℝ) + 1)) * W A' := by
      intro A' hA'
      have hc : ((T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card : ℝ)
          ≤ (t : ℝ) * ((t : ℝ) + 1) := by
        have hb := hfiber A' hA'
        have hb' : ((T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card : ℝ)
            ≤ ((t * (t + 1) : ℕ) : ℝ) := by exact_mod_cast hb
        have hcast : ((t * (t + 1) : ℕ) : ℝ) = (t : ℝ) * ((t : ℝ) + 1) := by
          push_cast
          ring
        linarith
      exact mul_le_mul_of_nonneg_right hc (hWnn A')
    calc ∑ A' ∈ tau n (t + 1), (T.filter (fun p => splitBlk p.1 p.2.1 p.2.2 = A')).card * W A'
        ≤ ∑ A' ∈ tau n (t + 1), ((t : ℝ) * ((t : ℝ) + 1)) * W A' := Finset.sum_le_sum h1
      _ = ((t : ℝ) * ((t : ℝ) + 1)) * (∑ A' ∈ tau n (t + 1), W A') := by
            rw [Finset.mul_sum]
  refine le_trans hLsum ?_
  rw [hTeq]
  exact hSbound
  /- @proof-region region.target-node.session.42e5bc16b430d4c5 end -/

end Statlib.Imported
end DPCompletedProof
