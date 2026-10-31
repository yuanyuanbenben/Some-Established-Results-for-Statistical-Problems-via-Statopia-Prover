import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_4081398995_d2b977a1 : ∀ (n t : ℕ) (A' : Finset (Finset (Fin n)))
    (hA' : A'.card = t + 1),
      (((tau n t).sigma
          (fun A : Finset (Finset (Fin n)) =>
            A.sigma (fun B : Finset (Fin n) => (B : Finset (Fin n))))).filter
        (fun p =>
          insert ({p.2.2} : Finset (Fin n))
            (insert (p.2.1.erase p.2.2) (p.1.erase p.2.1)) = A')).card ≤ t * (t + 1) := by
  /- @proof-region region.target-node.session.d4aca6aeb2029013 begin -/
  intro n t A' hA'
  classical
  set S := ((tau n t).sigma
      (fun A : Finset (Finset (Fin n)) =>
        A.sigma (fun B : Finset (Fin n) => (B : Finset (Fin n))))).filter
      (fun p =>
        insert ({p.2.2} : Finset (Fin n))
          (insert (p.2.1.erase p.2.2) (p.1.erase p.2.1)) = A') with hS
  let Q : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ({i} : Finset (Fin n)) ∈ A')
  have extract : ∀ r ∈ S,
      r.fst ∈ tau n t ∧ r.snd.fst ∈ r.fst ∧ r.snd.snd ∈ r.snd.fst ∧
        insert ({r.snd.snd} : Finset (Fin n))
          (insert (r.snd.fst.erase r.snd.snd) (r.fst.erase r.snd.fst)) = A' := by
    intro r hr
    rw [hS, Finset.mem_filter] at hr
    obtain ⟨hrsig, hrf⟩ := hr
    obtain ⟨hrAtau, hrsig2⟩ := Finset.mem_sigma.mp hrsig
    obtain ⟨hrB, hri⟩ := Finset.mem_sigma.mp hrsig2
    exact ⟨hrAtau, hrB, hri, hrf⟩
  have key : ∀ r ∈ S,
      ({r.snd.snd} : Finset (Fin n)) ∉ insert (r.snd.fst.erase r.snd.snd) (r.fst.erase r.snd.fst) ∧
      (r.snd.fst.erase r.snd.snd) ∉ r.fst.erase r.snd.fst := by
    intro r hr
    obtain ⟨hrAtau, hrB, hri, hrf⟩ := extract r hr
    have hrpart : IsPartitionOf n t r.fst := by simpa [tau] using hrAtau
    obtain ⟨hrcard, hrne, hrdisj, hrcover⟩ := hrpart
    have hsingle_notin_D : ({r.snd.snd} : Finset (Fin n)) ∉ r.fst.erase r.snd.fst := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hne, hsingB⟩ := hmem
      exact (Finset.disjoint_left.mp
        (hrdisj {r.snd.snd} hsingB r.snd.fst hrB hne) (Finset.mem_singleton_self _)) hri
    have hC_notin_D : (r.snd.fst.erase r.snd.snd) ∉ r.fst.erase r.snd.fst := by
      intro hmem
      rw [Finset.mem_erase] at hmem
      obtain ⟨hne, hCA⟩ := hmem
      have hdisjCB : Disjoint (r.snd.fst.erase r.snd.snd) r.snd.fst := hrdisj _ hCA r.snd.fst hrB hne
      obtain ⟨c, hc⟩ := hrne _ hCA
      exact (Finset.disjoint_left.mp hdisjCB hc) (Finset.mem_of_mem_erase hc)
    refine ⟨?_, hC_notin_D⟩
    rw [Finset.mem_insert]
    rintro (heq | hin)
    · have hmem : r.snd.snd ∈ r.snd.fst.erase r.snd.snd := by
        rw [← heq]; exact Finset.mem_singleton_self _
      rw [Finset.mem_erase] at hmem
      exact hmem.1 rfl
    · exact hsingle_notin_D hin
  have hbound : S.card ≤ (Q.sigma (fun i : Fin n => A'.erase ({i} : Finset (Fin n)))).card := by
    refine Finset.card_le_card_of_injOn
      (fun p => (⟨p.snd.snd, p.snd.fst.erase p.snd.snd⟩)) ?_ ?_
    · intro p hp
      obtain ⟨hAtau, hB, hi, hf⟩ := extract p hp
      have hiQ : p.snd.snd ∈ Q := by
        dsimp only [Q]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [← hf]; exact Finset.mem_insert_self _ _⟩
      have hCerase : p.snd.fst.erase p.snd.snd ∈ A'.erase ({p.snd.snd} : Finset (Fin n)) := by
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro heq
          have hmem : p.snd.snd ∈ p.snd.fst.erase p.snd.snd := by
            rw [heq]; exact Finset.mem_singleton_self _
          rw [Finset.mem_erase] at hmem
          exact hmem.1 rfl
        · rw [← hf]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      rw [Finset.mem_coe, Finset.mem_sigma]
      exact ⟨hiQ, hCerase⟩
    · intro p hp q hq hfeq
      have hpS : p ∈ S := hp
      have hqS : q ∈ S := hq
      have hi_eq : p.snd.snd = q.snd.snd := congrArg (fun r => r.fst) hfeq
      have hC_eq : p.snd.fst.erase p.snd.snd = q.snd.fst.erase q.snd.snd :=
        congrArg (fun r => r.snd) hfeq
      obtain ⟨hp1, hp2⟩ := key p hpS
      obtain ⟨hq1, hq2⟩ := key q hqS
      obtain ⟨_, hpB, hpi, hpf⟩ := extract p hpS
      obtain ⟨_, hqB, hqi, hqf⟩ := extract q hqS
      have hB_eq : p.snd.fst = q.snd.fst := by
        rw [← Finset.insert_erase hpi, ← Finset.insert_erase hqi, hC_eq, hi_eq]
      have hDp : (A'.erase ({p.snd.snd} : Finset (Fin n))).erase
          (p.snd.fst.erase p.snd.snd) = p.fst.erase p.snd.fst := by
        rw [← hpf, Finset.erase_insert hp1, Finset.erase_insert hp2]
      have hDq : (A'.erase ({q.snd.snd} : Finset (Fin n))).erase
          (q.snd.fst.erase q.snd.snd) = q.fst.erase q.snd.fst := by
        rw [← hqf, Finset.erase_insert hq1, Finset.erase_insert hq2]
      have hD_eq : p.fst.erase p.snd.fst = q.fst.erase q.snd.fst := by
        rw [← hDp, ← hDq, hC_eq, hi_eq]
      have hpq : p.fst = q.fst := by
        rw [← Finset.insert_erase hpB, ← Finset.insert_erase hqB, hD_eq, hB_eq]
      have hinner : p.snd = q.snd := Sigma.ext hB_eq (heq_of_eq hi_eq)
      exact Sigma.ext hpq (heq_of_eq hinner)
  have hTgcard : (Q.sigma (fun i : Fin n => A'.erase ({i} : Finset (Fin n)))).card = Q.card * t := by
    rw [Finset.card_sigma]
    have hterm : ∀ i ∈ Q, (A'.erase ({i} : Finset (Fin n))).card = t := by
      intro i hi
      have hiQ : ({i} : Finset (Fin n)) ∈ A' := by
        dsimp only [Q] at hi
        rw [Finset.mem_filter] at hi
        exact hi.2
      rw [Finset.card_erase_of_mem hiQ, hA']
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hQcard : Q.card ≤ t + 1 := by
    have hle : Q.card ≤ A'.card := by
      apply Finset.card_le_card_of_injOn (f := fun i : Fin n => ({i} : Finset (Fin n)))
      · intro i hi
        have hiQ : i ∈ Q := hi
        dsimp only [Q] at hiQ
        rw [Finset.mem_filter] at hiQ
        exact hiQ.2
      · intro i _ j _ hij
        simpa using hij
    rwa [hA'] at hle
  calc S.card ≤ (Q.sigma (fun i : Fin n => A'.erase ({i} : Finset (Fin n)))).card := hbound
    _ = Q.card * t := hTgcard
    _ ≤ (t + 1) * t := Nat.mul_le_mul_right t hQcard
    _ = t * (t + 1) := by rw [Nat.mul_comm]
  /- @proof-region region.target-node.session.d4aca6aeb2029013 end -/

end Statlib.Imported
