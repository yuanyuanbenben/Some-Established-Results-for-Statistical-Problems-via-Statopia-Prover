import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base

open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_2445022674_8afd0c25 : ∀ (q : ℕ) (a : Fin q → ℝ) (b : ℕ → ℝ)
    (hbmono : StrictMonoOn b (Set.Icc 0 q))
    (hbstep : ∀ k : Fin q, b ((k : ℕ) + 1) - b (k : ℕ) = a k)
    (I J : Finset (Fin q)) (C : Finset ℝ)
    (hC3 : ∀ c ∈ C, ∃ k ∈ I ∪ J, b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1)),
    ∀ k : Fin q,
      Multiset.ofList (List.zipWith (fun p r => r - p)
        ((b (k : ℕ) :: ((C ∪ (Finset.univ.filter (fun j : Fin q => j ∉ I ∪ J)).image
          (fun j : Fin q => (b (j : ℕ) + b ((j : ℕ) + 1)) / 2)).filter
          (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))
          ++ [b ((k : ℕ) + 1)])
        ((b (k : ℕ) :: ((C ∪ (Finset.univ.filter (fun j : Fin q => j ∉ I ∪ J)).image
          (fun j : Fin q => (b (j : ℕ) + b ((j : ℕ) + 1)) / 2)).filter
          (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1))).sort (· ≤ ·))
          ++ [b ((k : ℕ) + 1)]).tail)
      = (if k ∈ I ∪ J
         then Multiset.ofList (List.zipWith (fun p r => r - p)
           ((b (k : ℕ) :: (C.filter (fun c => b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1))).sort (· ≤ ·))
             ++ [b ((k : ℕ) + 1)])
           ((b (k : ℕ) :: (C.filter (fun c => b (k : ℕ) < c ∧ c < b ((k : ℕ) + 1))).sort (· ≤ ·))
             ++ [b ((k : ℕ) + 1)]).tail)
         else ({a k / 2, a k / 2} : Multiset ℝ)) := by
  /- @proof-region region.target-node.session.f0e4e27b4bd1ff22 begin -/
  intro q a b hbmono hbstep I J C hC3 k
  set m : Fin q → ℝ := fun j => (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 with hm
  set M : Finset ℝ := (Finset.univ.filter (fun j : Fin q => j ∉ I ∪ J)).image m with hM
  set P : Finset ℝ := (C ∪ M).filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1)) with hP
  set Pc : Finset ℝ := C.filter (fun x => b (k : ℕ) < x ∧ x < b ((k : ℕ) + 1)) with hPc
  have hmj : ∀ j : Fin q, m j = (b (j : ℕ) + b ((j : ℕ) + 1)) / 2 := fun j => by simp only [hm]
  have hblt : ∀ i j : ℕ, i < j → j ≤ q → b i < b j := by
    intro i j hij hjq
    exact hbmono ⟨by omega, by omega⟩ ⟨by omega, hjq⟩ hij
  have hble : ∀ i j : ℕ, i ≤ j → j ≤ q → b i ≤ b j := by
    intro i j hij hjq
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact le_of_lt (hblt i j h hjq)
  have hlt : ∀ j : Fin q, b (j : ℕ) < b ((j : ℕ) + 1) := by
    intro j
    exact hblt (j : ℕ) ((j : ℕ) + 1) (by omega) (by have := j.isLt; omega)
  have hmlo : ∀ j : Fin q, b (j : ℕ) < m j := by
    intro j; linarith [hmj j, hlt j]
  have hmhi : ∀ j : Fin q, m j < b ((j : ℕ) + 1) := by
    intro j; linarith [hmj j, hlt j]
  have huniq : ∀ i j : Fin q, b (i : ℕ) < m j → m j < b ((i : ℕ) + 1) → i = j := by
    intro i j h1 h2
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · have hle : b ((i : ℕ) + 1) ≤ b (j : ℕ) := hble ((i : ℕ) + 1) (j : ℕ) (by omega) (by have := j.isLt; omega)
      linarith [hmlo j]
    · exact Fin.ext h
    · have hle : b ((j : ℕ) + 1) ≤ b (i : ℕ) := hble ((j : ℕ) + 1) (i : ℕ) (by omega) (by have := i.isLt; omega)
      linarith [hmhi j]
  have hCpin : ∀ c ∈ C, b (k : ℕ) < c → c < b ((k : ℕ) + 1) → k ∈ I ∪ J := by
    intro c hc h1 h2
    rcases hC3 c hc with ⟨j, hjmem, hj1, hj2⟩
    rcases lt_trichotomy (k : ℕ) (j : ℕ) with h | h | h
    · have hle : b ((k : ℕ) + 1) ≤ b (j : ℕ) := hble ((k : ℕ) + 1) (j : ℕ) (by omega) (by have := j.isLt; omega)
      linarith
    · have hkj : k = j := Fin.ext h
      rw [← hkj] at hjmem
      exact hjmem
    · have hle : b ((j : ℕ) + 1) ≤ b (k : ℕ) := hble ((j : ℕ) + 1) (k : ℕ) (by omega) (by have := k.isLt; omega)
      linarith
  by_cases hk : k ∈ I ∪ J
  · have hPeqc : P = Pc := by
      apply Finset.ext
      intro x
      rw [hP, hPc]
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hxCM, hx1, hx2⟩
        rcases hxCM with hxC | hxM
        · exact ⟨hxC, hx1, hx2⟩
        · exfalso
          rw [hM] at hxM
          rcases Finset.mem_image.mp hxM with ⟨j, hjf, hjm⟩
          rw [Finset.mem_filter] at hjf
          obtain ⟨-, hjn⟩ := hjf
          have hx1' : b (k : ℕ) < m j := by rw [hjm]; exact hx1
          have hx2' : m j < b ((k : ℕ) + 1) := by rw [hjm]; exact hx2
          have hkj : k = j := huniq k j hx1' hx2'
          exact hjn (hkj ▸ hk)
      · rintro ⟨hxC, hx1, hx2⟩
        exact ⟨Or.inl hxC, hx1, hx2⟩
    rw [hPeqc, if_pos hk]
  · have hPeq : P = {m k} := by
      apply Finset.ext
      intro x
      rw [hP]
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hxCM, hx1, hx2⟩
        rcases hxCM with hxC | hxM
        · exact absurd (hCpin x hxC hx1 hx2) hk
        · rw [hM] at hxM
          rcases Finset.mem_image.mp hxM with ⟨j, hjf, hjm⟩
          rw [Finset.mem_filter] at hjf
          obtain ⟨-, hjn⟩ := hjf
          have hx1' : b (k : ℕ) < m j := by rw [hjm]; exact hx1
          have hx2' : m j < b ((k : ℕ) + 1) := by rw [hjm]; exact hx2
          have hkj : k = j := huniq k j hx1' hx2'
          rw [← hjm, hkj]
      · rintro rfl
        exact ⟨Or.inr (by rw [hM]; exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩), hmlo k, hmhi k⟩
    have hs : ({m k} : Finset ℝ).sort (· ≤ ·) = [m k] := by
      have h := (List.toFinset_sort (· ≤ ·) (l := [m k]) (by simp)).mpr (by simp)
      simpa using h
    have e1 : m k - b (k : ℕ) = a k / 2 := by linarith [hmj k, hbstep k]
    have e2 : b ((k : ℕ) + 1) - m k = a k / 2 := by linarith [hmj k, hbstep k]
    rw [hPeq, if_neg hk, hs]
    have hzip : List.zipWith (fun p r => r - p) ((b (k : ℕ) :: [m k]) ++ [b ((k : ℕ) + 1)]) (((b (k : ℕ) :: [m k]) ++ [b ((k : ℕ) + 1)]).tail) = [m k - b (k : ℕ), b ((k : ℕ) + 1) - m k] := rfl
    rw [hzip, e1, e2]
    rfl
  /- @proof-region region.target-node.session.f0e4e27b4bd1ff22 end -/

end LiuBangXiangYu
