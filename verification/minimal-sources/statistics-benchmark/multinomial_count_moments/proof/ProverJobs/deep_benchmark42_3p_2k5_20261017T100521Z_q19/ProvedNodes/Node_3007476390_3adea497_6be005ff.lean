import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.Base
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q19.ProvedNodes.Node_887293322_4a71d68e_98cac379

open Msc62GroundTruth

namespace Msc62GroundTruth

set_option autoImplicit false in
theorem statopia_math_node_3007476390_3adea497 : ∀ (n k : ℕ) (p : Fin k → ℝ) (hp_sum : (∑ c : Fin k, p c) = 1)
    (s t : Fin n) (hst : s ≠ t) (a b : Fin k),
    (∑ x : Fin n → Fin k,
      (∏ u : Fin n, p (x u)) *
        (if x s = a then (1 : ℝ) else 0) *
        (if x t = b then (1 : ℝ) else 0))
      = p a * p b := by
  /- @proof-region region.target-node.session.a3d2e49831c4a064 begin -/
  intro n k p hp_sum s t hst a b
  classical
  have hts : t ≠ s := fun h => hst h.symm
  set f : Fin n → Fin k → ℝ := (fun u c =>
    if u = s then (if c = a then p c else 0)
    else if u = t then (if c = b then p c else 0)
    else p c) with hf
  have hfval : ∀ (u : Fin n) (c : Fin k), f u c =
      (if u = s then (if c = a then p c else 0)
        else if u = t then (if c = b then p c else 0) else p c) :=
    fun u c => by rw [hf]
  have hsingle_eq : ∀ (x : ℝ) (i : Fin n), (∏ u : Fin n, (if i = u then x else 1)) = x := by
    intro x i
    have h := Finset.prod_ite_eq (s := (Finset.univ : Finset (Fin n))) (a := i)
      (b := fun _ : Fin n => x)
    simpa using h
  have hsingle : ∀ (x : ℝ) (i : Fin n), (∏ u : Fin n, (if u = i then x else 1)) = x := by
    intro x i
    have h2 : (∏ u : Fin n, (if u = i then x else 1))
        = ∏ u : Fin n, (if i = u then x else 1) :=
      Finset.prod_congr rfl (fun u _ => by
        by_cases hu : u = i
        · simp [hu]
        · have hu' : ¬(i = u) := fun hh => hu hh.symm
          simp [hu, hu'])
    rw [h2, hsingle_eq x i]
  have hSs : (∑ c : Fin k, f s c) = p a := by
    have h1 : (∑ c : Fin k, f s c) = ∑ c : Fin k, (if c = a then p c else 0) :=
      Finset.sum_congr rfl (fun c _ => by simp [hfval])
    have h2 : (∑ c : Fin k, (if c = a then p c else 0))
        = ∑ c : Fin k, (if a = c then p c else 0) :=
      Finset.sum_congr rfl (fun c _ => by
        by_cases hc : c = a
        · simp [hc]
        · have hc' : ¬(a = c) := fun hh => hc hh.symm
          simp [hc, hc'])
    have h3 : (∑ c : Fin k, (if a = c then p c else 0)) = p a := by
      have h := Finset.sum_ite_eq (s := (Finset.univ : Finset (Fin k))) (a := a) (b := p)
      simpa using h
    rw [h1, h2, h3]
  have hSt : (∑ c : Fin k, f t c) = p b := by
    have h1 : (∑ c : Fin k, f t c) = ∑ c : Fin k, (if c = b then p c else 0) :=
      Finset.sum_congr rfl (fun c _ => by simp [hfval, hts])
    have h2 : (∑ c : Fin k, (if c = b then p c else 0))
        = ∑ c : Fin k, (if b = c then p c else 0) :=
      Finset.sum_congr rfl (fun c _ => by
        by_cases hc : c = b
        · simp [hc]
        · have hc' : ¬(b = c) := fun hh => hc hh.symm
          simp [hc, hc'])
    have h3 : (∑ c : Fin k, (if b = c then p c else 0)) = p b := by
      have h := Finset.sum_ite_eq (s := (Finset.univ : Finset (Fin k))) (a := b) (b := p)
      simpa using h
    rw [h1, h2, h3]
  have hS1 : ∀ u : Fin n, u ≠ s → u ≠ t → (∑ c : Fin k, f u c) = 1 := by
    intro u hus hut
    have hpt : ∀ c : Fin k, f u c = p c := by
      intro c
      simp [hfval, hus, hut]
    calc (∑ c : Fin k, f u c) = ∑ c : Fin k, p c := Finset.sum_congr rfl (fun c _ => hpt c)
      _ = 1 := hp_sum
  have hSval : ∀ u : Fin n,
      (∑ c : Fin k, f u c) = if u = s then p a else if u = t then p b else 1 := by
    intro u
    by_cases hus : u = s
    · subst hus
      rw [if_pos rfl]
      exact hSs
    · rw [if_neg hus]
      by_cases hut : u = t
      · subst hut
        rw [if_pos rfl]
        exact hSt
      · rw [if_neg hut]
        exact hS1 u hus hut
  have hsplit : ∀ u : Fin n,
      (if u = s then p a else if u = t then p b else 1)
        = (if u = s then p a else 1) * (if u = t then p b else 1) := by
    intro u
    by_cases hus : u = s
    · subst hus
      simp [hst]
    · by_cases hut : u = t
      · subst hut
        simp [hts]
      · simp [hus, hut]
  have hprod : (∏ u : Fin n, (∑ c : Fin k, f u c)) = p a * p b := by
    calc (∏ u : Fin n, (∑ c : Fin k, f u c))
        = ∏ u : Fin n, (if u = s then p a else if u = t then p b else 1) :=
          Finset.prod_congr rfl (fun u _ => hSval u)
      _ = ∏ u : Fin n, ((if u = s then p a else 1) * (if u = t then p b else 1)) :=
          Finset.prod_congr rfl (fun u _ => hsplit u)
      _ = (∏ u : Fin n, (if u = s then p a else 1)) * (∏ u : Fin n, (if u = t then p b else 1)) :=
          Finset.prod_mul_distrib
      _ = p a * p b := by rw [hsingle (p a) s, hsingle (p b) t]
  have hpoint : ∀ x : Fin n → Fin k,
      (∏ u : Fin n, f u (x u)) =
        (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) := by
    intro x
    have hpt : ∀ u : Fin n, f u (x u) =
        p (x u) * (if u = s then (if x s = a then (1 : ℝ) else 0) else 1)
          * (if u = t then (if x t = b then (1 : ℝ) else 0) else 1) := by
      intro u
      by_cases hus : u = s
      · rw [hus]
        simp [hfval, hst]
      · by_cases hut : u = t
        · rw [hut]
          simp [hfval, hts]
        · simp [hfval, hus, hut]
    calc (∏ u : Fin n, f u (x u))
        = ∏ u : Fin n, (p (x u) * (if u = s then (if x s = a then (1 : ℝ) else 0) else 1)
            * (if u = t then (if x t = b then (1 : ℝ) else 0) else 1)) :=
          Finset.prod_congr rfl (fun u _ => hpt u)
      _ = (∏ u : Fin n, (p (x u) * (if u = s then (if x s = a then (1 : ℝ) else 0) else 1)))
            * (∏ u : Fin n, (if u = t then (if x t = b then (1 : ℝ) else 0) else 1)) :=
          Finset.prod_mul_distrib
      _ = ((∏ u : Fin n, p (x u))
            * (∏ u : Fin n, (if u = s then (if x s = a then (1 : ℝ) else 0) else 1)))
            * (∏ u : Fin n, (if u = t then (if x t = b then (1 : ℝ) else 0) else 1)) := by
          rw [Finset.prod_mul_distrib]
      _ = (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) := by
          rw [hsingle (if x s = a then (1 : ℝ) else 0) s,
            hsingle (if x t = b then (1 : ℝ) else 0) t]
  have hsum_eq : (∑ x : Fin n → Fin k, ∏ u : Fin n, f u (x u))
      = ∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun x _ => hpoint x)
  calc (∑ x : Fin n → Fin k, (∏ u : Fin n, p (x u)) * (if x s = a then (1 : ℝ) else 0) * (if x t = b then (1 : ℝ) else 0))
      = ∑ x : Fin n → Fin k, ∏ u : Fin n, f u (x u) := hsum_eq.symm
    _ = ∏ u : Fin n, ∑ c : Fin k, f u c := statopia_math_node_887293322_4a71d68e n k f
    _ = p a * p b := hprod
  /- @proof-region region.target-node.session.a3d2e49831c4a064 end -/

end Msc62GroundTruth
