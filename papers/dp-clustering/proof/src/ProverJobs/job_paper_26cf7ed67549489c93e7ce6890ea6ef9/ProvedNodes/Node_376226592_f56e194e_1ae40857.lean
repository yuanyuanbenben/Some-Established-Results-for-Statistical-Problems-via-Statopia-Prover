import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Vocabulary
import ProverJobs.job_paper_26cf7ed67549489c93e7ce6890ea6ef9.Base

open scoped BigOperators
open Statlib.Imported

open scoped BigOperators
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_376226592_f56e194e : ∀ (p : ℝ) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : k + 1 ≤ n),
    Finset.sum (Fs (k + 1) n)
        (fun a => ((n : ℝ) / ∏ i : Fin (k + 1), (((a i : ℕ) : ℝ) + 1)) ^ p)
      = Finset.sum (Finset.Icc 1 (n - k))
          (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p *
            Finset.sum (Fs k (n - b))
              (fun a => (((n - b : ℕ) : ℝ) / ∏ i : Fin k, (((a i : ℕ) : ℝ) + 1)) ^ p)) ∧
      (∀ b ∈ Finset.Icc 1 (n - k), 0 < ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p) := by
  /- @proof-region region.target-node.session.fc09eeb2c2d09536 begin -/
  intro p k hk n hn
  refine ⟨?_, ?_⟩
  · have hprod : ∀ a : Fin (k + 1) → Fin n,
        (∏ i : Fin (k + 1), (((a i : ℕ) : ℝ) + 1))
          = (∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1)) * (((a (Fin.last k) : ℕ) : ℝ) + 1) :=
      fun a => Fin.prod_univ_castSucc _
    have hsum : ∀ a : Fin (k + 1) → Fin n,
        (∑ i : Fin (k + 1), ((a i : ℕ) + 1))
          = (∑ i : Fin k, ((a (Fin.castSucc i) : ℕ) + 1)) + ((a (Fin.last k) : ℕ) + 1) :=
      fun a => Fin.sum_univ_castSucc _
    have hmem : ∀ (a : Fin (k + 1) → Fin n), a ∈ Fs (k + 1) n →
        ∑ i : Fin (k + 1), ((a i : ℕ) + 1) = n := by
      intro a ha
      simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ha
    have hS_ge_k : ∀ (a : Fin (k + 1) → Fin n),
        k ≤ ∑ i : Fin k, ((a (Fin.castSucc i) : ℕ) + 1) := by
      intro a
      have hk1 : (∑ i : Fin k, (1 : ℕ)) = k := by simp
      have hle : (∑ i : Fin k, (1 : ℕ)) ≤ ∑ i : Fin k, ((a (Fin.castSucc i) : ℕ) + 1) :=
        Finset.sum_le_sum (fun i _ => by omega)
      rw [hk1] at hle
      exact hle
    have hS_eq_gen : ∀ (a : Fin (k + 1) → Fin n), a ∈ Fs (k + 1) n →
        n - ((a (Fin.last k) : ℕ) + 1) = ∑ i : Fin k, ((a (Fin.castSucc i) : ℕ) + 1) := by
      intro a ha
      have hsplit : (∑ i : Fin k, ((a (Fin.castSucc i) : ℕ) + 1)) + ((a (Fin.last k) : ℕ) + 1) = n := by
        rw [← hsum a]; exact hmem a ha
      omega
    let Fs' : ℕ → Finset (Fin k → Fin n) :=
      fun b => Finset.univ.filter (fun g => ∑ i : Fin k, ((g i : ℕ) + 1) = n - b)
    let T : Finset ((b : ℕ) × (Fin k → Fin n)) :=
      (Finset.Icc 1 (n - k)).sigma Fs'
    let Wt : ℕ → ℝ := fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p
    let K : ℕ → (Fin k → Fin n) → ℝ :=
      fun b g => (((n - b : ℕ) : ℝ) / ∏ i : Fin k, (((g i : ℕ) : ℝ) + 1)) ^ p
    let G : ((b : ℕ) × (Fin k → Fin n)) → ℝ := fun x => Wt x.1 * K x.1 x.2
    have hFs'_mem : ∀ (b : ℕ) (g : Fin k → Fin n),
        g ∈ Fs' b ↔ ∑ i : Fin k, ((g i : ℕ) + 1) = n - b := by
      intro b g
      simp only [Fs', Finset.mem_filter, Finset.mem_univ, true_and]
    have hT1 : T.sum G = Finset.sum (Finset.Icc 1 (n - k))
        (fun b => Wt b * Finset.sum (Fs' b) (K b)) := by
      dsimp only [T, G]
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mul_sum]
    have fiber_eq : ∀ b : ℕ, Finset.sum (Fs' b) (K b)
        = Finset.sum (Fs k (n - b)) (fun a => (((n - b : ℕ) : ℝ) / ∏ i : Fin k, (((a i : ℕ) : ℝ) + 1)) ^ p) := by
      intro b
      refine Finset.sum_bij'
        (fun g hg => fun i => ⟨(g i : ℕ), ?_⟩)
        (fun a ha => fun i => ⟨(a i : ℕ), ?_⟩)
        ?_ ?_ ?_ ?_ ?_
      · have hg' := (hFs'_mem b g).mp hg
        have hle : (g i : ℕ) + 1 ≤ n - b := by
          rw [← hg']
          exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (g j : ℕ) + 1) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · exact lt_of_lt_of_le (a i).isLt (Nat.sub_le n b)
      · intro g hg
        have hg' := (hFs'_mem b g).mp hg
        simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using hg'
      · intro a ha
        rw [hFs'_mem]
        simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simpa using ha
      · intro g hg
        funext i
        exact Fin.ext rfl
      · intro a ha
        funext i
        exact Fin.ext rfl
      · intro g hg
        simp only [K, Fin.val_mk]
    have hT2 : Finset.sum (Finset.Icc 1 (n - k)) (fun b => Wt b * Finset.sum (Fs' b) (K b))
        = Finset.sum (Finset.Icc 1 (n - k))
          (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p *
            Finset.sum (Fs k (n - b))
              (fun a => (((n - b : ℕ) : ℝ) / ∏ i : Fin k, (((a i : ℕ) : ℝ) + 1)) ^ p)) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [fiber_eq b]
    have hT : T.sum G = Finset.sum (Finset.Icc 1 (n - k))
          (fun b => ((n : ℝ) / (((n - b : ℕ) : ℝ) * (b : ℝ))) ^ p *
            Finset.sum (Fs k (n - b))
              (fun a => (((n - b : ℕ) : ℝ) / ∏ i : Fin k, (((a i : ℕ) : ℝ) + 1)) ^ p)) :=
      hT1.trans hT2
    have hbij : Finset.sum (Fs (k + 1) n)
        (fun a => ((n : ℝ) / ∏ i : Fin (k + 1), (((a i : ℕ) : ℝ) + 1)) ^ p) = T.sum G := by
      let fwd : ∀ (a : Fin (k + 1) → Fin n), a ∈ Fs (k + 1) n → ((b : ℕ) × (Fin k → Fin n)) :=
        fun a ha => ⟨(a (Fin.last k) : ℕ) + 1, fun i => a (Fin.castSucc i)⟩
      let jfn : ∀ (x : (b : ℕ) × (Fin k → Fin n)), x ∈ T → (Fin (k + 1) → Fin n) :=
        fun x hx => Fin.snoc x.2 ⟨x.1 - 1, by
            have hx' := Finset.mem_sigma.mp hx
            have hxI := Finset.mem_Icc.mp hx'.1
            omega⟩
      refine Finset.sum_bij' fwd jfn ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · dsimp only [fwd]
          rw [Finset.mem_Icc]
          refine ⟨by omega, ?_⟩
          have hSe := hS_eq_gen a ha
          have hSk := hS_ge_k a
          have hbn : (a (Fin.last k) : ℕ) + 1 ≤ n := by have := (a (Fin.last k)).isLt; omega
          omega
        · dsimp only [fwd]
          rw [hFs'_mem]
          exact (hS_eq_gen a ha).symm
      · intro x hx
        have hx' := Finset.mem_sigma.mp hx
        have hxg : ∑ i : Fin k, ((x.2 i : ℕ) + 1) = n - x.1 := (hFs'_mem x.1 x.2).mp hx'.2
        have hxI := Finset.mem_Icc.mp hx'.1
        obtain ⟨hx1, hxle⟩ := hxI
        simp only [Fs, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hsum (jfn x hx)]
        simp only [jfn, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_mk]
        rw [hxg]
        omega
      · intro a ha
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp only [jfn, fwd, Fin.snoc_last, Fin.val_mk]
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        · intro i
          simp only [jfn, fwd, Fin.snoc_castSucc, Fin.val_mk]
      · intro x hx
        obtain ⟨b, g⟩ := x
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hx).1).1
        refine Sigma.ext ?_ ?_
        · dsimp only [fwd]
          simp only [jfn, Fin.snoc_last, Fin.val_mk]
          omega
        · apply heq_of_eq
          funext i
          dsimp only [fwd]
          simp only [jfn, Fin.snoc_castSucc]
      · intro a ha
        have hbn : (a (Fin.last k) : ℕ) + 1 ≤ n := by
          have := (a (Fin.last k)).isLt; omega
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          have : 0 < n := by omega
          exact_mod_cast this
        have hPpos : (0 : ℝ) < ∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1) := by positivity
        have hbrpos : (0 : ℝ) < ((a (Fin.last k) : ℕ) : ℝ) + 1 := by positivity
        have hnbpos : (0 : ℝ) < ((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ) := by
          have h1 : 0 < n - ((a (Fin.last k) : ℕ) + 1) := by
            have hSk := hS_ge_k a
            have hSe := hS_eq_gen a ha
            omega
          exact_mod_cast h1
        have hbc : (((a (Fin.last k) : ℕ) + 1 : ℕ) : ℝ) = ((a (Fin.last k) : ℕ) : ℝ) + 1 := by
          push_cast; ring
        dsimp only [G, Wt, K, fwd]
        rw [hprod a, hbc]
        have hPne : (∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1)) ≠ 0 := ne_of_gt hPpos
        have hbrne : ((a (Fin.last k) : ℕ) : ℝ) + 1 ≠ 0 := ne_of_gt hbrpos
        have hnbne : ((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ) ≠ 0 := ne_of_gt hnbpos
        have hB : (0 : ℝ) ≤ (n : ℝ) / ((((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ)) * (((a (Fin.last k) : ℕ) : ℝ) + 1)) :=
          le_of_lt (div_pos hnpos (mul_pos hnbpos hbrpos))
        have hC : (0 : ℝ) ≤ ((((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ)) / (∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1))) :=
          le_of_lt (div_pos hnbpos hPpos)
        have hBC : (n : ℝ) / ((∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1)) * (((a (Fin.last k) : ℕ) : ℝ) + 1))
            = ((n : ℝ) / ((((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ)) * (((a (Fin.last k) : ℕ) : ℝ) + 1)))
              * ((((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ)) / (∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1))) := by
          have h1 : (∏ i : Fin k, (((a (Fin.castSucc i) : ℕ) : ℝ) + 1)) * (((a (Fin.last k) : ℕ) : ℝ) + 1) ≠ 0 := mul_ne_zero hPne hbrne
          have h2 : (((n - ((a (Fin.last k) : ℕ) + 1) : ℕ) : ℝ)) * (((a (Fin.last k) : ℕ) : ℝ) + 1) ≠ 0 := mul_ne_zero hnbne hbrne
          field_simp
        rw [hBC, Real.mul_rpow hB hC]
    exact hbij.trans hT
  · intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hbpos : (0 : ℝ) < (b : ℝ) := by
      have hb0 : 0 < b := by omega
      exact_mod_cast hb0
    have hnmpos : (0 : ℝ) < ((n - b : ℕ) : ℝ) := by
      have h0 : 0 < n - b := by omega
      exact_mod_cast h0
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h0 : 0 < n := by omega
      exact_mod_cast h0
    exact Real.rpow_pos_of_pos (div_pos hnpos (mul_pos hnmpos hbpos)) p
  /- @proof-region region.target-node.session.fc09eeb2c2d09536 end -/

end Statlib.Imported
