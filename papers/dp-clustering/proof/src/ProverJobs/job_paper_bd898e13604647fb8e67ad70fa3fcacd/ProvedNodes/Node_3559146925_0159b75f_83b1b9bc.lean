import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Vocabulary
import ProverJobs.job_paper_bd898e13604647fb8e67ad70fa3fcacd.Base

open Statlib.Imported

namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_3559146925_0159b75f : ∀ (t s : ℕ) (sv : Fin t → ℕ)
    (hsv : ∑ j : Fin t, sv j = s),
    ((Finset.univ.filter
        (fun f : Fin s → Fin t =>
          ∀ j : Fin t, (Finset.univ.filter (fun i : Fin s => f i = j)).card = sv j)).card : ℝ)
      = (s.factorial : ℝ) / ∏ j : Fin t, ((sv j).factorial : ℝ) := by
  /- @proof-region region.target-node.session.51f6382e472e5caa begin -/
  intro t s sv hsv
  have hmain : ∀ (s : ℕ) (t : ℕ) (w : Fin t → ℕ), (∑ j : Fin t, w j = s) →
      (Finset.univ.filter (fun f : Fin s → Fin t =>
        ∀ j : Fin t, (Finset.univ.filter (fun i : Fin s => f i = j)).card = w j)).card
        * ∏ j : Fin t, (w j).factorial = s.factorial := by
    intro s
    induction s with
    | zero =>
        intro t w hw
        have hw0 : ∀ j : Fin t, w j = 0 := fun j =>
          Finset.sum_eq_zero_iff.mp hw j (Finset.mem_univ j)
        have hprod : (∏ j : Fin t, (w j).factorial) = 1 := by
          simp [hw0]
        have hcard : (Finset.univ.filter (fun f : Fin 0 → Fin t =>
            ∀ j : Fin t, (Finset.univ.filter (fun i : Fin 0 => f i = j)).card = w j)).card = 1 := by
          have hfil : (Finset.univ.filter (fun f : Fin 0 → Fin t =>
              ∀ j : Fin t, (Finset.univ.filter (fun i : Fin 0 => f i = j)).card = w j))
              = (Finset.univ : Finset (Fin 0 → Fin t)) := by
            refine Finset.filter_true_of_mem ?_
            intro f _
            intro j
            rw [hw0 j]
            simp
          rw [hfil, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            pow_zero]
        rw [hcard, hprod]
        simp
    | succ s ih =>
        intro t w hw
        have hfib : ∀ (g : Fin s → Fin t) (j k : Fin t),
            (Finset.univ.filter (fun i : Fin (s+1) =>
                Fin.snoc (α := fun _ => Fin t) g j i = k)).card
              = (Finset.univ.filter (fun i : Fin s => g i = k)).card
                + (if j = k then 1 else 0) := by
          intro g j k
          rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.card_eq_sum_ones,
            Finset.sum_filter]
          rw [Fin.sum_univ_castSucc]
          simp [Fin.snoc_castSucc, Fin.snoc_last]
        have hstep1 :
            (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
              ∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)).card
            = ∑ j : Fin t, (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
                ∧ f (Fin.last s) = j)).card := by
          rw [Finset.card_eq_sum_card_fiberwise
            (f := fun f : Fin (s+1) → Fin t => f (Fin.last s))
            (s := Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
              ∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k))
            (t := (Finset.univ : Finset (Fin t)))
            (by intro x _; simp)]
          apply Finset.sum_congr rfl
          intro j _
          have heq : Finset.filter (fun a : Fin (s+1) → Fin t => a (Fin.last s) = j)
              (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                ∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k))
              = Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
                ∧ f (Fin.last s) = j) := by
            ext f
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [heq]
        have hstep2 : ∀ j : Fin t,
            (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
              (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
              ∧ f (Fin.last s) = j)).card
            = (Finset.univ.filter (fun g : Fin s → Fin t => 1 ≤ w j ∧
              ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                = w k - (if k = j then 1 else 0))).card := by
          intro j
          have hinj : Function.Injective
              (fun g : Fin s → Fin t => Fin.snoc (α := fun _ => Fin t) g j) := by
            intro g₁ g₂ h
            funext i
            have hh := congrFun h (Fin.castSucc i)
            simpa only [Fin.snoc_castSucc] using hh
          have hset : (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
              (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
              ∧ f (Fin.last s) = j))
              = (Finset.univ.filter (fun g : Fin s → Fin t => 1 ≤ w j ∧
              ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                = w k - (if k = j then 1 else 0))).image
                (fun g : Fin s → Fin t => Fin.snoc (α := fun _ => Fin t) g j) := by
            ext f
            simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, true_and]
            constructor
            · rintro ⟨hf, hfj⟩
              have hwj : 1 ≤ w j := by
                have hpos : 0 < (Finset.univ.filter (fun i : Fin (s+1) => f i = j)).card :=
                  Finset.card_pos.mpr ⟨Fin.last s, by simp [hfj]⟩
                have hfj' := hf j
                omega
              have h3 : Fin.snoc (α := fun _ => Fin t) (fun i : Fin s => f (Fin.castSucc i)) j
                  = f := by
                funext i
                rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
                · have hi : i = Fin.castSucc (⟨i.val, h⟩ : Fin s) := Fin.ext rfl
                  rw [hi, Fin.snoc_castSucc]
                · have hi : i = Fin.last s := Fin.ext h
                  rw [hi, Fin.snoc_last, hfj]
              refine ⟨fun i : Fin s => f (Fin.castSucc i), ⟨hwj, ?_⟩, h3⟩
              intro k
              have h1 := hfib (fun i : Fin s => f (Fin.castSucc i)) j k
              rw [h3] at h1
              rw [hf k] at h1
              by_cases hk : k = j
              · rw [if_pos hk]
                rw [if_pos hk.symm] at h1
                rw [h1, Nat.add_sub_cancel]
              · rw [if_neg hk]
                rw [if_neg (Ne.symm hk)] at h1
                rw [h1, Nat.add_sub_cancel]
            · rintro ⟨g, ⟨hwj, hg⟩, rfl⟩
              constructor
              · intro k
                rw [hfib g j k, hg k]
                by_cases hk : k = j
                · subst hk
                  simpa using Nat.sub_add_cancel hwj
                · rw [if_neg hk, if_neg (Ne.symm hk)]
                  simp
              · simp [Fin.snoc_last]
          rw [hset, Finset.card_image_of_injective _ hinj]
        have hstep3 : ∀ j : Fin t,
            (Finset.univ.filter (fun g : Fin s → Fin t => 1 ≤ w j ∧
              ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                = w k - (if k = j then 1 else 0))).card
              * ∏ k : Fin t, (w k).factorial = w j * s.factorial := by
          intro j
          by_cases hwj : w j = 0
          · have hcard0 : (Finset.univ.filter (fun g : Fin s → Fin t => 1 ≤ w j ∧
                ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                  = w k - (if k = j then 1 else 0))).card = 0 := by
              by_contra h
              obtain ⟨g, hg⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
              omega
            rw [hcard0, hwj, Nat.zero_mul, Nat.zero_mul]
          · have hwj1 : 1 ≤ w j := Nat.one_le_iff_ne_zero.mpr hwj
            have hEq : (Finset.univ.filter (fun g : Fin s → Fin t => 1 ≤ w j ∧
                ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                  = w k - (if k = j then 1 else 0)))
                = Finset.univ.filter (fun g : Fin s → Fin t =>
                ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                  = w k - (if k = j then 1 else 0)) := by
              ext g
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨-, h⟩; exact h
              · intro h; exact ⟨hwj1, h⟩
            have hsum : (∑ k : Fin t, (w k - (if k = j then 1 else 0))) = s := by
              have hpt : ∀ k : Fin t,
                  (w k - (if k = j then 1 else 0)) + (if k = j then 1 else 0) = w k := by
                intro k
                by_cases hk : k = j
                · subst hk
                  simpa using Nat.sub_add_cancel hwj1
                · rw [if_neg hk, Nat.sub_zero, Nat.add_zero]
              have h2 : (∑ k : Fin t, (if k = j then 1 else 0)) = 1 := by
                rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
                have hone : (Finset.univ.filter (fun k : Fin t => k = j)) = {j} := by
                  ext k
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    Finset.mem_singleton]
                rw [hone]
                simp
              have e1 : (∑ k : Fin t,
                    ((w k - (if k = j then 1 else 0)) + (if k = j then 1 else 0)))
                  = (∑ k : Fin t, (w k - (if k = j then 1 else 0))) + 1 := by
                rw [Finset.sum_add_distrib, h2]
              have e2 : (∑ k : Fin t,
                    ((w k - (if k = j then 1 else 0)) + (if k = j then 1 else 0)))
                  = ∑ k : Fin t, w k := Finset.sum_congr rfl (fun k _ => hpt k)
              omega
            have hfac : (w j).factorial = w j * (w j - 1).factorial := by
              have h := Nat.factorial_succ (w j - 1)
              rw [Nat.sub_add_cancel hwj1] at h
              exact h
            have hsplitL : (∏ k : Fin t, (w k).factorial)
                = (w j).factorial * (∏ k ∈ (Finset.univ.erase j), (w k).factorial) := by
              conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ j)]
              rw [Finset.prod_insert (by simp : j ∉ Finset.univ.erase j)]
            have hsplitR : (∏ k : Fin t, (w k - (if k = j then 1 else 0)).factorial)
                = (w j - 1).factorial
                  * (∏ k ∈ (Finset.univ.erase j), (w k).factorial) := by
              conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ j)]
              rw [Finset.prod_insert (by simp : j ∉ Finset.univ.erase j)]
              congr 1
              · rw [if_pos rfl]
              exact Finset.prod_congr rfl (fun k hk => by
                rw [Finset.mem_erase] at hk
                rw [if_neg hk.1, Nat.sub_zero])
            have hih : (Finset.univ.filter (fun g : Fin s → Fin t =>
                  ∀ k : Fin t, (Finset.univ.filter (fun i : Fin s => g i = k)).card
                    = w k - (if k = j then 1 else 0))).card
                * (∏ k : Fin t, (w k - (if k = j then 1 else 0)).factorial)
                = s.factorial :=
              ih t (fun k => w k - (if k = j then 1 else 0)) hsum
            have hprod : (∏ k : Fin t, (w k).factorial)
                = w j * ∏ k : Fin t, (w k - (if k = j then 1 else 0)).factorial := by
              rw [hsplitL, hsplitR, hfac]
              ring
            rw [hEq, hprod, mul_left_comm, hih]
        calc (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                ∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)).card
              * ∏ k : Fin t, (w k).factorial
            = (∑ j : Fin t, (Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
                ∧ f (Fin.last s) = j)).card) * ∏ k : Fin t, (w k).factorial := by rw [hstep1]
          _ = ∑ j : Fin t, ((Finset.univ.filter (fun f : Fin (s+1) → Fin t =>
                (∀ k : Fin t, (Finset.univ.filter (fun i : Fin (s+1) => f i = k)).card = w k)
                ∧ f (Fin.last s) = j)).card * ∏ k : Fin t, (w k).factorial) := by
              rw [Finset.sum_mul]
          _ = ∑ j : Fin t, (w j * s.factorial) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hstep2 j]
              exact hstep3 j
          _ = (∑ j : Fin t, w j) * s.factorial := by rw [Finset.sum_mul]
          _ = (s+1) * s.factorial := by rw [hw]
          _ = (s+1).factorial := by rw [Nat.factorial_succ]
  have hnat := hmain s t sv hsv
  have hreal :
      ((Finset.univ.filter
        (fun f : Fin s → Fin t =>
          ∀ j : Fin t, (Finset.univ.filter (fun i : Fin s => f i = j)).card = sv j)).card : ℝ)
        * (∏ j : Fin t, ((sv j).factorial : ℝ)) = (s.factorial : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at h
    simpa using h
  have hne : (∏ j : Fin t, ((sv j).factorial : ℝ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    exact_mod_cast Nat.factorial_ne_zero (sv j)
  rw [eq_div_iff hne]
  exact hreal
  /- @proof-region region.target-node.session.51f6382e472e5caa end -/

end Statlib.Imported
