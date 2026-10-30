import ProverJobs.real_V_eq_15312944933b.Vocabulary
import ProverJobs.real_V_eq_15312944933b.Base
import ProverJobs.real_V_eq_15312944933b.ProvedNodes.Node_2170517157_b55dd4e4_4000b667
open scoped BigOperators
open LiuBangXiangYu

open scoped BigOperators
namespace LiuBangXiangYu

set_option autoImplicit false in
theorem statopia_math_node_689319304_41a3eefa : ∀ (n : ℕ) (p : Fin (n + 1) → ℝ) (M : Finset ℝ)
    (hp : StrictMono p)
    (hM : ∀ x ∈ M, p 0 ≤ x ∧ x ≤ p (Fin.last n)),
    (∑ k : Fin n, Multiset.ofList (List.zipWith (fun a b => b - a)
      (p (Fin.castSucc k) :: ((M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·)) ++ [p (Fin.succ k)])
      (p (Fin.castSucc k) :: ((M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·)) ++ [p (Fin.succ k)]).tail))
    = Multiset.ofList (List.zipWith (fun a b => b - a)
      ((Finset.image p Finset.univ ∪ M).sort (· ≤ ·))
      ((Finset.image p Finset.univ ∪ M).sort (· ≤ ·)).tail) := by
  /- @proof-region region.target-node.session.b92ed87173e4a96c begin -/
  intro n p M hp hM
  let G : List ℝ → List ℝ := fun L => List.zipWith (fun a b => b - a) L L.tail
  let W : Fin n → List ℝ := fun k =>
    (M.filter (fun x => p (Fin.castSucc k) < x ∧ x < p (Fin.succ k))).sort (· ≤ ·)
  let T : Fin n → List ℝ := fun k => p (Fin.castSucc k) :: (W k ++ [p (Fin.succ k)])
  let S : Finset ℝ := Finset.image p Finset.univ ∪ M
  let J : List ℝ := p 0 :: (List.ofFn (fun k : Fin n => W k ++ [p (Fin.succ k)])).flatten
  change (∑ k : Fin n, Multiset.ofList (G (T k))) = Multiset.ofList (G (S.sort (· ≤ ·)))
  have gcons : ∀ (a y : ℝ) (Y : List ℝ), G (a :: y :: Y) = (y - a) :: G (y :: Y) := by
    intro a y Y
    simp [G, List.tail_cons]
  have gsing : ∀ x : ℝ, G [x] = [] := by
    intro x
    simp [G, List.tail_cons]
  have tel2 : ∀ (A B' : List ℝ) (x : ℝ),
      G ((A ++ [x]) ++ B') = G (A ++ [x]) ++ G (x :: B') := by
    intro A
    induction A with
    | nil =>
      intro B' x
      simp [gsing]
    | cons a A' ih =>
      intro B' x
      cases A' with
      | nil =>
        show G (a :: x :: B') = G (a :: [x]) ++ G (x :: B')
        rw [gcons a x B', gcons a x [], gsing x]
        rfl
      | cons a' A'' =>
        show G (a :: a' :: ((A'' ++ [x]) ++ B')) = G (a :: a' :: (A'' ++ [x])) ++ G (x :: B')
        rw [gcons a a' ((A'' ++ [x]) ++ B'), gcons a a' (A'' ++ [x])]
        show (a' - a) :: G (((a' :: A'') ++ [x]) ++ B') =
          ((a' - a) :: G ((a' :: A'') ++ [x])) ++ G (x :: B')
        rw [ih B' x]
        rfl
  have ofFn_sum : ∀ (m : ℕ) (f : Fin m → List ℝ),
      (∑ k : Fin m, Multiset.ofList (f k)) = Multiset.ofList ((List.ofFn f).flatten) := by
    intro m
    induction m with
    | zero =>
      intro f
      simp
    | succ m ih =>
      intro f
      rw [Fin.sum_univ_succ, ih (fun k => f k.succ), Multiset.coe_add, List.ofFn_succ, List.flatten_cons]
  have h_ofFn : (∑ k : Fin n, Multiset.ofList (G (T k))) =
      Multiset.ofList ((List.ofFn (fun k : Fin n => G (T k))).flatten) :=
    ofFn_sum n (fun k => G (T k))
  have flat_tel : ∀ (m : ℕ) (q : Fin (m + 1) → ℝ) (V : Fin m → List ℝ),
      G (q 0 :: (List.ofFn (fun k : Fin m => V k ++ [q (Fin.succ k)])).flatten) =
        (List.ofFn (fun k : Fin m => G (q (Fin.castSucc k) :: (V k ++ [q (Fin.succ k)])))).flatten := by
    intro m
    induction m with
    | zero =>
      intro q V
      simp [gsing]
    | succ m ih =>
      intro q V
      rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatten_cons]
      have ih' : G (q (Fin.succ 0) :: (List.ofFn (fun k : Fin m => V (Fin.succ k) ++ [q (Fin.succ (Fin.succ k))])).flatten)
          = (List.ofFn (fun k : Fin m => G (q (Fin.succ k).castSucc :: (V (Fin.succ k) ++ [q (Fin.succ (Fin.succ k))])))).flatten :=
        ih (fun j : Fin (m + 1) => q (Fin.succ j)) (fun k : Fin m => V (Fin.succ k))
      show G (((q 0 :: V 0) ++ [q (Fin.succ 0)]) ++ (List.ofFn (fun k : Fin m => V (Fin.succ k) ++ [q (Fin.succ (Fin.succ k))])).flatten)
          = G (q (Fin.castSucc 0) :: (V 0 ++ [q (Fin.succ 0)])) ++
              (List.ofFn (fun k : Fin m => G (q (Fin.succ k).castSucc :: (V (Fin.succ k) ++ [q (Fin.succ (Fin.succ k))])))).flatten
      rw [tel2 (q 0 :: V 0)
        (List.ofFn (fun k : Fin m => V (Fin.succ k) ++ [q (Fin.succ (Fin.succ k))])).flatten
        (q (Fin.succ 0))]
      rw [ih']
      rfl
  have h_tel : (List.ofFn (fun k : Fin n => G (T k))).flatten = G J := by
    simpa only [T, J] using (flat_tel n p W).symm
  have h_J : J = S.sort (· ≤ ·) :=
    statopia_math_node_2170517157_b55dd4e4 n p M hp hM
  rw [h_ofFn, h_tel, h_J]
  /- @proof-region region.target-node.session.b92ed87173e4a96c end -/

end LiuBangXiangYu
