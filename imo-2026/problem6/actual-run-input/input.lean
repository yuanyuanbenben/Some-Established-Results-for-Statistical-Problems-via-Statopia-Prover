import Mathlib

namespace IMO2026P6

/- The source problem numbers the terms a_1, a_2, ...; this file uses a 0-based
   function, so a 0 corresponds to a_1. The last conjunct makes a (n+1) the
   least later integer meeting the gcd condition, not merely one example. -/
def IsValidSeq (a : Nat -> Nat) : Prop :=
  (forall n, 1 < a n) ∧
  (forall n,
    a n < a (n + 1) ∧
    (forall i, i <= n -> 1 < Nat.gcd (a (n + 1)) (a i)) ∧
    (forall b, a n < b -> b < a (n + 1) ->
      exists i, i <= n ∧ Nat.gcd b (a i) = 1))

/-- IMO 2026, Problem 6: the increasing greedy gcd sequence is additively
periodic. The period and translation are both strictly positive. -/
theorem imo2026_problem6 (a : Nat -> Nat) (ha : IsValidSeq a) :
    exists T L : Nat, 0 < T ∧ 0 < L ∧
      forall n, a (n + T) = a n + L := by
  sorry

end IMO2026P6
