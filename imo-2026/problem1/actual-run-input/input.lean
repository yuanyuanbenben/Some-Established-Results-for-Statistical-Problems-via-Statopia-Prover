import Mathlib

/- The five published claims are bundled into one target for the Deep runner.
   Each conjunct has the same quantifiers, hypotheses, and conclusion as the
   corresponding theorem in problem.lean; none is available as an assumption. -/

abbrev Board := Multiset ℕ

def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-- The conjunction of all five claims in the published Q1 problem file. -/
theorem main_theorem :
    (∀ (B₀ : Board), IsInitial B₀ →
      ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1))) ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B' : Board), Reachable B₀ B' → IsTerminal B' → HasUniqueLarge B') ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B₁ B₂ : Board), Reachable B₀ B₁ → Reachable B₀ B₂ →
        IsTerminal B₁ → IsTerminal B₂ →
        ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂)) ∧
    (∀ (B₀ : Board), IsInitial B₀ →
      ∀ (B' : Board), Reachable B₀ B' → IsTerminal B' →
        ∀ (M : ℕ), 1 < M → M ∈ B' → M = Mval B₀) ∧
    (∀ (B₀ : Board), IsInitial B₀ → 1 < Mval B₀) := by
  sorry
