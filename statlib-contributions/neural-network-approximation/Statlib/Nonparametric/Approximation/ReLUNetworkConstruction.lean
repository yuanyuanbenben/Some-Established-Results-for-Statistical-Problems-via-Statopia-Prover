import Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

open Statlib.Nonparametric.Vocabulary

/-! # Fully Connected ReLU Network Constructions

Reusable exact network combinators and fixed-width approximation gadgets.
-/

namespace Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

/-- The ReLU tent map used in the exponentially accurate square construction. -/
private noncomputable def reluApproxTent (x : ℝ) : ℝ :=
  2 * relu x - 4 * relu (x - 1 / 2)

private theorem reluApproxTent_eq_left {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    reluApproxTent x = 2 * x := by
  rw [reluApproxTent]
  simp only [relu]
  rw [max_eq_left hx0, max_eq_right]
  · ring
  · linarith

private theorem reluApproxTent_eq_right {x : ℝ} (hx : 1 / 2 ≤ x) :
    reluApproxTent x = 2 * (1 - x) := by
  rw [reluApproxTent]
  simp only [relu]
  rw [max_eq_left, max_eq_left]
  · ring
  · linarith
  · linarith

private theorem reluApproxTent_mem_unitInterval {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    reluApproxTent x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hhalf : x ≤ 1 / 2
  · rw [reluApproxTent_eq_left hx0 hhalf]
    constructor <;> linarith
  · have hhalf' : 1 / 2 ≤ x := le_of_not_ge hhalf
    rw [reluApproxTent_eq_right hhalf']
    constructor <;> linarith

/-- The elementary refinement identity behind the sawtooth square network. -/
private theorem reluApproxTent_square_error_identity {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x - x ^ 2 =
      (1 / 4 : ℝ) * reluApproxTent x +
        (1 / 4 : ℝ) * (reluApproxTent x - reluApproxTent x ^ 2) := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hhalf : x ≤ 1 / 2
  · rw [reluApproxTent_eq_left hx0 hhalf]
    ring
  · have hhalf' : 1 / 2 ≤ x := le_of_not_ge hhalf
    rw [reluApproxTent_eq_right hhalf']
    ring

/-- The `m`-fold iterate of the ReLU tent map. -/
private noncomputable def reluApproxTentIter : ℕ → ℝ → ℝ
  | 0, x => x
  | m + 1, x => reluApproxTent (reluApproxTentIter m x)

/-- The truncated sawtooth expansion of the square map. -/
private noncomputable def reluApproxSquareApprox : ℕ → ℝ → ℝ
  | 0, x => x
  | m + 1, x =>
      reluApproxSquareApprox m x -
        (1 / 4 : ℝ) ^ (m + 1) * reluApproxTentIter (m + 1) x

private theorem reluApproxTentIter_mem_unitInterval (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    reluApproxTentIter m x ∈ Set.Icc (0 : ℝ) 1 := by
  induction m with
  | zero => simpa [reluApproxTentIter] using hx
  | succ m ih =>
      simpa [reluApproxTentIter] using reluApproxTent_mem_unitInterval ih

private theorem reluApproxSquareApprox_error_identity (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    reluApproxSquareApprox m x - x ^ 2 =
      (1 / 4 : ℝ) ^ m *
        (reluApproxTentIter m x - reluApproxTentIter m x ^ 2) := by
  induction m with
  | zero => simp [reluApproxSquareApprox, reluApproxTentIter]
  | succ m ih =>
      have hiter := reluApproxTentIter_mem_unitInterval m hx
      have hrefine := reluApproxTent_square_error_identity hiter
      rw [reluApproxSquareApprox]
      calc
        reluApproxSquareApprox m x -
              (1 / 4 : ℝ) ^ (m + 1) * reluApproxTentIter (m + 1) x - x ^ 2 =
            (reluApproxSquareApprox m x - x ^ 2) -
              (1 / 4 : ℝ) ^ (m + 1) * reluApproxTentIter (m + 1) x := by ring
        _ = (1 / 4 : ℝ) ^ m *
              (reluApproxTentIter m x - reluApproxTentIter m x ^ 2) -
              (1 / 4 : ℝ) ^ (m + 1) * reluApproxTentIter (m + 1) x := by
              rw [ih]
        _ = (1 / 4 : ℝ) ^ (m + 1) *
              (reluApproxTentIter (m + 1) x -
                reluApproxTentIter (m + 1) x ^ 2) := by
              simp only [reluApproxTentIter]
              rw [hrefine]
              rw [pow_succ]
              ring

private theorem reluApproxSquareApprox_error_le (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |reluApproxSquareApprox m x - x ^ 2| ≤ (1 / 4 : ℝ) ^ m := by
  rw [reluApproxSquareApprox_error_identity m hx, abs_mul]
  have hiter := reluApproxTentIter_mem_unitInterval m hx
  have hpow : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
  have herr0 : 0 ≤ reluApproxTentIter m x - reluApproxTentIter m x ^ 2 := by
    rcases hiter with ⟨h0, h1⟩
    nlinarith [sq_nonneg (reluApproxTentIter m x)]
  have herr1 : reluApproxTentIter m x - reluApproxTentIter m x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (reluApproxTentIter m x)]
  rw [abs_of_nonneg hpow, abs_of_nonneg herr0]
  exact mul_le_of_le_one_right hpow herr1

/-- A width-three network carrying the current tent iterate and square
approximant in two persistent registers.  Each refinement uses two hidden
layers: one forms `relu (y - 1/2)`, and the next updates both registers. -/
private noncomputable def reluApproxSquareNet (m : ℕ) : FullyConnectedReLUNet 1 where
  depth := 2 * m + 1
  width := 3
  input :=
    { weight := fun o _ => if (o : ℕ) < 2 then 1 else 0
      bias := fun _ => 0 }
  hidden := fun t =>
    if (t : ℕ) % 2 = 0 then
      { weight := fun o i =>
          if (o : ℕ) = 0 then if (i : ℕ) = 0 then 1 else 0
          else if (o : ℕ) = 1 then if (i : ℕ) = 1 then 1 else 0
          else if (i : ℕ) = 1 then 1 else 0
        bias := fun o => if (o : ℕ) = 2 then -(1 / 2 : ℝ) else 0 }
    else
      let c : ℝ := (1 / 4 : ℝ) ^ ((t : ℕ) / 2 + 1)
      { weight := fun o i =>
          if (o : ℕ) = 0 then
            if (i : ℕ) = 0 then 1
            else if (i : ℕ) = 1 then -(2 * c)
            else 4 * c
          else if (o : ℕ) = 1 then
            if (i : ℕ) = 1 then 2 else if (i : ℕ) = 2 then -4 else 0
          else 0
        bias := fun _ => 0 }
  outputWeight := fun o => if (o : ℕ) = 0 then 1 else 0
  outputBias := 0

private theorem reluApproxSquareNet_state (m k : ℕ) (hk : k ≤ m)
    (x : Fin 1 → ℝ) (hx : x 0 ∈ Set.Icc (0 : ℝ) 1) :
    (reluApproxSquareNet m).hiddenState x (2 * k) ⟨0, by simp [reluApproxSquareNet]⟩ =
        reluApproxSquareApprox k (x 0) ∧
      (reluApproxSquareNet m).hiddenState x (2 * k) ⟨1, by simp [reluApproxSquareNet]⟩ =
        reluApproxTentIter k (x 0) ∧
      (reluApproxSquareNet m).hiddenState x (2 * k) ⟨2, by simp [reluApproxSquareNet]⟩ = 0 := by
  induction k with
  | zero =>
      rcases hx with ⟨hx0, _⟩
      simp [reluApproxSquareNet, FullyConnectedReLUNet.hiddenState,
        DenseLayer.reluApply, DenseLayer.apply, reluVec,
        reluApproxSquareApprox, reluApproxTentIter, relu, max_eq_left hx0]
  | succ k ih =>
      have hklt : k < m := by omega
      have ih' := ih (by omega)
      have hguard0 : 2 * k < (reluApproxSquareNet m).depth - 1 := by
        simp [reluApproxSquareNet]
        omega
      have hguard1 : 2 * k + 1 < (reluApproxSquareNet m).depth - 1 := by
        simp [reluApproxSquareNet]
        omega
      have hpar0 : (2 * k) % 2 = 0 := by omega
      have hpar1 : (2 * k + 1) % 2 ≠ 0 := by omega
      have hiter := reluApproxTentIter_mem_unitInterval k hx
      have happrox_nonneg : 0 ≤ reluApproxSquareApprox k (x 0) := by
        have herr := reluApproxSquareApprox_error_identity k hx
        have hy := hiter
        rcases hy with ⟨hy0, hy1⟩
        have hp : 0 ≤ (1 / 4 : ℝ) ^ k := by positivity
        have he : 0 ≤ reluApproxTentIter k (x 0) - reluApproxTentIter k (x 0) ^ 2 := by
          nlinarith [sq_nonneg (reluApproxTentIter k (x 0))]
        nlinarith [sq_nonneg (x 0), mul_nonneg hp he]
      have htent_nonneg : 0 ≤ reluApproxTent (reluApproxTentIter k (x 0)) :=
        (reluApproxTent_mem_unitInterval hiter).1
      have hnext_nonneg : 0 ≤ reluApproxSquareApprox (k + 1) (x 0) := by
        have herr := reluApproxSquareApprox_error_identity (k + 1) hx
        have hy := reluApproxTentIter_mem_unitInterval (k + 1) hx
        rcases hy with ⟨hy0, hy1⟩
        have hp : 0 ≤ (1 / 4 : ℝ) ^ (k + 1) := by positivity
        have he : 0 ≤ reluApproxTentIter (k + 1) (x 0) -
            reluApproxTentIter (k + 1) (x 0) ^ 2 := by
          nlinarith [sq_nonneg (reluApproxTentIter (k + 1) (x 0))]
        nlinarith [sq_nonneg (x 0), mul_nonneg hp he]
      rcases ih' with ⟨ih0, ih1, ih2⟩
      let q0 : Fin (reluApproxSquareNet m).width :=
        ⟨0, by simp [reluApproxSquareNet]⟩
      let q1 : Fin (reluApproxSquareNet m).width :=
        ⟨1, by simp [reluApproxSquareNet]⟩
      let q2 : Fin (reluApproxSquareNet m).width :=
        ⟨2, by simp [reluApproxSquareNet]⟩
      have ih0' : (reluApproxSquareNet m).hiddenState x (2 * k) q0 =
          reluApproxSquareApprox k (x 0) := by simpa [q0] using ih0
      have ih1' : (reluApproxSquareNet m).hiddenState x (2 * k) q1 =
          reluApproxTentIter k (x 0) := by simpa [q1] using ih1
      have ih2' : (reluApproxSquareNet m).hiddenState x (2 * k) q2 = 0 := by
        simpa [q2] using ih2
      have hs0 : (reluApproxSquareNet m).hiddenState x (2 * k + 1) =
          ((reluApproxSquareNet m).hidden ⟨2 * k, hguard0⟩).reluApply
            ((reluApproxSquareNet m).hiddenState x (2 * k)) := by
        simp [FullyConnectedReLUNet.hiddenState, hguard0]
      have hs1 : (reluApproxSquareNet m).hiddenState x (2 * (k + 1)) =
          ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply
            ((reluApproxSquareNet m).hiddenState x (2 * k + 1)) := by
        have htwo : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [htwo]
        simp [FullyConnectedReLUNet.hiddenState, hguard0, hguard1]
      have h_even : ∀ s : Fin (reluApproxSquareNet m).width → ℝ,
          ((reluApproxSquareNet m).hidden ⟨2 * k, hguard0⟩).reluApply s q0 =
              relu (s q0) ∧
            ((reluApproxSquareNet m).hidden ⟨2 * k, hguard0⟩).reluApply s q1 =
              relu (s q1) ∧
            ((reluApproxSquareNet m).hidden ⟨2 * k, hguard0⟩).reluApply s q2 =
              relu (s q1 - 1 / 2) := by
        intro s
        simp [q0, q1, q2, reluApproxSquareNet, hpar0, DenseLayer.reluApply,
          DenseLayer.apply, reluVec, Fin.sum_univ_three]
        ring
      have h_odd : ∀ s : Fin (reluApproxSquareNet m).width → ℝ,
          ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply s q0 =
              relu (s q0 - 2 * (1 / 4 : ℝ) ^ (k + 1) * s q1 +
                4 * (1 / 4 : ℝ) ^ (k + 1) * s q2) ∧
            ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply s q1 =
              relu (2 * s q1 - 4 * s q2) ∧
            ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply s q2 = 0 := by
        intro s
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simp [q0, q1, q2, reluApproxSquareNet, hdiv, DenseLayer.reluApply,
          DenseLayer.apply, reluVec, Fin.sum_univ_three, relu]
        all_goals ring_nf
        all_goals simp
      have hmid0 : (reluApproxSquareNet m).hiddenState x (2 * k + 1) q0 =
          reluApproxSquareApprox k (x 0) := by
        rw [hs0, (h_even _).1, ih0']
        simp [relu, max_eq_left happrox_nonneg]
      have hmid1 : (reluApproxSquareNet m).hiddenState x (2 * k + 1) q1 =
          reluApproxTentIter k (x 0) := by
        rw [hs0, (h_even _).2.1, ih1']
        simp [relu, max_eq_left hiter.1]
      have hmid2 : (reluApproxSquareNet m).hiddenState x (2 * k + 1) q2 =
          relu (reluApproxTentIter k (x 0) - 1 / 2) := by
        rw [hs0, (h_even _).2.2, ih1']
      rw [hs1]
      have htent_formula :
          2 * reluApproxTentIter k (x 0) -
              4 * relu (reluApproxTentIter k (x 0) - 1 / 2) =
            reluApproxTent (reluApproxTentIter k (x 0)) := by
        rw [reluApproxTent]
        simp [relu, max_eq_left hiter.1]
      have hupdate_formula :
          reluApproxSquareApprox k (x 0) -
                2 * (1 / 4 : ℝ) ^ (k + 1) * reluApproxTentIter k (x 0) +
                4 * (1 / 4 : ℝ) ^ (k + 1) *
                  relu (reluApproxTentIter k (x 0) - 1 / 2) =
            reluApproxSquareApprox (k + 1) (x 0) := by
        rw [reluApproxSquareApprox, reluApproxTentIter]
        rw [← htent_formula]
        ring
      change
        ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply
              ((reluApproxSquareNet m).hiddenState x (2 * k + 1)) q0 =
            reluApproxSquareApprox (k + 1) (x 0) ∧
          ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply
                ((reluApproxSquareNet m).hiddenState x (2 * k + 1)) q1 =
              reluApproxTentIter (k + 1) (x 0) ∧
            ((reluApproxSquareNet m).hidden ⟨2 * k + 1, hguard1⟩).reluApply
                ((reluApproxSquareNet m).hiddenState x (2 * k + 1)) q2 = 0
      constructor
      · rw [(h_odd _).1, hmid0, hmid1, hmid2, hupdate_formula]
        simp [relu, max_eq_left hnext_nonneg]
      constructor
      · rw [(h_odd _).2.1, hmid1, hmid2, htent_formula]
        simp [relu, max_eq_left htent_nonneg]
        simp [reluApproxTentIter]
      · rw [(h_odd _).2.2]

private theorem reluApproxSquareNet_realize (m : ℕ) (x : Fin 1 → ℝ)
    (hx : x 0 ∈ Set.Icc (0 : ℝ) 1) :
    (reluApproxSquareNet m).realize x = reluApproxSquareApprox m (x 0) := by
  rcases reluApproxSquareNet_state m m le_rfl x hx with ⟨h0, h1, h2⟩
  have hdepth : (reluApproxSquareNet m).depth - 1 = 2 * m := by
    simp [reluApproxSquareNet]
  rw [FullyConnectedReLUNet.realize, hdepth]
  simp [reluApproxSquareNet]
  simpa [reluApproxSquareNet] using h0

/-- Exponentially accurate fixed-width fully connected ReLU approximation of
the square map on `[0,1]`.  The precision improves as `4^{-m}` while the depth
is exactly `2m+1`. -/
theorem exists_reluNetworkClass_unitInterval_square_fixed_width_exponential_depth_rate
    (m : ℕ) :
    ∃ N : FullyConnectedReLUNet 1,
      N.depth = 2 * m + 1 ∧
      N.width = 3 ∧
      N.parameterCount = fullyConnectedReLUParameterCount 1 (2 * m + 1) 3 ∧
      N.realize ∈ reluNetworkClass 1 (2 * m + 1) 3
          (fullyConnectedReLUParameterCount 1 (2 * m + 1) 3) ∧
      ∀ x : Fin 1 → ℝ, x 0 ∈ Set.Icc (0 : ℝ) 1 →
        |N.realize x - (x 0) ^ 2| ≤ (1 / 4 : ℝ) ^ m := by
  refine ⟨reluApproxSquareNet m, rfl, rfl, rfl, ?_, ?_⟩
  · rw [reluNetworkClass]
    refine ⟨reluApproxSquareNet m, ?_, le_rfl, le_rfl, le_rfl, fun _ => rfl⟩
    simp [reluApproxSquareNet]
  · intro x hx
    rw [reluApproxSquareNet_realize m x hx]
    exact reluApproxSquareApprox_error_le m hx

/-- Precompose a concrete ReLU network with a scalar affine map. -/
noncomputable def FullyConnectedReLUNet.precomposeScalarAffine {d : ℕ}
    (N : FullyConnectedReLUNet 1) (a : Fin d → ℝ) (b : ℝ) :
    FullyConnectedReLUNet d where
  depth := N.depth
  width := N.width
  input :=
    { weight := fun o i => N.input.weight o 0 * a i
      bias := fun o => N.input.weight o 0 * b + N.input.bias o }
  hidden := N.hidden
  outputWeight := N.outputWeight
  outputBias := N.outputBias

theorem FullyConnectedReLUNet.precomposeScalarAffine_input_reluApply {d : ℕ}
    (N : FullyConnectedReLUNet 1) (a : Fin d → ℝ) (b : ℝ) (x : Fin d → ℝ) :
    (FullyConnectedReLUNet.precomposeScalarAffine N a b).input.reluApply x =
      N.input.reluApply (fun _ => (∑ i : Fin d, a i * x i) + b) := by
  funext o
  simp only [FullyConnectedReLUNet.precomposeScalarAffine, DenseLayer.reluApply,
    DenseLayer.apply, reluVec, Fin.sum_univ_one]
  congr 1
  calc
    (∑ i : Fin d, N.input.weight o 0 * a i * x i) +
          (N.input.weight o 0 * b + N.input.bias o) =
        (∑ i : Fin d, N.input.weight o 0 * (a i * x i)) +
          (N.input.weight o 0 * b + N.input.bias o) := by
            congr 2
            funext i
            ring
    _ = N.input.weight o 0 * (∑ i : Fin d, a i * x i) +
          (N.input.weight o 0 * b + N.input.bias o) := by
            rw [Finset.mul_sum]
    _ = N.input.weight o 0 * ((∑ i : Fin d, a i * x i) + b) +
          N.input.bias o := by ring

theorem FullyConnectedReLUNet.precomposeScalarAffine_hiddenState {d : ℕ}
    (N : FullyConnectedReLUNet 1) (a : Fin d → ℝ) (b : ℝ) (x : Fin d → ℝ)
    (t : ℕ) :
    (FullyConnectedReLUNet.precomposeScalarAffine N a b).hiddenState x t =
      N.hiddenState (fun _ => (∑ i : Fin d, a i * x i) + b) t := by
  induction t with
  | zero =>
      simpa [FullyConnectedReLUNet.hiddenState] using
        FullyConnectedReLUNet.precomposeScalarAffine_input_reluApply N a b x
  | succ t ih =>
      simp only [FullyConnectedReLUNet.hiddenState]
      by_cases ht : t < N.depth - 1
      · simp [FullyConnectedReLUNet.precomposeScalarAffine, ht]
        exact congrArg (N.hidden ⟨t, ht⟩).reluApply ih
      · simp [FullyConnectedReLUNet.precomposeScalarAffine, ht]
        simpa [FullyConnectedReLUNet.precomposeScalarAffine] using ih

theorem FullyConnectedReLUNet.precomposeScalarAffine_realize {d : ℕ}
    (N : FullyConnectedReLUNet 1) (a : Fin d → ℝ) (b : ℝ) (x : Fin d → ℝ) :
    (FullyConnectedReLUNet.precomposeScalarAffine N a b).realize x =
      N.realize (fun _ => (∑ i : Fin d, a i * x i) + b) := by
  have hs := FullyConnectedReLUNet.precomposeScalarAffine_hiddenState N a b x (N.depth - 1)
  change
    (∑ j, N.outputWeight j *
        (FullyConnectedReLUNet.precomposeScalarAffine N a b).hiddenState x (N.depth - 1) j) +
        N.outputBias =
      (∑ j, N.outputWeight j *
        N.hiddenState (fun _ => (∑ i : Fin d, a i * x i) + b) (N.depth - 1) j) +
        N.outputBias
  rw [hs]

/-- Coefficients of the four scalar affine forms used in the multiplication
polarization identity. -/
private noncomputable def reluApproxMulAffineCoeff (R : ℝ) (i : Fin 4) (q : Fin 2) : ℝ :=
  if (i : ℕ) = 0 then 1 / (4 * R)
  else if (i : ℕ) = 1 then -(1 / (4 * R))
  else if (i : ℕ) = 2 then if (q : ℕ) = 0 then 1 / (4 * R) else -(1 / (4 * R))
  else if (q : ℕ) = 0 then -(1 / (4 * R)) else 1 / (4 * R)

private noncomputable def reluApproxMulSquareInput (R : ℝ) (i : Fin 4)
    (x : Fin 2 → ℝ) : ℝ :=
  (∑ q : Fin 2, reluApproxMulAffineCoeff R i q * x q) + 1 / 2

private noncomputable def reluApproxMulPolarizationCoeff (R : ℝ) (i : Fin 4) : ℝ :=
  if (i : ℕ) < 2 then 2 * R ^ 2 else -(2 * R ^ 2)

private theorem reluApproxMulSquareInput_mem_unitInterval {R : ℝ} (hR : 0 < R)
    (i : Fin 4) (x : Fin 2 → ℝ)
    (hx0 : |x 0| ≤ R) (hx1 : |x 1| ≤ R) :
    reluApproxMulSquareInput R i x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases abs_le.mp hx0 with ⟨hx0l, hx0u⟩
  rcases abs_le.mp hx1 with ⟨hx1l, hx1u⟩
  have hden : 0 < 4 * R := by positivity
  have hx0dl : -(1 / 4 : ℝ) ≤ x 0 / (4 * R) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hx0du : x 0 / (4 * R) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hx1dl : -(1 / 4 : ℝ) ≤ x 1 / (4 * R) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hx1du : x 1 / (4 * R) ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hnorm0 : R⁻¹ * 4⁻¹ * x 0 = x 0 / (4 * R) := by
    field_simp
  have hnorm1 : R⁻¹ * 4⁻¹ * x 1 = x 1 / (4 * R) := by
    field_simp
  fin_cases i <;>
    simp [reluApproxMulSquareInput, reluApproxMulAffineCoeff,
      Fin.sum_univ_two] <;>
    constructor <;> rw [hnorm0, hnorm1] <;> nlinarith

private theorem reluApproxMul_polarization_identity {R : ℝ} (hR : R ≠ 0)
    (x : Fin 2 → ℝ) :
    ∑ i : Fin 4,
        reluApproxMulPolarizationCoeff R i *
          reluApproxMulSquareInput R i x ^ 2 = x 0 * x 1 := by
  simp [reluApproxMulPolarizationCoeff, reluApproxMulSquareInput,
    reluApproxMulAffineCoeff, Fin.sum_univ_four, Fin.sum_univ_two]
  field_simp
  ring

/-- Fixed-width multiplication on a bounded box, obtained from four affine
copies of the exponential square network and a serial linear-combination
register. -/
theorem exists_reluNetworkClass_mul_fixed_width_exponential_depth_rate_on_box
    (R : ℝ) (hR : 0 < R) (m : ℕ) :
    ∃ D P : ℕ,
      0 < D ∧
      D ≤ 5 * ((2 * m + 1 : ℕ) + 1) ∧
      P = fullyConnectedReLUParameterCount 2 D 10 ∧
      ∃ g : (Fin 2 → ℝ) → ℝ,
        g ∈ reluNetworkClass 2 D 10 P ∧
        ∀ x : Fin 2 → ℝ, |x 0| ≤ R → |x 1| ≤ R →
          |g x - x 0 * x 1| ≤ 8 * R ^ 2 * (1 / 4 : ℝ) ^ m := by
  let base : FullyConnectedReLUNet 1 := reluApproxSquareNet m
  let lifted : Fin 4 → FullyConnectedReLUNet 2 := fun i =>
    FullyConnectedReLUNet.precomposeScalarAffine base
      (reluApproxMulAffineCoeff R i) (1 / 2)
  let approx : Fin 4 → (Fin 2 → ℝ) → ℝ := fun i => (lifted i).realize
  let target : Fin 4 → (Fin 2 → ℝ) → ℝ := fun i x =>
    reluApproxMulSquareInput R i x ^ 2
  let eps : Fin 4 → ℝ := fun _ => (1 / 4 : ℝ) ^ m
  have heps : ∀ i : Fin 4, 0 ≤ eps i := by
    intro i
    simp [eps]
  have hclass : ∀ i : Fin 4,
      approx i ∈ reluNetworkClass 2 (2 * m + 1) 3
        (fullyConnectedReLUParameterCount 2 (2 * m + 1) 3) := by
    intro i
    rw [reluNetworkClass]
    refine ⟨lifted i, ?_, ?_, ?_, ?_, fun _ => rfl⟩
    · simp [lifted, base, FullyConnectedReLUNet.precomposeScalarAffine,
        reluApproxSquareNet]
    · simp [lifted, base, FullyConnectedReLUNet.precomposeScalarAffine,
        reluApproxSquareNet]
    · simp [lifted, base, FullyConnectedReLUNet.precomposeScalarAffine,
        reluApproxSquareNet]
    · simp [lifted, base, FullyConnectedReLUNet.precomposeScalarAffine,
        FullyConnectedReLUNet.parameterCount, reluApproxSquareNet]
  have herr : ∀ i : Fin 4, ∀ x : Fin 2 → ℝ,
      (|x 0| ≤ R ∧ |x 1| ≤ R) →
        |approx i x - target i x| ≤ eps i := by
    intro i x hx
    have hmem := reluApproxMulSquareInput_mem_unitInterval hR i x hx.1 hx.2
    have hsquare := reluApproxSquareApprox_error_le m hmem
    change
      |(lifted i).realize x - reluApproxMulSquareInput R i x ^ 2| ≤
        (1 / 4 : ℝ) ^ m
    rw [show (lifted i).realize x =
        base.realize (fun _ => reluApproxMulSquareInput R i x) by
      rw [FullyConnectedReLUNet.precomposeScalarAffine_realize]
      rfl]
    rw [show base.realize (fun _ => reluApproxMulSquareInput R i x) =
        reluApproxSquareApprox m (reluApproxMulSquareInput R i x) by
      apply reluApproxSquareNet_realize
      exact hmem]
    exact hsquare
  rcases finite_linear_combination_reluNetworkClass_serial_fixed_width_explicit_depth_bound
      (d := 2) (D0 := 2 * m + 1) (W0 := 3)
      (P0 := fullyConnectedReLUParameterCount 2 (2 * m + 1) 3)
      (domain := fun x : Fin 2 → ℝ => |x 0| ≤ R ∧ |x 1| ≤ R)
      (coeff := reluApproxMulPolarizationCoeff R)
      (target := target) (approx := approx) (eps := eps)
      (by omega) (by norm_num) heps hclass herr with
    ⟨D, P, hD, hDbound, hP, g, hgclass, hgerr⟩
  refine ⟨D, P, hD, ?_, ?_, g, ?_, ?_⟩
  · norm_num at hDbound ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hDbound
  · norm_num at hP ⊢
    exact hP
  · norm_num at hgclass ⊢
    exact hgclass
  · intro x hx0 hx1
    have hraw := hgerr x ⟨hx0, hx1⟩
    have hid := reluApproxMul_polarization_identity hR.ne' x
    change
      |g x - ∑ i : Fin 4,
          reluApproxMulPolarizationCoeff R i *
            reluApproxMulSquareInput R i x ^ 2| ≤
        ∑ i : Fin 4,
          |reluApproxMulPolarizationCoeff R i| * (1 / 4 : ℝ) ^ m at hraw
    rw [hid] at hraw
    calc
      |g x - x 0 * x 1| ≤
          ∑ i : Fin 4,
            |reluApproxMulPolarizationCoeff R i| * (1 / 4 : ℝ) ^ m := hraw
      _ = 8 * R ^ 2 * (1 / 4 : ℝ) ^ m := by
        have hnonneg : 0 ≤ 2 * R ^ 2 := by positivity
        simp [reluApproxMulPolarizationCoeff, Fin.sum_univ_four,
          abs_of_nonneg hnonneg, abs_of_nonpos (neg_nonpos.mpr hnonneg)]
        ring


/-- Running the exponential gadget for `(r + 1) * M^d` refinement steps is
already more accurate than the target shallow ReLU rate. -/
private theorem reluApprox_exponential_refinement_le_rate
    {d r M : ℕ} {beta : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (_hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) :
    (1 / 4 : ℝ) ^ ((r + 1) * M ^ d) ≤
      shallowReLUResolutionRate M r beta := by
  have hMpos : 0 < M := by omega
  have hMd_ge_M : M ≤ M ^ d := by
    cases d with
    | zero => omega
    | succ d =>
        rw [pow_succ]
        exact Nat.le_mul_of_pos_left M (pow_pos hMpos d)
  have hM2_le_4M_nat : M ^ 2 ≤ 4 ^ M := by
    calc
      M ^ 2 ≤ 2 * M ^ 2 + 1 := by omega
      _ ≤ 2 ^ (2 * M) := Nat.two_mul_sq_add_one_le_two_pow_two_mul M
      _ = 4 ^ M := by
        rw [pow_mul]
        norm_num
  have hM2_le_4M : (M : ℝ) ^ 2 ≤ (4 : ℝ) ^ M := by
    exact_mod_cast hM2_le_4M_nat
  have hInvPow : (1 / 4 : ℝ) ^ M ≤ ((M : ℝ)⁻¹) ^ 2 := by
    have h := (inv_le_inv₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ M)
      (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)).mpr hM2_le_4M
    simpa [one_div, inv_pow] using h
  have hQuarter_nonneg : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hQuarter_le_one : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hMd : (1 / 4 : ℝ) ^ (M ^ d) ≤ (1 / 4 : ℝ) ^ M :=
    pow_le_pow_of_le_one hQuarter_nonneg hQuarter_le_one hMd_ge_M
  have hBlock : (1 / 4 : ℝ) ^ (M ^ d) ≤ ((M : ℝ)⁻¹) ^ 2 :=
    le_trans hMd hInvPow
  have hPow :
      ((1 / 4 : ℝ) ^ (M ^ d)) ^ (r + 1) ≤
        (((M : ℝ)⁻¹) ^ 2) ^ (r + 1) := by
    exact pow_le_pow_left₀ (pow_nonneg hQuarter_nonneg (M ^ d)) hBlock (r + 1)
  have hInvPos : (0 : ℝ) < (M : ℝ)⁻¹ := by positivity
  have hInvLeOne : (M : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < (M : ℝ))).mpr
      (by exact_mod_cast (show 1 ≤ M by omega))
  have hExp : 2 * ((r : ℝ) + beta) ≤ (2 * (r + 1) : ℕ) := by
    push_cast
    nlinarith
  calc
    (1 / 4 : ℝ) ^ ((r + 1) * M ^ d) =
        ((1 / 4 : ℝ) ^ (M ^ d)) ^ (r + 1) := by
      rw [Nat.mul_comm, pow_mul]
    _ ≤ (((M : ℝ)⁻¹) ^ 2) ^ (r + 1) := hPow
    _ = ((M : ℝ)⁻¹) ^ (2 * (r + 1)) := by rw [pow_mul]
    _ = ((M : ℝ)⁻¹).rpow ((2 * (r + 1) : ℕ) : ℝ) := by
      exact (Real.rpow_natCast ((M : ℝ)⁻¹) (2 * (r + 1))).symm
    _ ≤ ((M : ℝ)⁻¹).rpow (2 * ((r : ℝ) + beta)) := by
      exact Real.rpow_le_rpow_of_exponent_ge hInvPos hInvLeOne hExp
    _ = shallowReLUResolutionRate M r beta := by
      dsimp [shallowReLUResolutionRate]
      rw [Real.rpow_neg_eq_inv_rpow]

/-- The residual exponential accuracy of the square gadget dominates the
quadratic accuracy profile expected by the generic multiplication API. -/
private theorem reluApprox_quarter_pow_le_nat_rpow_neg_two
    (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ^ n ≤ (n : ℝ).rpow (-2 : ℝ) := by
  have hn_sq_le : n ^ 2 ≤ 4 ^ n := by
    calc
      n ^ 2 ≤ 2 * n ^ 2 + 1 := by omega
      _ ≤ 2 ^ (2 * n) := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
      _ = 4 ^ n := by
        rw [pow_mul]
        norm_num
  have hn_sq_le_real : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    exact_mod_cast hn_sq_le
  have hinv : ((4 : ℝ) ^ n)⁻¹ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hn_sq_le_real
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (1 / 4 : ℝ) ^ n = ((4 : ℝ) ^ n)⁻¹ := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
    _ ≤ ((n : ℝ) ^ 2)⁻¹ := hinv
    _ = (n : ℝ).rpow (-2 : ℝ) := by
      simp [Real.rpow_neg (le_of_lt hn_real), Real.rpow_natCast, one_div]

/-- For fixed mesh parameter `M`, run the exponential multiplier for the
paper-scale refinement plus the requested generic resolution.  This presents
the concrete gadget in the `n^{-2}` family interface used by the reusable
monomial and finite-polynomial compilers, while retaining an `O(M^d)` depth
constant and a paper-rate error constant. -/
theorem exists_reluNetworkClass_mul_fixed_width_rate_scaled_family
    {d r M : ℕ} {beta : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) :
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    let cMulErr : ℝ := 8 * shallowReLUResolutionRate M r beta
    0 < cMulDepth ∧ 0 < cMulErr ∧
      ∀ n : ℕ, 0 < n →
      ∀ R : ℝ, 0 < R →
        ∃ Dmul Pmul : ℕ,
          0 < Dmul ∧
          (Dmul : ℝ) ≤ cMulDepth * (n : ℝ) ∧
          Pmul = fullyConnectedReLUParameterCount 2 Dmul 10 ∧
          ∃ gmul : (Fin 2 → ℝ) → ℝ,
            gmul ∈ reluNetworkClass 2 Dmul 10 Pmul ∧
              ∀ y : Fin 2 → ℝ,
                |y 0| ≤ R → |y 1| ≤ R →
                  |gmul y - y 0 * y 1| ≤
                    cMulErr * R ^ 2 * (n : ℝ).rpow (-2 : ℝ) := by
  dsimp only
  have hMpos : 0 < M := by omega
  have hrate_pos : 0 < shallowReLUResolutionRate M r beta := by
    unfold shallowReLUResolutionRate
    exact Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _
  refine ⟨by positivity, by positivity, ?_⟩
  intro n hn R hR
  let m0 : ℕ := (r + 1) * M ^ d
  rcases exists_reluNetworkClass_mul_fixed_width_exponential_depth_rate_on_box
      R hR (m0 + n) with
    ⟨D, P, hDpos, hDbound, hP, g, hgclass, hgerr⟩
  have hm0_le : m0 ≤ m0 * n := Nat.le_mul_of_pos_right m0 hn
  have hn1_le : n + 1 ≤ 2 * n := by omega
  have hsteps : m0 + n + 1 ≤ (m0 + 2) * n := by
    calc
      m0 + n + 1 = m0 + (n + 1) := by omega
      _ ≤ m0 * n + 2 * n := Nat.add_le_add hm0_le hn1_le
      _ = (m0 + 2) * n := by ring
  have hdepth_nat : D ≤ (10 * (m0 + 2)) * n := by
    calc
      D ≤ 5 * ((2 * (m0 + n) + 1 : ℕ) + 1) := hDbound
      _ = 10 * (m0 + n + 1) := by ring
      _ ≤ 10 * ((m0 + 2) * n) := Nat.mul_le_mul_left 10 hsteps
      _ = (10 * (m0 + 2)) * n := by ring
  have hrate := reluApprox_exponential_refinement_le_rate
    (d := d) (r := r) (M := M) (beta := beta)
    hd hM hbeta_pos hbeta_le_one
  have hnrate := reluApprox_quarter_pow_le_nat_rpow_neg_two n hn
  have hrate_nonneg : 0 ≤ shallowReLUResolutionRate M r beta := le_of_lt hrate_pos
  have hproduct :
      (1 / 4 : ℝ) ^ m0 * (1 / 4 : ℝ) ^ n ≤
        shallowReLUResolutionRate M r beta * (n : ℝ).rpow (-2 : ℝ) := by
    exact mul_le_mul hrate hnrate (by positivity) hrate_nonneg
  refine ⟨D, P, hDpos, ?_, hP, g, hgclass, ?_⟩
  · exact_mod_cast hdepth_nat
  · intro y hy0 hy1
    calc
      |g y - y 0 * y 1| ≤ 8 * R ^ 2 * (1 / 4 : ℝ) ^ (m0 + n) :=
        hgerr y hy0 hy1
      _ = 8 * R ^ 2 * ((1 / 4 : ℝ) ^ m0 * (1 / 4 : ℝ) ^ n) := by
        rw [pow_add]
      _ ≤ 8 * R ^ 2 *
          (shallowReLUResolutionRate M r beta * (n : ℝ).rpow (-2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = (8 * shallowReLUResolutionRate M r beta) * R ^ 2 *
          (n : ℝ).rpow (-2 : ℝ) := by ring

/-- At unit generic resolution, a fixed-degree monomial compiler propagates a
small multiplication error only linearly.  The majorant may depend on the
input radius and degree, but not on the multiplication error itself. -/
theorem exists_centeredMonomialFixedWidthApproxError_linear_mul_error_bound
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ 8 →
        centeredMonomialFixedWidthApproxError e R 1 k ≤ K * e := by
  have hnonneg : ∀ k : ℕ, ∀ e : ℝ, 0 ≤ e →
      0 ≤ centeredMonomialFixedWidthApproxError e R 1 k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro e he
        simp [centeredMonomialFixedWidthApproxError]
    | one =>
        intro e he
        simp [centeredMonomialFixedWidthApproxError]
    | more k _ih0 ih1 =>
        intro e he
        have hp := ih1 e he
        simp only [centeredMonomialFixedWidthApproxError]
        have hB : 0 ≤ R ^ (k + 1) +
            centeredMonomialFixedWidthApproxError e R 1 (k + 1) + R + 1 := by
          positivity
        norm_num only [Nat.cast_one]
        have hone : Real.rpow (1 : ℝ) (-2 : ℝ) = 1 := by
          norm_num [Real.rpow_def_of_pos]
        rw [hone, mul_one]
        positivity
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro e he he1
      simp [centeredMonomialFixedWidthApproxError]
  | one =>
      refine ⟨0, le_rfl, ?_⟩
      intro e he he1
      simp [centeredMonomialFixedWidthApproxError]
  | more k _ih0 ih1 =>
      rcases ih1 with ⟨K, hK, hbound⟩
      let B0 : ℝ := R ^ (k + 1) + 8 * K + R + 1
      let K' : ℝ := B0 ^ 2 + B0 * K
      have hB0 : 0 ≤ B0 := by
        dsimp [B0]
        positivity
      have hK' : 0 ≤ K' := by
        dsimp [K']
        positivity
      refine ⟨K', hK', ?_⟩
      intro e he he1
      let E : ℝ := centeredMonomialFixedWidthApproxError e R 1 (k + 1)
      let B : ℝ := R ^ (k + 1) + E + R + 1
      have hE : 0 ≤ E := hnonneg (k + 1) e he
      have hE_le : E ≤ K * e := hbound e he he1
      have hKe_le : K * e ≤ 8 * K := by
        nlinarith [mul_le_mul_of_nonneg_left he1 hK]
      have hB : 0 ≤ B := by
        dsimp [B, E]
        positivity
      have hB_le : B ≤ B0 := by
        dsimp [B, B0, E]
        linarith
      have hBsq : B ^ 2 ≤ B0 ^ 2 := by
        nlinarith [mul_le_mul hB_le hB_le hB hB0]
      have hfirst : e * B ^ 2 ≤ e * B0 ^ 2 :=
        mul_le_mul_of_nonneg_left hBsq he
      have hsecond : B * E ≤ B0 * (K * e) :=
        mul_le_mul hB_le hE_le hE hB0
      simp only [centeredMonomialFixedWidthApproxError]
      norm_num only [Nat.cast_one]
      have hone : Real.rpow (1 : ℝ) (-2 : ℝ) = 1 := by
        norm_num [Real.rpow_def_of_pos]
      rw [hone, mul_one]
      change e * B ^ 2 + B * E ≤ K' * e
      dsimp [K']
      nlinarith [hfirst, hsecond]

/-- A finite family of fixed-degree monomials inherits the linear propagation
bound, uniformly over a common multiplication error. -/
theorem exists_finiteCenteredMonomialPolynomialFixedWidthApproxError_linear_mul_error_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ) (hR : 0 ≤ R) (degree : ι → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ 8 →
        finiteCenteredMonomialPolynomialFixedWidthApproxError e R 1
            (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) degree ≤ K * e := by
  choose K hK hbound using
    fun i : ι => exists_centeredMonomialFixedWidthApproxError_linear_mul_error_bound
      R hR (degree i)
  refine ⟨∑ i : ι, K i, Finset.sum_nonneg (fun i _ => hK i), ?_⟩
  intro e he he1
  unfold finiteCenteredMonomialPolynomialFixedWidthApproxError
  calc
    (Finset.univ : Finset ι).sum
        (fun i => |(1 : ℝ)| * centeredMonomialFixedWidthApproxError e R 1 (degree i)) =
        ∑ i : ι, centeredMonomialFixedWidthApproxError e R 1 (degree i) := by simp
    _ ≤ ∑ i : ι, K i * e :=
      Finset.sum_le_sum (fun i _ => hbound i e he he1)
    _ = (∑ i : ι, K i) * e := by rw [Finset.sum_mul]

/-- The exponential multiplication gadget, scheduled at the two-scale
shallow ReLU mesh size.  Its width is fixed, its depth is `O(M^d)`, and its
error is already at the target `M^(-2(r + beta))` scale. -/
theorem exists_reluNetworkClass_mul_fixed_width_rate_on_box
    {d r M : ℕ} {beta R : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) (hR : 0 < R) :
    ∃ D P : ℕ,
      0 < D ∧
      D ≤ 10 * (r + 2) * M ^ d ∧
      P = fullyConnectedReLUParameterCount 2 D 10 ∧
      ∃ g : (Fin 2 → ℝ) → ℝ,
        g ∈ reluNetworkClass 2 D 10 P ∧
        ∀ x : Fin 2 → ℝ, |x 0| ≤ R → |x 1| ≤ R →
          |g x - x 0 * x 1| ≤
            8 * R ^ 2 * shallowReLUResolutionRate M r beta := by
  rcases exists_reluNetworkClass_mul_fixed_width_exponential_depth_rate_on_box
      R hR ((r + 1) * M ^ d) with
    ⟨D, P, hD, hDbound, hP, g, hgclass, hgerr⟩
  have hMpos : 0 < M := by omega
  have hMd_pos : 0 < M ^ d := pow_pos hMpos d
  have hsteps : (r + 1) * M ^ d + 1 ≤ (r + 2) * M ^ d := by
    nlinarith
  have hrate := reluApprox_exponential_refinement_le_rate
    (d := d) (r := r) (M := M) (beta := beta)
    hd hM hbeta_pos hbeta_le_one
  refine ⟨D, P, hD, ?_, hP, g, hgclass, ?_⟩
  · calc
      D ≤ 5 * ((2 * ((r + 1) * M ^ d) + 1 : ℕ) + 1) := hDbound
      _ = 10 * ((r + 1) * M ^ d + 1) := by ring
      _ ≤ 10 * ((r + 2) * M ^ d) := Nat.mul_le_mul_left 10 hsteps
      _ = 10 * (r + 2) * M ^ d := by ring
  · intro x hx0 hx1
    calc
      |g x - x 0 * x 1| ≤
          8 * R ^ 2 * (1 / 4 : ℝ) ^ ((r + 1) * M ^ d) :=
        hgerr x hx0 hx1
      _ ≤ 8 * R ^ 2 * shallowReLUResolutionRate M r beta := by
        exact mul_le_mul_of_nonneg_left hrate (by positivity)


/-! ## Signed-register affine compiler

The paper's two-pass construction carries signed real registers through ReLU
layers.  A register value `u j` is represented by the pair
`(relu (u j), relu (-u j))`; subtracting the two channels recovers `u j`
exactly.  The following concrete layers compile arbitrary finite-dimensional
affine updates into that representation.
-/

/-- Positive/negative ReLU encoding of a finite real register vector. -/
private noncomputable def reluApproxSignedEncode {s : ℕ} (u : Fin s → ℝ) :
    Fin (s + s) → ℝ :=
  Fin.addCases (fun j : Fin s ↦ relu (u j)) (fun j : Fin s ↦ relu (-u j))

@[simp] theorem reluApproxSignedEncode_castAdd {s : ℕ} (u : Fin s → ℝ)
    (j : Fin s) :
    reluApproxSignedEncode u (Fin.castAdd s j) = relu (u j) := by
  simp [reluApproxSignedEncode]

@[simp] theorem reluApproxSignedEncode_natAdd {s : ℕ} (u : Fin s → ℝ)
    (j : Fin s) :
    reluApproxSignedEncode u (Fin.natAdd s j) = relu (-u j) := by
  exact Fin.addCases_right j

/-- Decoding a positive/negative register pair is exact. -/
theorem reluApproxSignedEncode_sub (z : ℝ) : relu z - relu (-z) = z := by
  by_cases hz : 0 ≤ z
  · simp [relu, hz, neg_nonpos.mpr hz]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    have hnz : 0 ≤ -z := neg_nonneg.mpr hz'
    simp [relu, hz', hnz]

/-- A linear functional applied to signed register channels decodes to the
same linear functional of the underlying real registers. -/
private theorem reluApprox_sum_signedEncode {s : ℕ}
    (c u : Fin s → ℝ) :
    (∑ j : Fin (s + s),
        Fin.addCases (fun k : Fin s ↦ c k) (fun k : Fin s ↦ -c k) j *
          reluApproxSignedEncode u j) =
      ∑ j : Fin s, c j * u j := by
  rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Fin.addCases_left, Fin.addCases_right,
    reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd]
  calc
    c j * relu (u j) + -c j * relu (-u j) =
        c j * (relu (u j) - relu (-u j)) := by ring
    _ = c j * u j := by rw [reluApproxSignedEncode_sub]

/-- A finite affine map, written in the same row-major convention as
`DenseLayer`. -/
noncomputable def reluApproxFiniteAffineMap {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) : Fin n → ℝ :=
  fun i ↦ (∑ j : Fin m, A i j * x j) + b i

/-- Precompose a fully connected ReLU network with a finite-dimensional affine
map.  Only the input layer changes; depth, width, and all later layers are
preserved. -/
noncomputable def FullyConnectedReLUNet.precomposeAffine {m n : ℕ}
    (N : FullyConnectedReLUNet n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    FullyConnectedReLUNet m where
  depth := N.depth
  width := N.width
  input :=
    { weight := fun o j ↦ ∑ q : Fin n, N.input.weight o q * A q j
      bias := fun o ↦ (∑ q : Fin n, N.input.weight o q * b q) + N.input.bias o }
  hidden := N.hidden
  outputWeight := N.outputWeight
  outputBias := N.outputBias

theorem FullyConnectedReLUNet.precomposeAffine_input_reluApply {m n : ℕ}
    (N : FullyConnectedReLUNet n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) :
    (FullyConnectedReLUNet.precomposeAffine N A b).input.reluApply x =
      N.input.reluApply (reluApproxFiniteAffineMap A b x) := by
  classical
  funext o
  simp only [FullyConnectedReLUNet.precomposeAffine, DenseLayer.reluApply,
    DenseLayer.apply, reluVec, reluApproxFiniteAffineMap]
  congr 1
  calc
    (∑ j : Fin m, (∑ q : Fin n, N.input.weight o q * A q j) * x j) +
          ((∑ q : Fin n, N.input.weight o q * b q) + N.input.bias o) =
        (∑ q : Fin n, N.input.weight o q * (∑ j : Fin m, A q j * x j)) +
          ((∑ q : Fin n, N.input.weight o q * b q) + N.input.bias o) := by
            congr 1
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _hq
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
    _ = ∑ q : Fin n, N.input.weight o q *
          ((∑ j : Fin m, A q j * x j) + b q) + N.input.bias o := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
            ring

theorem FullyConnectedReLUNet.precomposeAffine_hiddenState {m n : ℕ}
    (N : FullyConnectedReLUNet n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ)
    (t : ℕ) :
    (FullyConnectedReLUNet.precomposeAffine N A b).hiddenState x t =
      N.hiddenState (reluApproxFiniteAffineMap A b x) t := by
  induction t with
  | zero =>
      simpa [FullyConnectedReLUNet.hiddenState] using
        FullyConnectedReLUNet.precomposeAffine_input_reluApply N A b x
  | succ t ih =>
      simp only [FullyConnectedReLUNet.hiddenState]
      by_cases ht : t < N.depth - 1
      · simp [FullyConnectedReLUNet.precomposeAffine, ht]
        exact congrArg (N.hidden ⟨t, ht⟩).reluApply ih
      · simp [FullyConnectedReLUNet.precomposeAffine, ht]
        simpa [FullyConnectedReLUNet.precomposeAffine] using ih

theorem FullyConnectedReLUNet.precomposeAffine_realize {m n : ℕ}
    (N : FullyConnectedReLUNet n)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (x : Fin m → ℝ) :
    (FullyConnectedReLUNet.precomposeAffine N A b).realize x =
      N.realize (reluApproxFiniteAffineMap A b x) := by
  have hs := FullyConnectedReLUNet.precomposeAffine_hiddenState
    N A b x (N.depth - 1)
  change
    (∑ j, N.outputWeight j *
        (FullyConnectedReLUNet.precomposeAffine N A b).hiddenState x
          (N.depth - 1) j) + N.outputBias =
      (∑ j, N.outputWeight j *
        N.hiddenState (reluApproxFiniteAffineMap A b x)
          (N.depth - 1) j) + N.outputBias
  rw [hs]

/-- Input layer which writes an affine function of the input into signed
register channels. -/
private noncomputable def reluApproxSignedAffineInputLayer {d s : ℕ}
    (A : Matrix (Fin s) (Fin d) ℝ) (b : Fin s → ℝ) :
    DenseLayer d (s + s) where
  weight := Fin.addCases (fun j : Fin s ↦ A j) (fun j : Fin s ↦ -A j)
  bias := Fin.addCases (fun j : Fin s ↦ b j) (fun j : Fin s ↦ -b j)

@[simp] theorem reluApproxSignedAffineInputLayer_weight_natAdd {d s : ℕ}
    (A : Matrix (Fin s) (Fin d) ℝ) (b : Fin s → ℝ) (i : Fin s) (j : Fin d) :
    (reluApproxSignedAffineInputLayer A b).weight (Fin.natAdd s i) j = -A i j := by
  change Fin.addCases (fun k : Fin s ↦ A k) (fun k : Fin s ↦ -A k)
      (Fin.natAdd s i) j = -A i j
  rw [Fin.addCases_right]
  rfl

@[simp] theorem reluApproxSignedAffineInputLayer_bias_natAdd {d s : ℕ}
    (A : Matrix (Fin s) (Fin d) ℝ) (b : Fin s → ℝ) (i : Fin s) :
    (reluApproxSignedAffineInputLayer A b).bias (Fin.natAdd s i) = -b i := by
  change Fin.addCases (fun k : Fin s ↦ b k) (fun k : Fin s ↦ -b k)
      (Fin.natAdd s i) = -b i
  exact Fin.addCases_right i

private theorem reluApproxSignedAffineInputLayer_reluApply {d s : ℕ}
    (A : Matrix (Fin s) (Fin d) ℝ) (b : Fin s → ℝ) (x : Fin d → ℝ) :
    (reluApproxSignedAffineInputLayer A b).reluApply x =
      reluApproxSignedEncode (reluApproxFiniteAffineMap A b x) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [reluApproxSignedAffineInputLayer, reluApproxSignedEncode,
      reluApproxFiniteAffineMap, DenseLayer.reluApply, DenseLayer.apply, reluVec]
  · intro j
    simp only [DenseLayer.reluApply, DenseLayer.apply, reluVec,
      reluApproxSignedAffineInputLayer_weight_natAdd,
      reluApproxSignedAffineInputLayer_bias_natAdd,
      reluApproxSignedEncode_natAdd, reluApproxFiniteAffineMap]
    change relu ((∑ k : Fin d, (-A j k) * x k) + (-b j)) =
      relu (-((∑ k : Fin d, A j k * x k) + b j))
    congr 1
    have hsum : (∑ k : Fin d, (-A j k) * x k) =
        -(∑ k : Fin d, A j k * x k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    rw [hsum]
    ring

/-- Hidden layer which applies an affine update to signed registers and writes
the result back in signed form. -/
private noncomputable def reluApproxSignedAffineTransitionLayer {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) :
    DenseLayer (s + s) (s + s) where
  weight :=
    Fin.addCases
      (fun i : Fin s ↦
        Fin.addCases (fun j : Fin s ↦ A i j) (fun j : Fin s ↦ -A i j))
      (fun i : Fin s ↦
        Fin.addCases (fun j : Fin s ↦ -A i j) (fun j : Fin s ↦ A i j))
  bias := Fin.addCases (fun i : Fin s ↦ b i) (fun i : Fin s ↦ -b i)

@[simp] theorem reluApproxSignedAffineTransitionLayer_weight_pos_pos {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i j : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).weight
        (Fin.castAdd s i) (Fin.castAdd s j) = A i j := by
  change Fin.addCases
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ A i k) (fun k : Fin s ↦ -A i k))
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ -A i k) (fun k : Fin s ↦ A i k))
      (Fin.castAdd s i) (Fin.castAdd s j) = A i j
  rw [Fin.addCases_left, Fin.addCases_left]

@[simp] theorem reluApproxSignedAffineTransitionLayer_weight_pos_neg {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i j : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).weight
        (Fin.castAdd s i) (Fin.natAdd s j) = -A i j := by
  change Fin.addCases
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ A i k) (fun k : Fin s ↦ -A i k))
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ -A i k) (fun k : Fin s ↦ A i k))
      (Fin.castAdd s i) (Fin.natAdd s j) = -A i j
  rw [Fin.addCases_left, Fin.addCases_right]

@[simp] theorem reluApproxSignedAffineTransitionLayer_weight_neg_pos {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i j : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).weight
        (Fin.natAdd s i) (Fin.castAdd s j) = -A i j := by
  change Fin.addCases
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ A i k) (fun k : Fin s ↦ -A i k))
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ -A i k) (fun k : Fin s ↦ A i k))
      (Fin.natAdd s i) (Fin.castAdd s j) = -A i j
  rw [Fin.addCases_right, Fin.addCases_left]

@[simp] theorem reluApproxSignedAffineTransitionLayer_weight_neg_neg {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i j : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).weight
        (Fin.natAdd s i) (Fin.natAdd s j) = A i j := by
  change Fin.addCases
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ A i k) (fun k : Fin s ↦ -A i k))
      (fun i : Fin s ↦
        Fin.addCases (fun k : Fin s ↦ -A i k) (fun k : Fin s ↦ A i k))
      (Fin.natAdd s i) (Fin.natAdd s j) = A i j
  rw [Fin.addCases_right, Fin.addCases_right]

@[simp] theorem reluApproxSignedAffineTransitionLayer_bias_pos {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).bias (Fin.castAdd s i) = b i := by
  change Fin.addCases (fun k : Fin s ↦ b k) (fun k : Fin s ↦ -b k)
      (Fin.castAdd s i) = b i
  exact Fin.addCases_left i

@[simp] theorem reluApproxSignedAffineTransitionLayer_bias_neg {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (i : Fin s) :
    (reluApproxSignedAffineTransitionLayer A b).bias (Fin.natAdd s i) = -b i := by
  change Fin.addCases (fun k : Fin s ↦ b k) (fun k : Fin s ↦ -b k)
      (Fin.natAdd s i) = -b i
  exact Fin.addCases_right i

private theorem reluApproxSignedAffineTransitionLayer_reluApply {s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (u : Fin s → ℝ) :
    (reluApproxSignedAffineTransitionLayer A b).reluApply
        (reluApproxSignedEncode u) =
      reluApproxSignedEncode (reluApproxFiniteAffineMap A b u) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [DenseLayer.reluApply, DenseLayer.apply, reluVec, Fin.sum_univ_add,
      reluApproxSignedAffineTransitionLayer_weight_pos_pos,
      reluApproxSignedAffineTransitionLayer_weight_pos_neg,
      reluApproxSignedAffineTransitionLayer_bias_pos,
      reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd,
      reluApproxFiniteAffineMap]
    change relu
        ((∑ k : Fin s, A j k * relu (u k)) +
          (∑ k : Fin s, (-A j k) * relu (-u k)) + b j) =
      relu ((∑ k : Fin s, A j k * u k) + b j)
    congr 1
    apply congrArg (fun z : ℝ ↦ z + b j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    calc
      A j k * relu (u k) + -A j k * relu (-u k) =
          A j k * (relu (u k) - relu (-u k)) := by ring
      _ = A j k * u k := by rw [reluApproxSignedEncode_sub]
  · intro j
    simp only [DenseLayer.reluApply, DenseLayer.apply, reluVec, Fin.sum_univ_add,
      reluApproxSignedAffineTransitionLayer_weight_neg_pos,
      reluApproxSignedAffineTransitionLayer_weight_neg_neg,
      reluApproxSignedAffineTransitionLayer_bias_neg,
      reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd,
      reluApproxFiniteAffineMap]
    change relu
        ((∑ k : Fin s, (-A j k) * relu (u k)) +
          (∑ k : Fin s, A j k * relu (-u k)) + (-b j)) =
      relu (-((∑ k : Fin s, A j k * u k) + b j))
    congr 1
    have hsum :
        (∑ k : Fin s, (-A j k) * relu (u k)) +
            (∑ k : Fin s, A j k * relu (-u k)) =
          -(∑ k : Fin s, A j k * u k) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      calc
        -A j k * relu (u k) + A j k * relu (-u k) =
            -(A j k * (relu (u k) - relu (-u k))) := by ring
        _ = -(A j k * u k) := by rw [reluApproxSignedEncode_sub]
    rw [hsum]
    ring

/-- State generated by a finite sequence of affine register updates.  The
definition is saturated after the last scheduled update, matching
`FullyConnectedReLUNet.hiddenState`. -/
private noncomputable def reluApproxAffineRegisterRecursion {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) : ℕ → Fin s → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxFiniteAffineMap (A ⟨t, ht⟩) (b ⟨t, ht⟩)
          (reluApproxAffineRegisterRecursion A0 b0 A b x t)
      else
        reluApproxAffineRegisterRecursion A0 b0 A b x t

/-- Concrete fully connected ReLU network compiling a finite affine register
recursion.  Its width is twice the number of signed registers and its hidden
depth is exactly one plus the number of updates. -/
private noncomputable def reluApproxSignedAffineRecursionNet {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    FullyConnectedReLUNet d where
  depth := T + 1
  width := s + s
  input := reluApproxSignedAffineInputLayer A0 b0
  hidden := fun t =>
    reluApproxSignedAffineTransitionLayer
      (A (Fin.cast (by omega) t)) (b (Fin.cast (by omega) t))
  outputWeight :=
    Fin.addCases (fun j : Fin s ↦ outputWeight j) (fun j : Fin s ↦ -outputWeight j)
  outputBias := outputBias

private theorem reluApproxSignedAffineRecursionNet_depth {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias).depth =
      T + 1 := rfl

private theorem reluApproxSignedAffineRecursionNet_width {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias).width =
      s + s := rfl

/-- The concrete network's hidden state is exactly the signed encoding of the
scheduled affine recursion. -/
private theorem reluApproxSignedAffineRecursionNet_hiddenState {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    (reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias).hiddenState x t =
      reluApproxSignedEncode
        (reluApproxAffineRegisterRecursion A0 b0 A b x t) := by
  let N := reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias
  change N.hiddenState x t =
    reluApproxSignedEncode (reluApproxAffineRegisterRecursion A0 b0 A b x t)
  induction t with
  | zero =>
      change (reluApproxSignedAffineInputLayer A0 b0).reluApply x =
        reluApproxSignedEncode (reluApproxFiniteAffineMap A0 b0 x)
      exact reluApproxSignedAffineInputLayer_reluApply A0 b0 x
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      have hguard : t < N.depth - 1 := by
        simpa [N, reluApproxSignedAffineRecursionNet] using htlt
      rw [show N.hiddenState x (t + 1) =
          (N.hidden ⟨t, hguard⟩).reluApply (N.hiddenState x t) by
        simp [FullyConnectedReLUNet.hiddenState, hguard]]
      rw [ih (Nat.le_of_succ_le ht)]
      have hdepth : N.depth - 1 = T := by
        simp [N, reluApproxSignedAffineRecursionNet]
      have hindex : Fin.cast hdepth ⟨t, hguard⟩ =
          (⟨t, htlt⟩ : Fin T) := by
        apply Fin.ext
        rfl
      change
        (reluApproxSignedAffineTransitionLayer
            (A (Fin.cast hdepth ⟨t, hguard⟩))
            (b (Fin.cast hdepth ⟨t, hguard⟩))).reluApply
              (reluApproxSignedEncode
                (reluApproxAffineRegisterRecursion A0 b0 A b x t)) =
          reluApproxSignedEncode
            (reluApproxAffineRegisterRecursion A0 b0 A b x (t + 1))
      rw [hindex]
      rw [reluApproxSignedAffineTransitionLayer_reluApply]
      simp [reluApproxAffineRegisterRecursion, htlt]

/-- Exact readout theorem for the compiled affine register machine. -/
private theorem reluApproxSignedAffineRecursionNet_realize {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) (x : Fin d → ℝ) :
    (reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias).realize x =
      (∑ j : Fin s,
        outputWeight j * reluApproxAffineRegisterRecursion A0 b0 A b x T j) +
        outputBias := by
  let N := reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias
  have hdepth : N.depth - 1 = T := by
    simp [N, reluApproxSignedAffineRecursionNet]
  have hstate : N.hiddenState x T =
      reluApproxSignedEncode
        (reluApproxAffineRegisterRecursion A0 b0 A b x T) :=
    reluApproxSignedAffineRecursionNet_hiddenState
      A0 b0 A b outputWeight outputBias x T (Nat.le_refl T)
  change
    (∑ j : Fin (s + s),
        (Fin.addCases (fun k : Fin s ↦ outputWeight k)
            (fun k : Fin s ↦ -outputWeight k) j) *
          N.hiddenState x (N.depth - 1) j) + outputBias = _
  rw [hdepth, hstate, Fin.sum_univ_add]
  apply congrArg (fun z : ℝ ↦ z + outputBias)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Fin.addCases_left, Fin.addCases_right,
    reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd]
  calc
    outputWeight j * relu (reluApproxAffineRegisterRecursion A0 b0 A b x T j) +
        -outputWeight j * relu (-reluApproxAffineRegisterRecursion A0 b0 A b x T j) =
      outputWeight j *
        (relu (reluApproxAffineRegisterRecursion A0 b0 A b x T j) -
          relu (-reluApproxAffineRegisterRecursion A0 b0 A b x T j)) := by ring
    _ = outputWeight j * reluApproxAffineRegisterRecursion A0 b0 A b x T j := by
      rw [reluApproxSignedEncode_sub]

/-- The compiler uses the ordinary fully connected parameter count at its
exact depth and width. -/
private theorem reluApproxSignedAffineRecursionNet_parameterCount {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin s) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedAffineRecursionNet A0 b0 A b outputWeight outputBias).parameterCount =
      fullyConnectedReLUParameterCount d (T + 1) (s + s) := rfl


/-! ## Two-layer ReLU macro updates

A paper macro step has the form `u ↦ A (relu (B u + c)) + d`.  The
workspace below stores a signed register vector in its first `2s` channels and
uses the final `h` channels for the intermediate ReLU features. -/

/-- Signed state registers followed by zeroed feature workspace. -/
private noncomputable def reluApproxSignedWorkspaceEncode {s h : ℕ}
    (u : Fin s → ℝ) : Fin ((s + s) + h) → ℝ :=
  Fin.addCases (reluApproxSignedEncode u) (fun _ : Fin h ↦ 0)

/-- Zeroed state workspace followed by the ReLU feature vector. -/
private noncomputable def reluApproxFeatureWorkspace {s h : ℕ}
    (v : Fin h → ℝ) : Fin ((s + s) + h) → ℝ :=
  Fin.addCases (fun _ : Fin (s + s) ↦ 0) (fun i : Fin h ↦ relu (v i))

@[simp] theorem reluApproxSignedWorkspaceEncode_castAdd {s h : ℕ}
    (u : Fin s → ℝ) (j : Fin (s + s)) :
    reluApproxSignedWorkspaceEncode (h := h) u (Fin.castAdd h j) =
      reluApproxSignedEncode u j := by
  exact Fin.addCases_left j

@[simp] theorem reluApproxSignedWorkspaceEncode_natAdd {s h : ℕ}
    (u : Fin s → ℝ) (j : Fin h) :
    reluApproxSignedWorkspaceEncode (h := h) u (Fin.natAdd (s + s) j) = 0 := by
  exact Fin.addCases_right j

@[simp] theorem reluApproxFeatureWorkspace_castAdd {s h : ℕ}
    (v : Fin h → ℝ) (j : Fin (s + s)) :
    reluApproxFeatureWorkspace (s := s) v (Fin.castAdd h j) = 0 := by
  exact Fin.addCases_left j

@[simp] theorem reluApproxFeatureWorkspace_natAdd {s h : ℕ}
    (v : Fin h → ℝ) (j : Fin h) :
    reluApproxFeatureWorkspace (s := s) v (Fin.natAdd (s + s) j) = relu (v j) := by
  exact Fin.addCases_right j

/-- First layer of a macro update: decode signed state registers, apply an
affine map, and place its ReLU features in the workspace. -/
private noncomputable def reluApproxSignedMacroFeatureLayer {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) :
    DenseLayer ((s + s) + h) ((s + s) + h) where
  weight :=
    Fin.addCases
      (fun _ : Fin (s + s) ↦ 0)
      (fun i : Fin h ↦
        Fin.addCases
          (Fin.addCases (fun j : Fin s ↦ B i j) (fun j : Fin s ↦ -B i j))
          (fun _ : Fin h ↦ 0))
  bias := Fin.addCases (fun _ : Fin (s + s) ↦ 0) c

@[simp] theorem reluApproxSignedMacroFeatureLayer_weight_feature_pos {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) (i : Fin h) (j : Fin s) :
    (reluApproxSignedMacroFeatureLayer B c).weight
        (Fin.natAdd (s + s) i) (Fin.castAdd h (Fin.castAdd s j)) = B i j := by
  simp [reluApproxSignedMacroFeatureLayer]

@[simp] theorem reluApproxSignedMacroFeatureLayer_weight_feature_state {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (i : Fin h) (j : Fin (s + s)) :
    (reluApproxSignedMacroFeatureLayer B c).weight
        (Fin.natAdd (s + s) i) (Fin.castAdd h j) =
      Fin.addCases (fun k : Fin s ↦ B i k) (fun k : Fin s ↦ -B i k) j := by
  simp [reluApproxSignedMacroFeatureLayer]

@[simp] theorem reluApproxSignedMacroFeatureLayer_weight_feature_neg {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) (i : Fin h) (j : Fin s) :
    (reluApproxSignedMacroFeatureLayer B c).weight
        (Fin.natAdd (s + s) i) (Fin.castAdd h (Fin.natAdd s j)) = -B i j := by
  rw [reluApproxSignedMacroFeatureLayer_weight_feature_state]
  exact Fin.addCases_right j

@[simp] theorem reluApproxSignedMacroFeatureLayer_weight_feature_workspace {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) (i j : Fin h) :
    (reluApproxSignedMacroFeatureLayer B c).weight
        (Fin.natAdd (s + s) i) (Fin.natAdd (s + s) j) = 0 := by
  simp [reluApproxSignedMacroFeatureLayer]

@[simp] theorem reluApproxSignedMacroFeatureLayer_bias_feature {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) (i : Fin h) :
    (reluApproxSignedMacroFeatureLayer B c).bias (Fin.natAdd (s + s) i) = c i := by
  simp [reluApproxSignedMacroFeatureLayer]

/-- Second layer of a macro update: apply an affine map to the feature
workspace and write its result back into signed state channels. -/
private noncomputable def reluApproxSignedMacroUpdatePosRow {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (i : Fin s) :
    Fin ((s + s) + h) → ℝ :=
  Fin.addCases (fun _ : Fin (s + s) ↦ 0) (fun k : Fin h ↦ A i k)

private noncomputable def reluApproxSignedMacroUpdateNegRow {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (i : Fin s) :
    Fin ((s + s) + h) → ℝ :=
  Fin.addCases (fun _ : Fin (s + s) ↦ 0) (fun k : Fin h ↦ -A i k)

private noncomputable def reluApproxSignedMacroUpdateStateRows {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) :
    Fin (s + s) → Fin ((s + s) + h) → ℝ :=
  Fin.addCases (reluApproxSignedMacroUpdatePosRow A)
    (reluApproxSignedMacroUpdateNegRow A)

private noncomputable def reluApproxSignedMacroUpdateLayer {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) :
    DenseLayer ((s + s) + h) ((s + s) + h) where
  weight :=
    Fin.addCases (reluApproxSignedMacroUpdateStateRows A)
      (fun _ : Fin h ↦ 0)
  bias :=
    Fin.addCases
      (Fin.addCases (fun i : Fin s ↦ d i) (fun i : Fin s ↦ -d i))
      (fun _ : Fin h ↦ 0)

@[simp] theorem reluApproxSignedMacroUpdateLayer_weight_pos_state {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ)
    (i : Fin s) (j : Fin (s + s)) :
    (reluApproxSignedMacroUpdateLayer A d).weight
        (Fin.castAdd h (Fin.castAdd s i)) (Fin.castAdd h j) = 0 := by
  simp [reluApproxSignedMacroUpdateLayer, reluApproxSignedMacroUpdateStateRows,
    reluApproxSignedMacroUpdatePosRow]

@[simp] theorem reluApproxSignedMacroUpdateLayer_weight_pos_feature {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ)
    (i : Fin s) (j : Fin h) :
    (reluApproxSignedMacroUpdateLayer A d).weight
        (Fin.castAdd h (Fin.castAdd s i)) (Fin.natAdd (s + s) j) = A i j := by
  simp [reluApproxSignedMacroUpdateLayer, reluApproxSignedMacroUpdateStateRows,
    reluApproxSignedMacroUpdatePosRow]

@[simp] theorem reluApproxSignedMacroUpdateLayer_bias_pos {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) (i : Fin s) :
    (reluApproxSignedMacroUpdateLayer A d).bias
        (Fin.castAdd h (Fin.castAdd s i)) = d i := by
  simp [reluApproxSignedMacroUpdateLayer]

@[simp] theorem reluApproxSignedMacroUpdateLayer_weight_neg_state {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ)
    (i : Fin s) (j : Fin (s + s)) :
    (reluApproxSignedMacroUpdateLayer A d).weight
        (Fin.castAdd h (Fin.natAdd s i)) (Fin.castAdd h j) = 0 := by
  change (Fin.addCases (motive := fun _ : Fin ((s + s) + h) ↦
      Fin ((s + s) + h) → ℝ) (reluApproxSignedMacroUpdateStateRows A)
      (fun _ : Fin h ↦ (0 : Fin ((s + s) + h) → ℝ))
      (Fin.castAdd h (Fin.natAdd s i))) (Fin.castAdd h j) = 0
  rw [Fin.addCases_left]
  rw [show reluApproxSignedMacroUpdateStateRows A (Fin.natAdd s i) =
      reluApproxSignedMacroUpdateNegRow A i from Fin.addCases_right i]
  exact Fin.addCases_left j

@[simp] theorem reluApproxSignedMacroUpdateLayer_weight_neg_feature {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ)
    (i : Fin s) (j : Fin h) :
    (reluApproxSignedMacroUpdateLayer A d).weight
        (Fin.castAdd h (Fin.natAdd s i)) (Fin.natAdd (s + s) j) = -A i j := by
  change (Fin.addCases (motive := fun _ : Fin ((s + s) + h) ↦
      Fin ((s + s) + h) → ℝ) (reluApproxSignedMacroUpdateStateRows A)
      (fun _ : Fin h ↦ (0 : Fin ((s + s) + h) → ℝ))
      (Fin.castAdd h (Fin.natAdd s i))) (Fin.natAdd (s + s) j) = -A i j
  rw [Fin.addCases_left]
  rw [show reluApproxSignedMacroUpdateStateRows A (Fin.natAdd s i) =
      reluApproxSignedMacroUpdateNegRow A i from Fin.addCases_right i]
  exact Fin.addCases_right j

@[simp] theorem reluApproxSignedMacroUpdateLayer_bias_neg {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) (i : Fin s) :
    (reluApproxSignedMacroUpdateLayer A d).bias
        (Fin.castAdd h (Fin.natAdd s i)) = -d i := by
  change
    Fin.addCases
      (Fin.addCases (fun k : Fin s ↦ d k) (fun k : Fin s ↦ -d k))
      (fun _ : Fin h ↦ (0 : ℝ))
      (Fin.castAdd h (Fin.natAdd s i)) = -d i
  rw [Fin.addCases_left]
  exact Fin.addCases_right i

@[simp] theorem reluApproxSignedMacroUpdateLayer_workspace_row {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ)
    (i : Fin h) (j : Fin ((s + s) + h)) :
    (reluApproxSignedMacroUpdateLayer A d).weight
        (Fin.natAdd (s + s) i) j = 0 := by
  simp [reluApproxSignedMacroUpdateLayer]

@[simp] theorem reluApproxSignedMacroUpdateLayer_workspace_bias {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) (i : Fin h) :
    (reluApproxSignedMacroUpdateLayer A d).bias
        (Fin.natAdd (s + s) i) = 0 := by
  simp [reluApproxSignedMacroUpdateLayer]

private theorem reluApproxSignedMacroFeatureLayer_reluApply {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ) (u : Fin s → ℝ) :
    (reluApproxSignedMacroFeatureLayer B c).reluApply
        (reluApproxSignedWorkspaceEncode (h := h) u) =
      reluApproxFeatureWorkspace
        (reluApproxFiniteAffineMap B c u) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [reluApproxSignedMacroFeatureLayer, reluApproxSignedWorkspaceEncode,
      reluApproxFeatureWorkspace, DenseLayer.reluApply, DenseLayer.apply, reluVec, relu]
  · intro j
    rw [reluApproxFeatureWorkspace_natAdd]
    change relu
        ((∑ k : Fin ((s + s) + h),
            (reluApproxSignedMacroFeatureLayer B c).weight
                (Fin.natAdd (s + s) j) k *
              reluApproxSignedWorkspaceEncode (h := h) u k) +
          (reluApproxSignedMacroFeatureLayer B c).bias
            (Fin.natAdd (s + s) j)) =
      relu ((∑ k : Fin s, B j k * u k) + c j)
    rw [Fin.sum_univ_add]
    simp only [reluApproxSignedMacroFeatureLayer_weight_feature_state,
      reluApproxSignedMacroFeatureLayer_weight_feature_workspace,
      reluApproxSignedMacroFeatureLayer_bias_feature,
      reluApproxSignedWorkspaceEncode_castAdd,
      reluApproxSignedWorkspaceEncode_natAdd, mul_zero, Finset.sum_const_zero, add_zero]
    rw [reluApprox_sum_signedEncode]

private theorem reluApproxSignedMacroUpdateLayer_reluApply {s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) (v : Fin h → ℝ) :
    (reluApproxSignedMacroUpdateLayer A d).reluApply
        (reluApproxFeatureWorkspace (s := s) v) =
      reluApproxSignedWorkspaceEncode (h := h)
        (reluApproxFiniteAffineMap A d (fun i ↦ relu (v i))) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      rw [reluApproxSignedWorkspaceEncode_castAdd,
        reluApproxSignedEncode_castAdd]
      change relu
          ((∑ j : Fin ((s + s) + h),
              (reluApproxSignedMacroUpdateLayer A d).weight
                  (Fin.castAdd h (Fin.castAdd s k)) j *
                reluApproxFeatureWorkspace (s := s) v j) +
            (reluApproxSignedMacroUpdateLayer A d).bias
              (Fin.castAdd h (Fin.castAdd s k))) =
        relu ((∑ j : Fin h, A k j * relu (v j)) + d k)
      rw [Fin.sum_univ_add]
      simp
    · intro k
      rw [reluApproxSignedWorkspaceEncode_castAdd,
        reluApproxSignedEncode_natAdd]
      change relu
          ((∑ j : Fin ((s + s) + h),
              (reluApproxSignedMacroUpdateLayer A d).weight
                  (Fin.castAdd h (Fin.natAdd s k)) j *
                reluApproxFeatureWorkspace (s := s) v j) +
            (reluApproxSignedMacroUpdateLayer A d).bias
              (Fin.castAdd h (Fin.natAdd s k))) =
        relu (-((∑ j : Fin h, A k j * relu (v j)) + d k))
      rw [Fin.sum_univ_add]
      simp only [reluApproxSignedMacroUpdateLayer_weight_neg_state,
        reluApproxSignedMacroUpdateLayer_weight_neg_feature,
        reluApproxSignedMacroUpdateLayer_bias_neg,
        reluApproxFeatureWorkspace_castAdd, reluApproxFeatureWorkspace_natAdd,
        mul_zero, Finset.sum_const_zero, zero_add]
      congr 1
      have hsum : (∑ j : Fin h, (-A k j) * relu (v j)) =
          -(∑ j : Fin h, A k j * relu (v j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [hsum]
      ring
  · intro j
    rw [reluApproxSignedWorkspaceEncode_natAdd]
    change relu
        ((∑ k : Fin ((s + s) + h),
            (reluApproxSignedMacroUpdateLayer A d).weight
                (Fin.natAdd (s + s) j) k *
              reluApproxFeatureWorkspace (s := s) v k) +
          (reluApproxSignedMacroUpdateLayer A d).bias
            (Fin.natAdd (s + s) j)) = 0
    simp [relu]

/-- Exact two-layer compilation law for one nonlinear macro update. -/
private theorem reluApproxSignedMacroStep_exact {s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (A : Matrix (Fin s) (Fin h) ℝ) (d : Fin s → ℝ) (u : Fin s → ℝ) :
    (reluApproxSignedMacroUpdateLayer A d).reluApply
        ((reluApproxSignedMacroFeatureLayer B c).reluApply
          (reluApproxSignedWorkspaceEncode (h := h) u)) =
      reluApproxSignedWorkspaceEncode (h := h)
        (reluApproxFiniteAffineMap A d
          (fun i ↦ relu (reluApproxFiniteAffineMap B c u i))) := by
  rw [reluApproxSignedMacroFeatureLayer_reluApply]
  exact reluApproxSignedMacroUpdateLayer_reluApply A d
    (reluApproxFiniteAffineMap B c u)

/-- Input layer for a macro-recursion network: initialize the signed state
registers by an affine map of the external input and clear the feature
workspace. -/
private noncomputable def reluApproxSignedMacroInputLayer {d s h : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ) :
    DenseLayer d ((s + s) + h) where
  weight :=
    Fin.addCases (reluApproxSignedAffineInputLayer A0 b0).weight
      (fun _ : Fin h ↦ 0)
  bias :=
    Fin.addCases (reluApproxSignedAffineInputLayer A0 b0).bias
      (fun _ : Fin h ↦ 0)

private theorem reluApproxSignedMacroInputLayer_reluApply {d s h : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ) (x : Fin d → ℝ) :
    (reluApproxSignedMacroInputLayer (h := h) A0 b0).reluApply x =
      reluApproxSignedWorkspaceEncode (h := h)
        (reluApproxFiniteAffineMap A0 b0 x) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [reluApproxSignedWorkspaceEncode_castAdd]
    have hinput := congrFun (reluApproxSignedAffineInputLayer_reluApply A0 b0 x) j
    simpa [reluApproxSignedMacroInputLayer, DenseLayer.reluApply, DenseLayer.apply,
      reluVec] using hinput
  · intro j
    rw [reluApproxSignedWorkspaceEncode_natAdd]
    simp [reluApproxSignedMacroInputLayer, DenseLayer.reluApply, DenseLayer.apply,
      reluVec, relu]

/-- State recursion generated by a sequence of two-layer ReLU macro updates. -/
noncomputable def reluApproxSignedMacroRecursion {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) : ℕ → Fin s → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxFiniteAffineMap (A ⟨t, ht⟩) (b ⟨t, ht⟩)
          (fun i ↦ relu (reluApproxFiniteAffineMap (B ⟨t, ht⟩) (c ⟨t, ht⟩)
            (reluApproxSignedMacroRecursion A0 b0 B c A b x t) i))
      else
        reluApproxSignedMacroRecursion A0 b0 B c A b x t

/-- Fully connected ReLU network obtained by alternating the feature and
update layer of every scheduled macro step. -/
private noncomputable def reluApproxSignedMacroRecursionNet {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    FullyConnectedReLUNet d where
  depth := 2 * T + 1
  width := (s + s) + h
  input := reluApproxSignedMacroInputLayer A0 b0
  hidden := fun l =>
    if _heven : l.val % 2 = 0 then
      reluApproxSignedMacroFeatureLayer
        (B ⟨l.val / 2, by omega⟩) (c ⟨l.val / 2, by omega⟩)
    else
      reluApproxSignedMacroUpdateLayer
        (A ⟨l.val / 2, by omega⟩) (b ⟨l.val / 2, by omega⟩)
  outputWeight :=
    Fin.addCases
      (Fin.addCases (fun i : Fin s ↦ outputWeight i) (fun i : Fin s ↦ -outputWeight i))
      (fun _ : Fin h ↦ 0)
  outputBias := outputBias

private theorem reluApproxSignedMacroRecursionNet_depth {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias).depth =
      2 * T + 1 := rfl

private theorem reluApproxSignedMacroRecursionNet_width {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias).width =
      (s + s) + h := rfl

/-- After `k` complete macro steps, the even hidden state is exactly the
signed encoding of the mathematical macro recursion. -/
private theorem reluApproxSignedMacroRecursionNet_hiddenState_even {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ) (k : ℕ) (hk : k ≤ T) :
    (reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias).hiddenState
        x (2 * k) =
      reluApproxSignedWorkspaceEncode (h := h)
        (reluApproxSignedMacroRecursion A0 b0 B c A b x k) := by
  let N := reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias
  change N.hiddenState x (2 * k) = _
  induction k with
  | zero =>
      change (reluApproxSignedMacroInputLayer A0 b0).reluApply x =
        reluApproxSignedWorkspaceEncode (h := h)
          (reluApproxFiniteAffineMap A0 b0 x)
      exact reluApproxSignedMacroInputLayer_reluApply A0 b0 x
  | succ k ih =>
      have hklt : k < T := Nat.lt_of_succ_le hk
      have hguard0 : 2 * k < N.depth - 1 := by
        simp [N, reluApproxSignedMacroRecursionNet]
        omega
      have hguard1 : 2 * k + 1 < N.depth - 1 := by
        simp [N, reluApproxSignedMacroRecursionNet]
        omega
      have hlayer0 : N.hidden ⟨2 * k, hguard0⟩ =
          reluApproxSignedMacroFeatureLayer (B ⟨k, hklt⟩) (c ⟨k, hklt⟩) := by
        simp [N, reluApproxSignedMacroRecursionNet]
      have hdiv : (2 * k + 1) / 2 = k := by omega
      have hlayer1 : N.hidden ⟨2 * k + 1, hguard1⟩ =
          reluApproxSignedMacroUpdateLayer (A ⟨k, hklt⟩) (b ⟨k, hklt⟩) := by
        simp [N, reluApproxSignedMacroRecursionNet, hdiv]
      have hfeature : N.hiddenState x (2 * k + 1) =
          reluApproxFeatureWorkspace
            (reluApproxFiniteAffineMap (B ⟨k, hklt⟩) (c ⟨k, hklt⟩)
              (reluApproxSignedMacroRecursion A0 b0 B c A b x k)) := by
        calc
          N.hiddenState x (2 * k + 1) =
              (N.hidden ⟨2 * k, hguard0⟩).reluApply
                (N.hiddenState x (2 * k)) := by
            simp [FullyConnectedReLUNet.hiddenState, hguard0]
          _ = (reluApproxSignedMacroFeatureLayer
                (B ⟨k, hklt⟩) (c ⟨k, hklt⟩)).reluApply
              (reluApproxSignedWorkspaceEncode (h := h)
                (reluApproxSignedMacroRecursion A0 b0 B c A b x k)) := by
            rw [hlayer0, ih (Nat.le_of_succ_le hk)]
          _ = _ := reluApproxSignedMacroFeatureLayer_reluApply
            (B ⟨k, hklt⟩) (c ⟨k, hklt⟩)
              (reluApproxSignedMacroRecursion A0 b0 B c A b x k)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega]
      calc
        N.hiddenState x (2 * k + 2) =
            (N.hidden ⟨2 * k + 1, hguard1⟩).reluApply
              (N.hiddenState x (2 * k + 1)) := by
          simp [FullyConnectedReLUNet.hiddenState, hguard0, hguard1]
        _ = (reluApproxSignedMacroUpdateLayer
              (A ⟨k, hklt⟩) (b ⟨k, hklt⟩)).reluApply
            (reluApproxFeatureWorkspace
              (reluApproxFiniteAffineMap (B ⟨k, hklt⟩) (c ⟨k, hklt⟩)
                (reluApproxSignedMacroRecursion A0 b0 B c A b x k))) := by
          rw [hlayer1, hfeature]
        _ = reluApproxSignedWorkspaceEncode (h := h)
            (reluApproxFiniteAffineMap (A ⟨k, hklt⟩) (b ⟨k, hklt⟩)
              (fun i ↦ relu
                (reluApproxFiniteAffineMap (B ⟨k, hklt⟩) (c ⟨k, hklt⟩)
                  (reluApproxSignedMacroRecursion A0 b0 B c A b x k) i))) :=
          reluApproxSignedMacroUpdateLayer_reluApply _ _ _
        _ = reluApproxSignedWorkspaceEncode (h := h)
            (reluApproxSignedMacroRecursion A0 b0 B c A b x (k + 1)) := by
          simp [reluApproxSignedMacroRecursion, hklt]

/-- Exact output formula for the compiled sequence of nonlinear macro
updates. -/
private theorem reluApproxSignedMacroRecursionNet_realize {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) (x : Fin d → ℝ) :
    (reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias).realize x =
      (∑ i : Fin s,
        outputWeight i * reluApproxSignedMacroRecursion A0 b0 B c A b x T i) +
        outputBias := by
  let N := reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias
  have hdepth : N.depth - 1 = 2 * T := by
    simp [N, reluApproxSignedMacroRecursionNet]
  have hstate : N.hiddenState x (2 * T) =
      reluApproxSignedWorkspaceEncode (h := h)
        (reluApproxSignedMacroRecursion A0 b0 B c A b x T) :=
    reluApproxSignedMacroRecursionNet_hiddenState_even
      A0 b0 B c A b outputWeight outputBias x T (Nat.le_refl T)
  change
    (∑ j : Fin ((s + s) + h),
        (Fin.addCases
          (Fin.addCases (fun i : Fin s ↦ outputWeight i)
            (fun i : Fin s ↦ -outputWeight i))
          (fun _ : Fin h ↦ 0) j) * N.hiddenState x (N.depth - 1) j) +
      outputBias = _
  rw [hdepth, hstate, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right,
    reluApproxSignedWorkspaceEncode_castAdd,
    reluApproxSignedWorkspaceEncode_natAdd, mul_zero, Finset.sum_const_zero, add_zero]
  rw [reluApprox_sum_signedEncode]

private theorem reluApproxSignedMacroRecursionNet_parameterCount {d s h T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias).parameterCount =
      fullyConnectedReLUParameterCount d (2 * T + 1) ((s + s) + h) := rfl

/-- A fully connected identity layer.  Since hidden states are nonnegative,
its ReLU application is the identity on every hidden state. -/
private noncomputable def reluApproxIdentityDenseLayer (w : ℕ) : DenseLayer w w where
  weight i j := if j = i then 1 else 0
  bias _ := 0

private theorem reluApproxIdentityDenseLayer_apply (w : ℕ) (v : Fin w → ℝ) :
    (reluApproxIdentityDenseLayer w).apply v = v := by
  funext i
  simp [reluApproxIdentityDenseLayer, DenseLayer.apply]

private theorem reluApproxIdentityDenseLayer_reluApply (w : ℕ) (v : Fin w → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (reluApproxIdentityDenseLayer w).reluApply v = v := by
  calc
    (reluApproxIdentityDenseLayer w).reluApply v =
        reluVec ((reluApproxIdentityDenseLayer w).apply v) := by
      rfl
    _ = reluVec v := by rw [reluApproxIdentityDenseLayer_apply]
    _ = v := by
      funext i
      simp [reluVec, relu, max_eq_left (hv i)]

/-- Every hidden state of a ReLU network is coordinatewise nonnegative. -/
theorem fullyConnectedReLUNet_hiddenState_nonneg {d : ℕ}
    (N : FullyConnectedReLUNet d) (x : Fin d → ℝ) (t : ℕ) (i : Fin N.width) :
    0 ≤ N.hiddenState x t i := by
  induction t with
  | zero =>
      simp [FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec, relu]
  | succ t ih =>
      by_cases ht : t < N.depth - 1
      · simp [FullyConnectedReLUNet.hiddenState, ht, DenseLayer.reluApply, reluVec, relu]
      · simp [FullyConnectedReLUNet.hiddenState, ht, ih]

/-- Pad a fully connected ReLU network to a prescribed depth by appending
identity hidden layers.  When the prescribed depth is at least the original
depth, the realization is unchanged. -/
noncomputable def reluApproxPadDepth {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) : FullyConnectedReLUNet d where
  depth := D
  width := N.width
  input := N.input
  hidden j :=
    if h : j.val < N.depth - 1 then N.hidden ⟨j.val, h⟩
    else reluApproxIdentityDenseLayer N.width
  outputWeight := N.outputWeight
  outputBias := N.outputBias

@[simp] theorem reluApproxPadDepth_depth {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) :
    (reluApproxPadDepth N D).depth = D := rfl

@[simp] theorem reluApproxPadDepth_width {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) :
    (reluApproxPadDepth N D).width = N.width := rfl

private theorem reluApproxPadDepth_hiddenState_original {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) (hdepth : N.depth ≤ D)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ N.depth - 1) :
    (reluApproxPadDepth N D).hiddenState x t = N.hiddenState x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htN : t < N.depth - 1 := Nat.lt_of_succ_le ht
      have htD : t < D - 1 :=
        lt_of_lt_of_le htN (Nat.sub_le_sub_right hdepth 1)
      simp only [FullyConnectedReLUNet.hiddenState]
      rw [dif_pos (by simpa using htD), dif_pos htN, ih (by omega)]
      simp [reluApproxPadDepth, htN]

private theorem reluApproxPadDepth_hiddenState_stable {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) (x : Fin d → ℝ) (t : ℕ)
    (htN : N.depth - 1 ≤ t) :
    (reluApproxPadDepth N D).hiddenState x (t + 1) =
      (reluApproxPadDepth N D).hiddenState x t := by
  by_cases ht : t < D - 1
  · have hnot : ¬t < N.depth - 1 := by omega
    calc
      (reluApproxPadDepth N D).hiddenState x (t + 1) =
          (reluApproxIdentityDenseLayer N.width).reluApply
            ((reluApproxPadDepth N D).hiddenState x t) := by
        simp [FullyConnectedReLUNet.hiddenState, reluApproxPadDepth,
          ht, hnot]
      _ = (reluApproxPadDepth N D).hiddenState x t :=
        reluApproxIdentityDenseLayer_reluApply N.width _
          (fun i ↦ fullyConnectedReLUNet_hiddenState_nonneg
            (reluApproxPadDepth N D) x t i)
  · simp [FullyConnectedReLUNet.hiddenState, ht]

private theorem reluApproxPadDepth_hiddenState_final {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) (hdepth : N.depth ≤ D)
    (x : Fin d → ℝ) :
    (reluApproxPadDepth N D).hiddenState x (D - 1) =
      N.hiddenState x (N.depth - 1) := by
  have hiter : ∀ t : ℕ, N.depth - 1 ≤ t → t ≤ D - 1 →
      (reluApproxPadDepth N D).hiddenState x t =
        (reluApproxPadDepth N D).hiddenState x (N.depth - 1) := by
    intro t htN htD
    induction t with
    | zero =>
        have hzero : N.depth - 1 = 0 := by omega
        simp [hzero]
    | succ t ih =>
        by_cases heq : t + 1 = N.depth - 1
        · simp [heq]
        · have htN' : N.depth - 1 ≤ t := by omega
          calc
            (reluApproxPadDepth N D).hiddenState x (t + 1) =
                (reluApproxPadDepth N D).hiddenState x t :=
              reluApproxPadDepth_hiddenState_stable N D x t htN'
            _ = (reluApproxPadDepth N D).hiddenState x (N.depth - 1) :=
              ih htN' (by omega)
  calc
    (reluApproxPadDepth N D).hiddenState x (D - 1) =
        (reluApproxPadDepth N D).hiddenState x (N.depth - 1) :=
      hiter (D - 1) (Nat.sub_le_sub_right hdepth 1) le_rfl
    _ = N.hiddenState x (N.depth - 1) :=
      reluApproxPadDepth_hiddenState_original N D hdepth x (N.depth - 1) le_rfl

theorem reluApproxPadDepth_realize {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) (hdepth : N.depth ≤ D)
    (x : Fin d → ℝ) :
    (reluApproxPadDepth N D).realize x = N.realize x := by
  unfold FullyConnectedReLUNet.realize
  simp only [reluApproxPadDepth_depth]
  rw [reluApproxPadDepth_hiddenState_final N D hdepth x]
  rfl

theorem reluApproxPadDepth_parameterCount {d : ℕ}
    (N : FullyConnectedReLUNet d) (D : ℕ) :
    (reluApproxPadDepth N D).parameterCount =
      fullyConnectedReLUParameterCount d D N.width := rfl

theorem fullyConnectedReLUParameterCount_mono_width
    (d D : ℕ) {W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    fullyConnectedReLUParameterCount d D W₁ ≤
      fullyConnectedReLUParameterCount d D W₂ := by
  unfold fullyConnectedReLUParameterCount
  have hinput : (d + 1) * W₁ ≤ (d + 1) * W₂ :=
    Nat.mul_le_mul_left (d + 1) hW
  have hhidden : (W₁ + 1) * W₁ ≤ (W₂ + 1) * W₂ :=
    Nat.mul_le_mul (Nat.add_le_add_right hW 1) hW
  have hlayers : (D - 1) * ((W₁ + 1) * W₁) ≤
      (D - 1) * ((W₂ + 1) * W₂) :=
    Nat.mul_le_mul_left (D - 1) hhidden
  exact Nat.add_le_add (Nat.add_le_add hinput hlayers)
    (Nat.add_le_add_right hW 1)

/-- A bounded-class witness can be replaced by a concrete network at the
class's exact depth, without changing its realization or exceeding the class
width/parameter budget. -/
theorem exists_exactDepth_fullyConnectedReLUNet_of_mem_reluNetworkClass
    {d D W : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hg : g ∈ reluNetworkClass d D W
      (fullyConnectedReLUParameterCount d D W)) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = D ∧ N.width ≤ W ∧
        N.parameterCount ≤ fullyConnectedReLUParameterCount d D W ∧
        ∀ x : Fin d → ℝ, N.realize x = g x := by
  rcases hg with ⟨N, _hNpos, hNdepth, hNwidth, _hNparam, hNrealize⟩
  refine ⟨reluApproxPadDepth N D, rfl, hNwidth, ?_, ?_⟩
  · rw [reluApproxPadDepth_parameterCount]
    exact fullyConnectedReLUParameterCount_mono_width d D hNwidth
  · intro x
    rw [reluApproxPadDepth_realize N D hNdepth x]
    exact (hNrealize x).symm

/-- Compile a finite sequence of two-layer nonlinear macro updates and pad it
to any larger requested depth and width budget.  The returned network remains
fully connected and has the exact realization of the mathematical recursion. -/
theorem exists_reluApproxSignedMacroRecursionNet_exactDepth
    {d s h T D W : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (hdepth : 2 * T + 1 ≤ D) (hwidth : (s + s) + h ≤ W) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = D ∧ N.width ≤ W ∧
        N.parameterCount ≤ fullyConnectedReLUParameterCount d D W ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            (∑ i : Fin s,
              outputWeight i *
                reluApproxSignedMacroRecursion A0 b0 B c A b x T i) +
              outputBias := by
  let N0 :=
    reluApproxSignedMacroRecursionNet A0 b0 B c A b outputWeight outputBias
  refine ⟨reluApproxPadDepth N0 D, rfl, ?_, ?_, ?_⟩
  · simpa [N0, reluApproxSignedMacroRecursionNet] using hwidth
  · rw [reluApproxPadDepth_parameterCount]
    exact fullyConnectedReLUParameterCount_mono_width d D hwidth
  · intro x
    rw [reluApproxPadDepth_realize N0 D]
    · exact reluApproxSignedMacroRecursionNet_realize
        A0 b0 B c A b outputWeight outputBias x
    · simpa [N0, reluApproxSignedMacroRecursionNet] using hdepth

/-- Arrange `q` two-layer nonlinear macro updates per cell and pad to the
exact block depth `cells * (2 * q + 1)`.  This is the architecture used by the
two scans in the shallow ReLU construction: all state dimensions and the
number of macros per cell are fixed before the grid resolution is chosen. -/
private theorem exists_reluApproxSignedMacroBlockScheduleNet
    {d s h cells q : ℕ} (hCells : 0 < cells)
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (B : Fin (cells * q) → Matrix (Fin h) (Fin s) ℝ)
    (c : Fin (cells * q) → Fin h → ℝ)
    (A : Fin (cells * q) → Matrix (Fin s) (Fin h) ℝ)
    (b : Fin (cells * q) → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = cells * (2 * q + 1) ∧
        N.width ≤ (s + s) + h ∧
        N.parameterCount ≤
          fullyConnectedReLUParameterCount d (cells * (2 * q + 1))
            ((s + s) + h) ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            (∑ i : Fin s, outputWeight i *
              reluApproxSignedMacroRecursion A0 b0 B c A b x
                (cells * q) i) + outputBias := by
  have hdepth : 2 * (cells * q) + 1 ≤ cells * (2 * q + 1) := by
    calc
      2 * (cells * q) + 1 = 2 * cells * q + 1 := by ring
      _ ≤ 2 * cells * q + cells :=
        Nat.add_le_add_left (Nat.succ_le_iff.mpr hCells) (2 * cells * q)
      _ = cells * (2 * q + 1) := by ring
  exact exists_reluApproxSignedMacroRecursionNet_exactDepth
    A0 b0 B c A b outputWeight outputBias hdepth le_rfl

/-! ## Value-carrying box selector

The first and second scans in the deep construction repeatedly load a bounded
register value only on one axis-aligned cell.  This is the value-carrying
selector from Lemma 6(b) of shallow ReLU, stated independently of a chosen
register layout so it can be embedded in several parallel macro updates. -/

/-- Sum of the lower- and upper-face violations used by the box selector. -/
private noncomputable def reluApproxBoxViolation {d : ℕ} (R : ℝ)
    (lower upper x : Fin d → ℝ) : ℝ :=
  ∑ q : Fin d,
    (relu (lower q + R⁻¹ - x q) + relu (x q - upper q + R⁻¹))

/-- A two-ReLU-layer gate which returns `value` in the shrunken box and zero
outside the unshrunk box, provided `|value| ≤ R`. -/
noncomputable def reluApproxBoxGate {d : ℕ} (R : ℝ)
    (lower upper x : Fin d → ℝ) (value : ℝ) : ℝ :=
  relu (relu value - R ^ 2 * reluApproxBoxViolation R lower upper x) -
    relu (relu (-value) - R ^ 2 * reluApproxBoxViolation R lower upper x)

private theorem reluApproxBoxViolation_nonneg {d : ℕ} (R : ℝ)
    (lower upper x : Fin d → ℝ) :
    0 ≤ reluApproxBoxViolation R lower upper x := by
  unfold reluApproxBoxViolation
  exact Finset.sum_nonneg fun q _ =>
    add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- The value-carrying box selector never increases the magnitude of its
payload, including in the transition strip between the two exact regimes. -/
private theorem abs_reluApproxBoxGate_le_abs {d : ℕ} (R : ℝ)
    (lower upper x : Fin d → ℝ) (value : ℝ) :
    |reluApproxBoxGate R lower upper x value| ≤ |value| := by
  let penalty := R ^ 2 * reluApproxBoxViolation R lower upper x
  have hpenalty : 0 ≤ penalty :=
    mul_nonneg (sq_nonneg R)
      (reluApproxBoxViolation_nonneg R lower upper x)
  unfold reluApproxBoxGate relu
  change |max (max value 0 - penalty) 0 -
      max (max (-value) 0 - penalty) 0| ≤ |value|
  by_cases hvalue : 0 ≤ value
  · have hneg : max (-value) 0 = 0 := max_eq_right (by linarith)
    have hsecond : max (max (-value) 0 - penalty) 0 = 0 := by
      rw [hneg]
      exact max_eq_right (by linarith)
    rw [hsecond, sub_zero, abs_of_nonneg (le_max_right _ _), abs_of_nonneg hvalue]
    exact max_le (by rw [max_eq_left hvalue]; linarith) hvalue
  · have hvalue' : value ≤ 0 := le_of_not_ge hvalue
    have hpos : max value 0 = 0 := max_eq_right hvalue'
    have hfirst : max (max value 0 - penalty) 0 = 0 := by
      rw [hpos]
      exact max_eq_right (by linarith)
    rw [hfirst, zero_sub, abs_neg,
      abs_of_nonneg (le_max_right _ _), abs_of_nonpos hvalue']
    exact max_le (by rw [max_eq_left (by linarith : 0 ≤ -value)]; linarith)
      (by linarith)

theorem reluApproxBoxGate_nonneg_of_nonneg {d : Nat} (R : Real)
    (lower upper x : Fin d -> Real) {value : Real} (hvalue : 0 <= value) :
    0 <= reluApproxBoxGate R lower upper x value := by
  have hpenalty : 0 <= R ^ 2 * reluApproxBoxViolation R lower upper x :=
    mul_nonneg (sq_nonneg R)
      (reluApproxBoxViolation_nonneg R lower upper x)
  have hrelu_value : relu value = value := by
    simp [relu, max_eq_left hvalue]
  have hrelu_neg : relu (-value) = 0 := by
    simp [relu, max_eq_right (by linarith : -value <= 0)]
  unfold reluApproxBoxGate
  rw [hrelu_value, hrelu_neg]
  have hsecond : relu (0 - R ^ 2 *
      reluApproxBoxViolation R lower upper x) = 0 := by
    unfold relu
    exact max_eq_right (by linarith)
  rw [hsecond, sub_zero]
  exact le_max_right _ _

theorem reluApproxBoxGate_le_of_nonneg {d : Nat} (R : Real)
    (lower upper x : Fin d -> Real) {value : Real} (hvalue : 0 <= value) :
    reluApproxBoxGate R lower upper x value <= value := by
  have hgate := reluApproxBoxGate_nonneg_of_nonneg R lower upper x hvalue
  have habs := abs_reluApproxBoxGate_le_abs R lower upper x value
  simpa [abs_of_nonneg hgate, abs_of_nonneg hvalue] using habs

private theorem reluApproxBoxViolation_eq_zero_on_margin {d : ℕ} {R : ℝ}
    (_hR : 0 < R) (lower upper x : Fin d → ℝ)
    (hx : ∀ q : Fin d, lower q + R⁻¹ ≤ x q ∧ x q ≤ upper q - R⁻¹) :
    reluApproxBoxViolation R lower upper x = 0 := by
  unfold reluApproxBoxViolation
  apply Finset.sum_eq_zero
  intro q _hq
  have hlo : lower q + R⁻¹ - x q ≤ 0 := by linarith [(hx q).1]
  have hhi : x q - upper q + R⁻¹ ≤ 0 := by linarith [(hx q).2]
  simp [relu, max_eq_right hlo, max_eq_right hhi]

private theorem reluApproxBoxGate_eq_value_on_margin {d : ℕ} {R : ℝ}
    (hR : 0 < R) (lower upper x : Fin d → ℝ) (value : ℝ)
    (hx : ∀ q : Fin d, lower q + R⁻¹ ≤ x q ∧ x q ≤ upper q - R⁻¹) :
    reluApproxBoxGate R lower upper x value = value := by
  rw [reluApproxBoxGate,
    reluApproxBoxViolation_eq_zero_on_margin hR lower upper x hx]
  simp only [mul_zero, sub_zero]
  have hidem : ∀ z : ℝ, relu (relu z) = relu z := by
    intro z
    unfold relu
    rw [max_eq_left (le_max_right z 0)]
  rw [hidem value, hidem (-value)]
  unfold relu
  by_cases hv : 0 ≤ value
  · rw [max_eq_left hv, max_eq_right (by linarith : -value ≤ 0)]
    ring
  · have hv' : value ≤ 0 := le_of_not_ge hv
    have hnv : 0 ≤ -value := by linarith
    rw [max_eq_right hv', max_eq_left hnv]
    ring

private theorem reluApproxBoxViolation_inv_le_of_outside {d : ℕ} {R : ℝ}
    (hR : 0 < R) (lower upper x : Fin d → ℝ)
    (hout : ∃ q : Fin d, x q ≤ lower q ∨ upper q ≤ x q) :
    R⁻¹ ≤ reluApproxBoxViolation R lower upper x := by
  rcases hout with ⟨q, hq⟩
  unfold reluApproxBoxViolation
  have hterm : R⁻¹ ≤
      relu (lower q + R⁻¹ - x q) + relu (x q - upper q + R⁻¹) := by
    rcases hq with hlo | hhi
    · have harg : R⁻¹ ≤ lower q + R⁻¹ - x q := by linarith
      have harg0 : 0 ≤ lower q + R⁻¹ - x q :=
        le_trans (inv_nonneg.mpr hR.le) harg
      rw [show relu (lower q + R⁻¹ - x q) =
          lower q + R⁻¹ - x q by simp [relu, max_eq_left harg0]]
      have hnonneg : 0 ≤ relu (x q - upper q + R⁻¹) := by
        simp [relu]
      linarith
    · have harg : R⁻¹ ≤ x q - upper q + R⁻¹ := by linarith
      have harg0 : 0 ≤ x q - upper q + R⁻¹ :=
        le_trans (inv_nonneg.mpr hR.le) harg
      rw [show relu (x q - upper q + R⁻¹) =
          x q - upper q + R⁻¹ by simp [relu, max_eq_left harg0]]
      have hnonneg : 0 ≤ relu (lower q + R⁻¹ - x q) := by
        simp [relu]
      linarith
  refine le_trans hterm (Finset.single_le_sum
    (s := Finset.univ)
    (f := fun i : Fin d =>
      relu (lower i + R⁻¹ - x i) + relu (x i - upper i + R⁻¹)) ?_ ?_)
  · intro i _hi
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  · exact Finset.mem_univ q

theorem reluApproxBoxGate_eq_zero_of_outside {d : ℕ} {R : ℝ}
    (hR : 0 < R) (lower upper x : Fin d → ℝ) (value : ℝ)
    (hvalue : |value| ≤ R)
    (hout : ∃ q : Fin d, x q ≤ lower q ∨ upper q ≤ x q) :
    reluApproxBoxGate R lower upper x value = 0 := by
  have hviol := reluApproxBoxViolation_inv_le_of_outside hR lower upper x hout
  have hmul : R ≤ R ^ 2 * reluApproxBoxViolation R lower upper x := by
    have hRne : R ≠ 0 := ne_of_gt hR
    have hnonneg : 0 ≤ R ^ 2 := sq_nonneg R
    have hscaled := mul_le_mul_of_nonneg_left hviol hnonneg
    calc
      R = R ^ 2 * R⁻¹ := by field_simp
      _ ≤ R ^ 2 * reluApproxBoxViolation R lower upper x := hscaled
  have hvpos : relu value ≤ R := by
    rw [relu]
    exact max_le (le_trans (le_abs_self value) hvalue) hR.le
  have hvneg : relu (-value) ≤ R := by
    rw [relu]
    have habs : |-value| ≤ R := by simpa using hvalue
    exact max_le (le_trans (le_abs_self (-value)) habs) hR.le
  have hpos : relu value - R ^ 2 *
      reluApproxBoxViolation R lower upper x ≤ 0 := by linarith
  have hneg : relu (-value) - R ^ 2 *
      reluApproxBoxViolation R lower upper x ≤ 0 := by linarith
  have hzpos : relu (relu value - R ^ 2 *
      reluApproxBoxViolation R lower upper x) = 0 := by
    unfold relu
    exact max_eq_right hpos
  have hzneg : relu (relu (-value) - R ^ 2 *
      reluApproxBoxViolation R lower upper x) = 0 := by
    unfold relu
    exact max_eq_right hneg
  rw [reluApproxBoxGate, hzpos, hzneg, sub_self]

/-- A scan over pairwise inactive boxes loads exactly the payload belonging to
the unique box whose shrunken interior contains the input.  The payload type is
left scalar because the paper applies the same scan in parallel to every
center, derivative, and correction-tail register. -/
theorem reluApprox_sum_boxGate_eq_payload_of_unique {d T : ℕ} {R : ℝ}
    (hR : 0 < R) (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → ℝ) (x : Fin d → ℝ) (active : Fin T)
    (hpayload : ∀ i : Fin T, |payload i| ≤ R)
    (hactive : ∀ q : Fin d,
      lower active q + R⁻¹ ≤ x q ∧ x q ≤ upper active q - R⁻¹)
    (hinactive : ∀ i : Fin T, i ≠ active →
      ∃ q : Fin d, x q ≤ lower i q ∨ upper i q ≤ x q) :
    (∑ i : Fin T, reluApproxBoxGate R (lower i) (upper i) x (payload i)) =
      payload active := by
  rw [Finset.sum_eq_single active]
  · exact reluApproxBoxGate_eq_value_on_margin hR
      (lower active) (upper active) x (payload active) hactive
  · intro i _hi hne
    exact reluApproxBoxGate_eq_zero_of_outside hR
      (lower i) (upper i) x (payload i) (hpayload i) (hinactive i hne)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ active))

/-- The concrete two-hidden-layer realization of the value-carrying box
selector.  The final input coordinate carries the value to be gated. -/
private noncomputable def reluApproxBoxGateNet (d : ℕ) (R : ℝ)
    (lower upper : Fin d → ℝ) : FullyConnectedReLUNet (d + 1) := by
  let w := (d + d) + 2
  let inputLayer : DenseLayer (d + 1) w :=
    { weight := Fin.addCases
        (Fin.addCases
          (fun q : Fin d ↦ Fin.addCases
            (fun i : Fin d ↦ if i = q then -1 else 0)
            (fun _ : Fin 1 ↦ 0))
          (fun q : Fin d ↦ Fin.addCases
            (fun i : Fin d ↦ if i = q then 1 else 0)
            (fun _ : Fin 1 ↦ 0)))
        (fun sign : Fin 2 ↦ Fin.addCases
          (fun _ : Fin d ↦ 0)
          (fun _ : Fin 1 ↦ if sign.val = 0 then 1 else -1))
      bias := Fin.addCases
        (Fin.addCases
          (fun q : Fin d ↦ lower q + R⁻¹)
          (fun q : Fin d ↦ -upper q + R⁻¹))
        (fun _ : Fin 2 ↦ 0) }
  let hiddenLayer : DenseLayer w w :=
    { weight := fun j k ↦
        if j.val = 0 then
          Fin.addCases (fun _ : Fin (d + d) ↦ -(R ^ 2))
            (fun sign : Fin 2 ↦ if sign.val = 0 then 1 else 0) k
        else if j.val = 1 then
          Fin.addCases (fun _ : Fin (d + d) ↦ -(R ^ 2))
            (fun sign : Fin 2 ↦ if sign.val = 1 then 1 else 0) k
        else 0
      bias := fun _ ↦ 0 }
  exact
    { depth := 2
      width := w
      input := inputLayer
      hidden := fun _ ↦ hiddenLayer
      outputWeight := fun j ↦
        if j.val = 0 then 1 else if j.val = 1 then -1 else 0
      outputBias := 0 }

private theorem reluApproxBoxGateNet_realize (d : ℕ) (R : ℝ) (hd : 0 < d)
    (lower upper : Fin d → ℝ) (x : Fin d → ℝ) (value : ℝ) :
    (reluApproxBoxGateNet d R lower upper).realize
        (Fin.addCases x (fun _ : Fin 1 ↦ value)) =
      reluApproxBoxGate R lower upper x value := by
  let u : Fin (d + 1) → ℝ := Fin.addCases x (fun _ : Fin 1 ↦ value)
  let N := reluApproxBoxGateNet d R lower upper
  let z : Fin ((d + d) + 2) → ℝ := N.input.reluApply u
  have haddNat_eq_natAdd (q : Fin d) : q.addNat d = Fin.natAdd d q := by
    apply Fin.ext
    simp
  have hright : ∀ {α : Type} (f g : Fin d → α) (q : Fin d),
      Fin.addCases f g (q.addNat d) = g q := by
    intro α f g q
    rw [haddNat_eq_natAdd q]
    exact Fin.addCases_right q
  have hzLower (q : Fin d) :
      z (Fin.castAdd 2 (Fin.castAdd d q)) = relu (lower q + R⁻¹ - x q) := by
    simp [z, N, reluApproxBoxGateNet, u, DenseLayer.reluApply, reluVec,
      DenseLayer.apply, Fin.sum_univ_add]
    ring_nf
  have hzUpper (q : Fin d) :
      z (Fin.castAdd 2 (Fin.natAdd d q)) = relu (x q - upper q + R⁻¹) := by
    simp [z, N, reluApproxBoxGateNet, u, DenseLayer.reluApply, reluVec,
      DenseLayer.apply, Fin.sum_univ_add, hright]
    ring_nf
  have hzUpperAdd (q : Fin d) :
      z (Fin.castAdd 2 (q.addNat d)) = relu (x q - upper q + R⁻¹) := by
    rw [haddNat_eq_natAdd q]
    exact hzUpper q
  have hzSign (sign : Fin 2) :
      z (Fin.natAdd (d + d) sign) =
        if sign.val = 0 then relu value else relu (-value) := by
    fin_cases sign <;>
      simp [z, N, reluApproxBoxGateNet, u, DenseLayer.reluApply, reluVec,
        DenseLayer.apply, Fin.sum_univ_add]
  let H : DenseLayer ((d + d) + 2) ((d + d) + 2) :=
    N.hidden
      ⟨0, by change 0 < 2 - 1; omega⟩
  have hrow0 : H.reluApply z ⟨0, by omega⟩ =
      relu (relu value - R ^ 2 * reluApproxBoxViolation R lower upper x) := by
    simp [H, N, reluApproxBoxGateNet, DenseLayer.reluApply, reluVec,
      DenseLayer.apply, Fin.sum_univ_add, hzLower, hzUpperAdd, hzSign,
      reluApproxBoxViolation]
    congr 1
    rw [Finset.mul_sum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring
  have hrow1 : H.reluApply z ⟨1, by omega⟩ =
      relu (relu (-value) - R ^ 2 * reluApproxBoxViolation R lower upper x) := by
    simp [H, N, reluApproxBoxGateNet, DenseLayer.reluApply, reluVec,
      DenseLayer.apply, Fin.sum_univ_add, hzLower, hzUpperAdd, hzSign,
      reluApproxBoxViolation]
    congr 1
    rw [Finset.mul_sum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring
  have hstate :
      N.hiddenState u 1 = H.reluApply z := by
    rw [FullyConnectedReLUNet.hiddenState]
    rw [dif_pos (by change 0 < 2 - 1; omega)]
    rfl
  rw [show Fin.addCases x (fun _ : Fin 1 ↦ value) = u by rfl]
  change ((∑ j : Fin ((d + d) + 2),
      (if j.val = 0 then 1 else if j.val = 1 then -1 else 0) *
        N.hiddenState u 1 j) + 0) = _
  rw [add_zero]
  rw [hstate]
  change (∑ j : Fin ((d + d) + 2),
      (if j.val = 0 then 1 else if j.val = 1 then -1 else 0) * H.reluApply z j) = _
  have hsum :
      (∑ j : Fin ((d + d) + 2),
          (if j.val = 0 then 1 else if j.val = 1 then -1 else 0) * H.reluApply z j) =
        H.reluApply z ⟨0, by omega⟩ - H.reluApply z ⟨1, by omega⟩ := by
    let i0 : Fin ((d + d) + 2) := ⟨0, by omega⟩
    let i1 : Fin ((d + d) + 2) := ⟨1, by omega⟩
    calc
      (∑ j : Fin ((d + d) + 2),
          (if j.val = 0 then 1 else if j.val = 1 then -1 else 0) * H.reluApply z j) =
          ∑ j : Fin ((d + d) + 2),
            (if j = i0 then H.reluApply z i0
              else if j = i1 then -H.reluApply z i1 else 0) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hj0 : j = i0
            · subst j
              simp [i0, i1]
            · have hjv0 : j.val ≠ 0 := by
                intro h
                apply hj0
                apply Fin.ext
                simpa [i0] using h
              by_cases hj1 : j = i1
              · subst j
                simp [i0, i1]
              · have hjv1 : j.val ≠ 1 := by
                  intro h
                  apply hj1
                  apply Fin.ext
                  simpa [i1] using h
                simp [hj0, hj1, hjv0, hjv1]
      _ = H.reluApply z i0 - H.reluApply z i1 := by
            let F : Fin ((d + d) + 2) → ℝ := fun j ↦
              if j = i0 then H.reluApply z i0
              else if j = i1 then -H.reluApply z i1 else 0
            change (∑ j : Fin ((d + d) + 2), F j) = _
            rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin ((d + d) + 2)))
              F (Finset.mem_univ i0)]
            have hi01 : i1 ≠ i0 := by
              intro h
              have := congrArg Fin.val h
              simp [i0, i1] at this
            have hi10 : i0 ≠ i1 := Ne.symm hi01
            have hrest :
                (∑ j ∈ (Finset.univ : Finset (Fin ((d + d) + 2))).erase i0, F j) =
                  -H.reluApply z i1 := by
              rw [Finset.sum_eq_single i1]
              · simp [F, hi01]
              · intro j hj hji1
                have hji0 : j ≠ i0 := (Finset.mem_erase.mp hj).1
                simp [F, hji0, hji1]
              · intro hi1
                exact False.elim (hi1 (Finset.mem_erase.mpr ⟨hi01, Finset.mem_univ i1⟩))
            rw [hrest]
            simp [F, hi10]
            ring
  rw [hsum, hrow0, hrow1]
  rfl

/-- Fix the value input of `reluApproxBoxGateNet` in the input-layer bias.
The resulting network has domain dimension `d` and the same two hidden
layers and width. -/
private noncomputable def reluApproxFixedBoxGateNet (d : ℕ) (R : ℝ)
    (lower upper : Fin d → ℝ) (value : ℝ) : FullyConnectedReLUNet d := by
  let base := reluApproxBoxGateNet d R lower upper
  exact
    { depth := base.depth
      width := base.width
      input :=
        { weight := fun i j ↦ base.input.weight i (Fin.castAdd 1 j)
          bias := fun i ↦ base.input.bias i +
            base.input.weight i (Fin.natAdd d 0) * value }
      hidden := base.hidden
      outputWeight := base.outputWeight
      outputBias := base.outputBias }

@[simp] theorem reluApproxFixedBoxGateNet_depth (d : ℕ) (R : ℝ)
    (lower upper : Fin d → ℝ) (value : ℝ) :
    (reluApproxFixedBoxGateNet d R lower upper value).depth = 2 := rfl

@[simp] theorem reluApproxFixedBoxGateNet_width (d : ℕ) (R : ℝ)
    (lower upper : Fin d → ℝ) (value : ℝ) :
    (reluApproxFixedBoxGateNet d R lower upper value).width = (d + d) + 2 := rfl

private theorem reluApproxFixedBoxGateNet_realize (d : ℕ) (R : ℝ) (hd : 0 < d)
    (lower upper : Fin d → ℝ) (value : ℝ) (x : Fin d → ℝ) :
    (reluApproxFixedBoxGateNet d R lower upper value).realize x =
      reluApproxBoxGate R lower upper x value := by
  let u : Fin (d + 1) → ℝ := Fin.addCases x (fun _ : Fin 1 ↦ value)
  let base := reluApproxBoxGateNet d R lower upper
  have hinput :
      (reluApproxFixedBoxGateNet d R lower upper value).input.reluApply x =
        base.input.reluApply u := by
    funext i
    unfold DenseLayer.reluApply reluVec
    change relu
        ((reluApproxFixedBoxGateNet d R lower upper value).input.apply x i) =
      relu (base.input.apply u i)
    congr 1
    simp [DenseLayer.apply, reluApproxFixedBoxGateNet, base, u,
      Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Fin.sum_univ_one]
    ring
  have hstate :
      (reluApproxFixedBoxGateNet d R lower upper value).hiddenState x 1 =
        base.hiddenState u 1 := by
    simp only [FullyConnectedReLUNet.hiddenState]
    rw [dif_pos (by change 0 < 2 - 1; omega)]
    rw [dif_pos (by change 0 < 2 - 1; omega)]
    change
      (base.hidden ⟨0, by change 0 < 2 - 1; omega⟩).reluApply
          ((reluApproxFixedBoxGateNet d R lower upper value).input.reluApply x) =
        (base.hidden ⟨0, by change 0 < 2 - 1; omega⟩).reluApply
          (base.input.reluApply u)
    rw [hinput]
  change
    (∑ j : Fin ((d + d) + 2),
        base.outputWeight j *
          (reluApproxFixedBoxGateNet d R lower upper value).hiddenState x 1 j) +
        base.outputBias = _
  rw [hstate]
  exact reluApproxBoxGateNet_realize d R hd lower upper x value

private theorem reluApproxFixedBoxGateNet_parameterCount (d : ℕ) (R : ℝ)
    (lower upper : Fin d → ℝ) (value : ℝ) :
    (reluApproxFixedBoxGateNet d R lower upper value).parameterCount =
      fullyConnectedReLUParameterCount d 2 ((d + d) + 2) := rfl

private theorem reluApproxFixedBoxGateNet_mem_reluNetworkClass
    (d : ℕ) (R : ℝ) (hd : 0 < d)
    (lower upper : Fin d → ℝ) (value : ℝ) :
    (fun x ↦ reluApproxBoxGate R lower upper x value) ∈
      reluNetworkClass d 2 ((d + d) + 2)
        (fullyConnectedReLUParameterCount d 2 ((d + d) + 2)) := by
  refine ⟨reluApproxFixedBoxGateNet d R lower upper value,
    by norm_num, le_rfl, le_rfl, le_rfl, ?_⟩
  intro x
  exact (reluApproxFixedBoxGateNet_realize d R hd lower upper value x).symm

/-- Serially scan a finite family of boxes and accumulate their scalar
payloads.  The depth is linear in the number of boxes while the width is
independent of that number. -/
theorem exists_reluApproxBoxGateScanNet {d T : ℕ} (hd : 0 < d)
    (R : ℝ) (lower upper : Fin T → Fin d → ℝ) (payload : Fin T → ℝ) :
    ∃ N : FullyConnectedReLUNet d,
      0 < N.depth ∧
        N.depth ≤ (T + 1) * (2 + 1) ∧
        N.width ≤ 2 * d + ((d + d) + 2) + 3 ∧
        N.parameterCount ≤
          fullyConnectedReLUParameterCount d ((T + 1) * (2 + 1))
            (2 * d + ((d + d) + 2) + 3) ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            ∑ i : Fin T, reluApproxBoxGate R (lower i) (upper i) x (payload i) := by
  let approx : Fin T → (Fin d → ℝ) → ℝ := fun i x ↦
    reluApproxBoxGate R (lower i) (upper i) x (payload i)
  have hclass : ∀ i : Fin T,
      approx i ∈ reluNetworkClass d 2 ((d + d) + 2)
        (fullyConnectedReLUParameterCount d 2 ((d + d) + 2)) := by
    intro i
    exact reluApproxFixedBoxGateNet_mem_reluNetworkClass
      d R hd (lower i) (upper i) (payload i)
  rcases finite_linear_combination_reluNetworkClass_serial_fixed_width_network_witness_bound
      (d := d) (D0 := 2) (W0 := (d + d) + 2)
      (P0 := fullyConnectedReLUParameterCount d 2 ((d + d) + 2))
      (by norm_num) (by omega) (fun _ : Fin T ↦ (1 : ℝ)) approx hclass with
    ⟨N, hNdepth, hNdepth_le, hNwidth, hNparam, hNrealize⟩
  refine ⟨N, hNdepth, ?_, hNwidth, ?_, ?_⟩
  · simpa using hNdepth_le
  · simpa using hNparam
  · intro x
    simpa [approx] using hNrealize x

/-- Under the unique-active-box hypotheses, the serial scan network returns
the active box's payload exactly. -/
private theorem exists_reluApproxBoxGateScanNet_eq_payload_of_unique
    {d T : ℕ} {R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (lower upper : Fin T → Fin d → ℝ) (payload : Fin T → ℝ)
    (x : Fin d → ℝ) (active : Fin T)
    (hpayload : ∀ i : Fin T, |payload i| ≤ R)
    (hactive : ∀ q : Fin d,
      lower active q + R⁻¹ ≤ x q ∧ x q ≤ upper active q - R⁻¹)
    (hinactive : ∀ i : Fin T, i ≠ active →
      ∃ q : Fin d, x q ≤ lower i q ∨ upper i q ≤ x q) :
    ∃ N : FullyConnectedReLUNet d,
      0 < N.depth ∧
        N.depth ≤ (T + 1) * (2 + 1) ∧
        N.width ≤ 2 * d + ((d + d) + 2) + 3 ∧
        N.parameterCount ≤
          fullyConnectedReLUParameterCount d ((T + 1) * (2 + 1))
            (2 * d + ((d + d) + 2) + 3) ∧
        N.realize x = payload active := by
  rcases exists_reluApproxBoxGateScanNet hd R lower upper payload with
    ⟨N, hNdepth, hNdepth_le, hNwidth, hNparam, hNrealize⟩
  refine ⟨N, hNdepth, hNdepth_le, hNwidth, hNparam, ?_⟩
  rw [hNrealize]
  exact reluApprox_sum_boxGate_eq_payload_of_unique hR lower upper payload x
    active hpayload hactive hinactive


/-! ## State-preserving box scan

The scalar serial-sum theorem above hides the input-carry channels inside its
network witness.  The paper compiler needs those channels after the coarse
scan, because the selected code is decoded while the original input is still
used by the Taylor readout.  The following two macro updates expose exactly
that stronger state invariant. -/

/-- State size for an input vector, an accumulator, and three box-gate work
registers (violation and the positive/negative payload parts). -/
private def reluApproxBoxScanStateSize (d : ℕ) : ℕ := d + 4

/-- Feature size shared by the load and accumulate macros.  The first `2s`
features are a signed copy of the complete state; the remaining features are
the two face violations per coordinate and two payload channels. -/
private def reluApproxBoxScanFeatureSize (d : ℕ) : ℕ :=
  let s := reluApproxBoxScanStateSize d
  (s + s) + (d + d + 2)

/-- The state before a box is processed. -/
private noncomputable def reluApproxBoxScanState {d : ℕ}
    (x : Fin d → ℝ) (acc : ℝ) :
    Fin (reluApproxBoxScanStateSize d) → ℝ :=
  Fin.addCases x (fun i : Fin 4 ↦ if i.val = 0 then acc else 0)

/-- State after the first macro of a box: preserve `x` and `acc`, and store
the face-violation sum and the signed payload parts. -/
private noncomputable def reluApproxBoxScanLoadedState {d : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ) (payload acc : ℝ) :
    Fin (reluApproxBoxScanStateSize d) → ℝ :=
  Fin.addCases x (fun i : Fin 4 ↦
    if i.val = 0 then acc
    else if i.val = 1 then reluApproxBoxViolation R lower upper x
    else if i.val = 2 then relu payload
    else relu (-payload))

/-- Signed-copy rows used at the front of both box-scan feature maps. -/
private noncomputable def reluApproxBoxScanCopyRows (s : ℕ) :
    Matrix (Fin (s + s)) (Fin s) ℝ :=
  Fin.addCases
    (fun i j ↦ if i = j then 1 else 0)
    (fun i j ↦ if i = j then -1 else 0)

/-- First macro feature map: signed-copy the old state, compute all face
violations, and create positive/negative payload features. -/
private noncomputable def reluApproxBoxScanLoadFeatureMatrix (d : ℕ) :
    Matrix (Fin (reluApproxBoxScanFeatureSize d))
      (Fin (reluApproxBoxScanStateSize d)) ℝ :=
  let s := reluApproxBoxScanStateSize d
  Fin.addCases (reluApproxBoxScanCopyRows s)
    (Fin.addCases
      (Fin.addCases
        (fun q j ↦ if j.val = q.val then -1 else 0)
        (fun q j ↦ if j.val = q.val then 1 else 0))
      (fun _ _ ↦ 0))

private noncomputable def reluApproxBoxScanLoadFeatureBias {d : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : ℝ) :
    Fin (reluApproxBoxScanFeatureSize d) → ℝ :=
  let s := reluApproxBoxScanStateSize d
  Fin.addCases (fun _ : Fin (s + s) ↦ 0)
    (Fin.addCases
      (Fin.addCases (fun q ↦ lower q + R⁻¹) (fun q ↦ -upper q + R⁻¹))
      (fun i : Fin 2 ↦ if i.val = 0 then payload else -payload))

/-- Decode a state coordinate from the signed-copy feature prefix. -/
private noncomputable def reluApproxBoxScanDecodeRow (d : ℕ)
    (i : Fin (reluApproxBoxScanStateSize d)) :
    Fin (reluApproxBoxScanFeatureSize d) → ℝ :=
  let s := reluApproxBoxScanStateSize d
  Fin.addCases
    (Fin.addCases (fun j : Fin s ↦ if j = i then 1 else 0)
      (fun j : Fin s ↦ if j = i then -1 else 0))
    (fun _ ↦ 0)

/-- First macro update map. -/
private noncomputable def reluApproxBoxScanLoadUpdateMatrix (d : ℕ) :
    Matrix (Fin (reluApproxBoxScanStateSize d))
      (Fin (reluApproxBoxScanFeatureSize d)) ℝ :=
  fun i ↦
    if hi : i.val < d + 1 then reluApproxBoxScanDecodeRow d i
    else if hi1 : i.val = d + 1 then
      let s := reluApproxBoxScanStateSize d
      Fin.addCases (fun _ : Fin (s + s) ↦ 0)
        (Fin.addCases (fun _ : Fin (d + d) ↦ 1) (fun _ : Fin 2 ↦ 0))
    else if hi2 : i.val = d + 2 then
      let s := reluApproxBoxScanStateSize d
      Fin.addCases (fun _ : Fin (s + s) ↦ 0)
        (Fin.addCases (fun _ : Fin (d + d) ↦ 0)
          (fun k : Fin 2 ↦ if k.val = 0 then 1 else 0))
    else
      let s := reluApproxBoxScanStateSize d
      Fin.addCases (fun _ : Fin (s + s) ↦ 0)
        (Fin.addCases (fun _ : Fin (d + d) ↦ 0)
          (fun k : Fin 2 ↦ if k.val = 1 then 1 else 0))

/-- Second macro feature map.  Its first two extra rows are the two outer
box-gate preactivations. -/
private noncomputable def reluApproxBoxScanAccFeatureMatrix (d : ℕ) (R : ℝ) :
    Matrix (Fin (reluApproxBoxScanFeatureSize d))
      (Fin (reluApproxBoxScanStateSize d)) ℝ :=
  let s := reluApproxBoxScanStateSize d
  Fin.addCases (reluApproxBoxScanCopyRows s)
    (fun k j ↦
      if k.val = 0 then
        if j.val = d + 1 then -(R ^ 2) else if j.val = d + 2 then 1 else 0
      else if k.val = 1 then
        if j.val = d + 1 then -(R ^ 2) else if j.val = d + 3 then 1 else 0
      else 0)

/-- Second macro update: preserve `x`, add the signed gate to the accumulator,
and clear the three temporary registers. -/
private noncomputable def reluApproxBoxScanAccUpdateMatrix (d : ℕ) :
    Matrix (Fin (reluApproxBoxScanStateSize d))
      (Fin (reluApproxBoxScanFeatureSize d)) ℝ :=
  fun i ↦
    if hi : i.val < d then reluApproxBoxScanDecodeRow d i
    else if hi0 : i.val = d then
      let s := reluApproxBoxScanStateSize d
      Fin.addCases
        (Fin.addCases
          (fun j : Fin s ↦ if j.val = d then 1 else 0)
          (fun j : Fin s ↦ if j.val = d then -1 else 0))
        (fun k ↦ if k.val = 0 then 1 else if k.val = 1 then -1 else 0)
    else fun _ ↦ 0

/-- Exact feature vector produced by the load macro. -/
private noncomputable def reluApproxBoxScanLoadFeatures {d : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : ℝ)
    (u : Fin (reluApproxBoxScanStateSize d) → ℝ) :
    Fin (reluApproxBoxScanFeatureSize d) → ℝ :=
  let s := reluApproxBoxScanStateSize d
  Fin.addCases (reluApproxSignedEncode u)
    (Fin.addCases
      (Fin.addCases
        (fun q : Fin d ↦ relu (lower q + R⁻¹ - u (Fin.castAdd 4 q)))
        (fun q : Fin d ↦ relu (u (Fin.castAdd 4 q) - upper q + R⁻¹)))
      (fun i : Fin 2 ↦ if i.val = 0 then relu payload else relu (-payload)))

private theorem reluApproxBoxScanLoadFeatures_exact {d : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : ℝ)
    (u : Fin (reluApproxBoxScanStateSize d) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxBoxScanLoadFeatureMatrix d)
      (reluApproxBoxScanLoadFeatureBias R lower upper payload) u i)) =
      reluApproxBoxScanLoadFeatures R lower upper payload u := by
  have hsum_pos (k : Fin (reluApproxBoxScanStateSize d)) :
      (∑ x : Fin (reluApproxBoxScanStateSize d),
        (if k = x then 1 else 0) * u x) = u k := by
    classical
    calc
      (∑ x : Fin (reluApproxBoxScanStateSize d),
          (if k = x then 1 else 0) * u x) =
          (if k = k then 1 else 0) * u k := by
            apply Finset.sum_eq_single k
            · intro b _hb hbk
              simp [Ne.symm hbk]
            · simp
      _ = u k := by simp
  have hsum_neg (k : Fin (reluApproxBoxScanStateSize d)) :
      (∑ x : Fin (reluApproxBoxScanStateSize d),
        (if k = x then -1 else 0) * u x) = -u k := by
    classical
    calc
      (∑ x : Fin (reluApproxBoxScanStateSize d),
          (if k = x then -1 else 0) * u x) =
          (if k = k then -1 else 0) * u k := by
            apply Finset.sum_eq_single k
            · intro b _hb hbk
              simp [Ne.symm hbk]
            · simp
      _ = -u k := by simp
  have hsum_coord_neg (k : Fin d) :
      (∑ x : Fin (reluApproxBoxScanStateSize d),
        (if x.val = k.val then -1 else 0) * u x) =
        -u (Fin.castAdd 4 k) := by
    have hcond : ∀ x : Fin (reluApproxBoxScanStateSize d),
        (x.val = k.val) = (x = Fin.castAdd 4 k) := by
      intro x
      apply propext
      constructor
      · intro hv
        apply Fin.ext
        simpa using hv
      · intro hx
        simpa [hx]
    simp_rw [hcond]
    simpa using hsum_neg (Fin.castAdd 4 k)
  have hsum_coord_pos (k : Fin d) :
      (∑ x : Fin (reluApproxBoxScanStateSize d),
        (if x.val = k.val then 1 else 0) * u x) =
        u (Fin.castAdd 4 k) := by
    have hcond : ∀ x : Fin (reluApproxBoxScanStateSize d),
        (x.val = k.val) = (x = Fin.castAdd 4 k) := by
      intro x
      apply propext
      constructor
      · intro hv
        apply Fin.ext
        simpa using hv
      · intro hx
        simpa [hx]
    simp_rw [hcond]
    simpa using hsum_pos (Fin.castAdd 4 k)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp [reluApproxBoxScanLoadFeatures,
        reluApproxBoxScanLoadFeatureMatrix,
        reluApproxBoxScanLoadFeatureBias,
        reluApproxBoxScanCopyRows, reluApproxFiniteAffineMap]
    · intro k
      simp only [reluApproxBoxScanLoadFeatures, reluApproxBoxScanFeatureSize,
        reluApproxBoxScanLoadFeatureMatrix,
        reluApproxBoxScanLoadFeatureBias,
        reluApproxBoxScanCopyRows, reluApproxFiniteAffineMap,
        Fin.addCases_left, Fin.addCases_right, add_zero]
      rw [hsum_neg]
      exact (reluApproxSignedEncode_natAdd u k).symm
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp only [reluApproxBoxScanLoadFeatures, reluApproxBoxScanFeatureSize,
          reluApproxBoxScanLoadFeatureMatrix,
          reluApproxBoxScanLoadFeatureBias, reluApproxFiniteAffineMap,
          Fin.addCases_right, Fin.addCases_left, add_zero]
        rw [hsum_coord_neg]
        congr 1
        ring
      · intro k
        simp only [reluApproxBoxScanLoadFeatures, reluApproxBoxScanFeatureSize,
          reluApproxBoxScanLoadFeatureMatrix,
          reluApproxBoxScanLoadFeatureBias, reluApproxFiniteAffineMap,
          Fin.addCases_left, Fin.addCases_right, add_zero]
        rw [hsum_coord_pos]
        congr 1
        ring
    · intro k
      fin_cases k <;>
        simp [reluApproxBoxScanLoadFeatures,
          reluApproxBoxScanLoadFeatureMatrix,
          reluApproxBoxScanLoadFeatureBias,
          reluApproxFiniteAffineMap]

/-- The signed-copy prefix of a box-scan feature vector decodes any state
coordinate exactly; all gate-work features have zero coefficient in this row. -/
private theorem reluApproxBoxScanDecodeRow_dot_loadFeatures {d : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : ℝ)
    (u : Fin (reluApproxBoxScanStateSize d) → ℝ)
    (i : Fin (reluApproxBoxScanStateSize d)) :
    (∑ j : Fin (reluApproxBoxScanFeatureSize d),
        reluApproxBoxScanDecodeRow d i j *
          reluApproxBoxScanLoadFeatures R lower upper payload u j) = u i := by
  simp only [reluApproxBoxScanFeatureSize]
  rw [Fin.sum_univ_add]
  simp only [reluApproxBoxScanDecodeRow,
    reluApproxBoxScanLoadFeatures, Fin.addCases_left, Fin.addCases_right,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right,
    reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd]
  have hpos :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
          (if j = i then 1 else 0) * relu (u j)) = relu (u i) := by
    classical
    calc
      _ = (if i = i then 1 else 0) * relu (u i) := by
        apply Finset.sum_eq_single i
        · intro b _hb hbi
          simp [hbi]
        · simp
      _ = relu (u i) := by simp
  have hneg :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
          (if j = i then -1 else 0) * relu (-u j)) = -relu (-u i) := by
    classical
    calc
      _ = (if i = i then -1 else 0) * relu (-u i) := by
        apply Finset.sum_eq_single i
        · intro b _hb hbi
          simp [hbi]
        · simp
      _ = -relu (-u i) := by simp
  rw [hpos, hneg]
  exact reluApproxSignedEncode_sub (u i)

/-- The first box-scan macro preserves the input and accumulator and loads the
three work registers used by the outer gate. -/
private theorem reluApproxBoxScanLoadUpdate_exact {d : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ) (payload acc : ℝ) :
    reluApproxFiniteAffineMap (reluApproxBoxScanLoadUpdateMatrix d)
        (fun _ ↦ 0)
        (reluApproxBoxScanLoadFeatures R lower upper payload
          (reluApproxBoxScanState x acc)) =
      reluApproxBoxScanLoadedState R lower upper x payload acc := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    have hk : (Fin.castAdd 4 k : Fin (reluApproxBoxScanStateSize d)).val < d + 1 := by
      simp [reluApproxBoxScanStateSize]
    simp only [reluApproxFiniteAffineMap,
      reluApproxBoxScanLoadUpdateMatrix, dif_pos hk, add_zero]
    rw [reluApproxBoxScanDecodeRow_dot_loadFeatures]
    simp [reluApproxBoxScanState, reluApproxBoxScanLoadedState]
  · intro q
    fin_cases q
    · simp only [reluApproxFiniteAffineMap,
        reluApproxBoxScanLoadUpdateMatrix]
      split
      · simp only [add_zero]
        rw [reluApproxBoxScanDecodeRow_dot_loadFeatures]
        simp [reluApproxBoxScanState, reluApproxBoxScanLoadedState,
          reluApproxBoxScanStateSize]
      · rename_i h
        exfalso
        apply h
        simp
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanLoadUpdateMatrix,
        reluApproxBoxScanLoadFeatures, reluApproxBoxScanLoadedState,
        reluApproxBoxScanStateSize, reluApproxBoxScanFeatureSize,
        reluApproxBoxViolation, Fin.sum_univ_add]
      have haddNat_eq_natAdd (q : Fin d) : q.addNat d = Fin.natAdd d q := by
        apply Fin.ext
        simp
      have hstate (q : Fin d) :
          reluApproxBoxScanState x acc (Fin.castAdd 4 q) = x q := by
        simp [reluApproxBoxScanState]
      simp_rw [hstate]
      have hsecond :
          (∑ q : Fin d,
              Fin.addCases
                (fun p : Fin d ↦ relu (lower p + R⁻¹ - x p))
                (fun p : Fin d ↦ relu (x p - upper p + R⁻¹))
                (q.addNat d)) =
            ∑ q : Fin d, relu (x q - upper q + R⁻¹) := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [haddNat_eq_natAdd q]
        exact Fin.addCases_right q
      rw [hsecond, Finset.sum_add_distrib]
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanLoadUpdateMatrix,
        reluApproxBoxScanLoadFeatures, reluApproxBoxScanLoadedState,
        reluApproxBoxScanStateSize, reluApproxBoxScanFeatureSize,
        Fin.sum_univ_add]
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanLoadUpdateMatrix,
        reluApproxBoxScanLoadFeatures, reluApproxBoxScanLoadedState,
        reluApproxBoxScanStateSize, reluApproxBoxScanFeatureSize,
        Fin.sum_univ_add]

/-- Exact feature vector produced by the accumulator macro. -/
private noncomputable def reluApproxBoxScanAccFeatures {d : ℕ} (R : ℝ)
    (u : Fin (reluApproxBoxScanStateSize d) → ℝ) :
    Fin (reluApproxBoxScanFeatureSize d) → ℝ :=
  let violation : Fin (reluApproxBoxScanStateSize d) :=
    Fin.natAdd d (1 : Fin 4)
  let positive : Fin (reluApproxBoxScanStateSize d) :=
    Fin.natAdd d (2 : Fin 4)
  let negative : Fin (reluApproxBoxScanStateSize d) :=
    Fin.natAdd d (3 : Fin 4)
  Fin.addCases (reluApproxSignedEncode u) (fun k ↦
    if k.val = 0 then relu (u positive - R ^ 2 * u violation)
    else if k.val = 1 then relu (u negative - R ^ 2 * u violation)
    else 0)

private theorem reluApproxBoxScanAccFeatures_exact {d : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ) (payload acc : ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxBoxScanAccFeatureMatrix d R) (fun _ ↦ 0)
      (reluApproxBoxScanLoadedState R lower upper x payload acc) i)) =
      reluApproxBoxScanAccFeatures R
        (reluApproxBoxScanLoadedState R lower upper x payload acc) := by
  let u := reluApproxBoxScanLoadedState R lower upper x payload acc
  have hsum_pos (k : Fin (reluApproxBoxScanStateSize d)) :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
        (if k = j then 1 else 0) * u j) = u k := by
    classical
    calc
      _ = (if k = k then 1 else 0) * u k := by
        apply Finset.sum_eq_single k
        · intro b _hb hbk
          simp [Ne.symm hbk]
        · simp
      _ = u k := by simp
  have hsum_neg (k : Fin (reluApproxBoxScanStateSize d)) :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
        (if k = j then -1 else 0) * u j) = -u k := by
    classical
    calc
      _ = (if k = k then -1 else 0) * u k := by
        apply Finset.sum_eq_single k
        · intro b _hb hbk
          simp [Ne.symm hbk]
        · simp
      _ = -u k := by simp
  have hgatePos :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
          if j.val = d + 1 then -(R ^ 2 * u j)
          else if j.val = d + 2 then u j else 0) =
        u (Fin.natAdd d (2 : Fin 4)) -
          R ^ 2 * u (Fin.natAdd d (1 : Fin 4)) := by
    simp only [reluApproxBoxScanStateSize]
    rw [Fin.sum_univ_add]
    have hleft :
        (∑ j : Fin d,
            if (Fin.castAdd 4 j).val = d + 1 then
              -(R ^ 2 * u (Fin.castAdd 4 j))
            else if (Fin.castAdd 4 j).val = d + 2 then
              u (Fin.castAdd 4 j) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      have hj := j.isLt
      simp only [Fin.val_castAdd]
      split_ifs
      · exfalso
        omega
      · exfalso
        omega
      · rfl
    rw [hleft, Fin.sum_univ_four]
    simp
    ring
  have hgateNeg :
      (∑ j : Fin (reluApproxBoxScanStateSize d),
          if j.val = d + 1 then -(R ^ 2 * u j)
          else if j.val = d + 3 then u j else 0) =
        u (Fin.natAdd d (3 : Fin 4)) -
          R ^ 2 * u (Fin.natAdd d (1 : Fin 4)) := by
    simp only [reluApproxBoxScanStateSize]
    rw [Fin.sum_univ_add]
    have hleft :
        (∑ j : Fin d,
            if (Fin.castAdd 4 j).val = d + 1 then
              -(R ^ 2 * u (Fin.castAdd 4 j))
            else if (Fin.castAdd 4 j).val = d + 3 then
              u (Fin.castAdd 4 j) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      have hj := j.isLt
      simp only [Fin.val_castAdd]
      split_ifs
      · exfalso
        omega
      · exfalso
        omega
      · rfl
    rw [hleft, Fin.sum_univ_four]
    simp
    ring
  change (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxBoxScanAccFeatureMatrix d R) (fun _ ↦ 0) u i)) =
    reluApproxBoxScanAccFeatures R u
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccFeatureMatrix,
        reluApproxBoxScanCopyRows, reluApproxBoxScanAccFeatures,
        Fin.addCases_left, add_zero]
      rw [hsum_pos]
      exact (reluApproxSignedEncode_castAdd u k).symm
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccFeatureMatrix,
        reluApproxBoxScanCopyRows, reluApproxBoxScanAccFeatures,
        Fin.addCases_left, Fin.addCases_right, add_zero]
      rw [hsum_neg]
      exact (reluApproxSignedEncode_natAdd u k).symm
  · intro k
    by_cases hk0 : k.val = 0
    · have hk0' : k = 0 := Fin.ext hk0
      subst k
      simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccFeatureMatrix, reluApproxBoxScanAccFeatures,
        hgatePos]
    · by_cases hk1 : k.val = 1
      · have hk1' : k = 1 := Fin.ext hk1
        subst k
        simp [reluApproxFiniteAffineMap,
          reluApproxBoxScanAccFeatureMatrix, reluApproxBoxScanAccFeatures,
          hgateNeg]
      · have hk0' : k ≠ 0 := by
          intro hk
          apply hk0
          exact congrArg Fin.val hk
        simp [reluApproxFiniteAffineMap,
          reluApproxBoxScanAccFeatureMatrix, reluApproxBoxScanAccFeatures,
          hk0, hk1, hk0']
        simp [relu]

private theorem reluApproxBoxScanDecodeRow_dot_accFeatures {d : ℕ}
    (R : ℝ) (u : Fin (reluApproxBoxScanStateSize d) → ℝ)
    (i : Fin (reluApproxBoxScanStateSize d)) :
    (∑ j : Fin (reluApproxBoxScanFeatureSize d),
        reluApproxBoxScanDecodeRow d i j *
          reluApproxBoxScanAccFeatures R u j) = u i := by
  simpa [reluApproxBoxScanAccFeatures, reluApproxBoxScanLoadFeatures,
    reluApproxBoxScanDecodeRow, reluApproxBoxScanFeatureSize,
    Fin.sum_univ_add] using
      (reluApproxBoxScanDecodeRow_dot_loadFeatures
        (R := R) (lower := fun _ ↦ 0) (upper := fun _ ↦ 0)
        (payload := 0) u i)

/-- The accumulator macro adds the current box gate and returns to the
canonical scan-state shape. -/
private theorem reluApproxBoxScanAccUpdate_exact {d : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ) (payload acc : ℝ) :
    reluApproxFiniteAffineMap (reluApproxBoxScanAccUpdateMatrix d)
        (fun _ ↦ 0)
        (reluApproxBoxScanAccFeatures R
          (reluApproxBoxScanLoadedState R lower upper x payload acc)) =
      reluApproxBoxScanState x
        (acc + reluApproxBoxGate R lower upper x payload) := by
  let u := reluApproxBoxScanLoadedState R lower upper x payload acc
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    have hk : (Fin.castAdd 4 k : Fin (reluApproxBoxScanStateSize d)).val < d := by
      simp [reluApproxBoxScanStateSize]
    simp only [reluApproxFiniteAffineMap,
      reluApproxBoxScanAccUpdateMatrix, dif_pos hk, add_zero]
    rw [reluApproxBoxScanDecodeRow_dot_accFeatures]
    simp [u, reluApproxBoxScanLoadedState, reluApproxBoxScanState]
  · intro q
    fin_cases q
    · simp only [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccUpdateMatrix]
      split
      · rename_i h
        exfalso
        have : ¬(Fin.natAdd d (0 : Fin 4) :
            Fin (reluApproxBoxScanStateSize d)).val < d := by simp
        exact this h
      · split
        · have hsigned :
              (∑ j : Fin (reluApproxBoxScanStateSize d +
                  reluApproxBoxScanStateSize d),
                Fin.addCases
                    (fun k : Fin (reluApproxBoxScanStateSize d) ↦
                      if k.val = d then 1 else 0)
                    (fun k : Fin (reluApproxBoxScanStateSize d) ↦
                      if k.val = d then -1 else 0) j *
                  reluApproxSignedEncode u j) = u (Fin.natAdd d (0 : Fin 4)) := by
            let k0 : Fin (reluApproxBoxScanStateSize d) :=
              Fin.natAdd d (0 : Fin 4)
            rw [Fin.sum_univ_add]
            simp only [Fin.addCases_left, Fin.addCases_right,
              reluApproxSignedEncode_castAdd,
              reluApproxSignedEncode_natAdd]
            have hpos :
                (∑ k : Fin (reluApproxBoxScanStateSize d),
                    (if k.val = d then 1 else 0) * relu (u k)) =
                  relu (u k0) := by
              classical
              calc
                _ = (if k0.val = d then 1 else 0) * relu (u k0) := by
                  apply Finset.sum_eq_single k0
                  · intro b _hb hbk
                    have hbval : b.val ≠ d := by
                      intro hbval
                      apply hbk
                      apply Fin.ext
                      simpa [k0] using hbval
                    simp [hbval]
                  · simp
                _ = relu (u k0) := by simp [k0]
            have hneg :
                (∑ k : Fin (reluApproxBoxScanStateSize d),
                    (if k.val = d then -1 else 0) * relu (-u k)) =
                  -relu (-u k0) := by
              classical
              calc
                _ = (if k0.val = d then -1 else 0) * relu (-u k0) := by
                  apply Finset.sum_eq_single k0
                  · intro b _hb hbk
                    have hbval : b.val ≠ d := by
                      intro hbval
                      apply hbk
                      apply Fin.ext
                      simpa [k0] using hbval
                    simp [hbval]
                  · simp
                _ = -relu (-u k0) := by simp [k0]
            rw [hpos, hneg]
            exact reluApproxSignedEncode_sub (u k0)
          simp only [reluApproxBoxScanFeatureSize]
          rw [Fin.sum_univ_add]
          simp only [Fin.addCases_left, Fin.addCases_right,
            reluApproxBoxScanAccFeatures, add_zero]
          rw [hsigned]
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp [reluApproxBoxScanAccFeatures, u,
            reluApproxBoxScanLoadedState, reluApproxBoxScanState,
            reluApproxBoxGate]
          ring
        · rename_i h
          exfalso
          apply h
          simp
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccUpdateMatrix, reluApproxBoxScanState]
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccUpdateMatrix, reluApproxBoxScanState]
    · simp [reluApproxFiniteAffineMap,
        reluApproxBoxScanAccUpdateMatrix, reluApproxBoxScanState]



/-! ## Concrete fixed-base floor decoder -/

/-- The explicit one-hidden-layer network used to decode an integer digit
away from the ramp neighborhoods of the finite integer grid. -/
noncomputable def reluApproxTruncatedFloorNet (R : ℝ) (B : ℕ) :
    FullyConnectedReLUNet 1 where
  depth := 1
  width := 2 * B
  input :=
    { weight := fun _ _ ↦ 1
      bias := fun k : Fin (2 * B) ↦
        -(((k.val / 2 + 1 : ℕ) : ℝ)) -
          (if k.val % 2 = 0 then 0 else R⁻¹) }
  hidden := Fin.elim0
  outputWeight := fun k : Fin (2 * B) ↦ if k.val % 2 = 0 then R else -R
  outputBias := 0

@[simp] theorem reluApproxTruncatedFloorNet_depth (R : ℝ) (B : ℕ) :
    (reluApproxTruncatedFloorNet R B).depth = 1 := rfl

@[simp] theorem reluApproxTruncatedFloorNet_width (R : ℝ) (B : ℕ) :
    (reluApproxTruncatedFloorNet R B).width = 2 * B := rfl

theorem reluApproxTruncatedFloorNet_realize (R : ℝ) (B : ℕ)
    (x : Fin 1 → ℝ) :
    (reluApproxTruncatedFloorNet R B).realize x =
      truncatedFloorReLUFunction R B (x 0) := by
  calc
    (reluApproxTruncatedFloorNet R B).realize x =
        ∑ j : Fin (2 * B),
          (if j.val % 2 = 0 then R else -R) *
            relu (x 0 - ((j.val / 2 + 1 : ℕ) : ℝ) -
              (if j.val % 2 = 0 then 0 else R⁻¹)) := by
      simp only [reluApproxTruncatedFloorNet, FullyConnectedReLUNet.realize,
        FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec,
        DenseLayer.apply, Fin.sum_univ_one, add_zero]
      apply Finset.sum_congr rfl
      intro j _hj
      congr 1
      congr 1
      ring
    _ = ∑ i : Fin B,
        (R * relu (x 0 - ((i.val + 1 : ℕ) : ℝ)) +
          (-R) * relu (x 0 - ((i.val + 1 : ℕ) : ℝ) - R⁻¹)) := by
      let F : Fin (2 * B) → ℝ := fun j ↦
        (if j.val % 2 = 0 then R else -R) *
          relu (x 0 - ((j.val / 2 + 1 : ℕ) : ℝ) -
            (if j.val % 2 = 0 then 0 else R⁻¹))
      let H0 : Fin B → ℝ := fun i ↦
        R * relu (x 0 - ((i.val + 1 : ℕ) : ℝ))
      let H1 : Fin B → ℝ := fun i ↦
        (-R) * relu (x 0 - ((i.val + 1 : ℕ) : ℝ) - R⁻¹)
      let e : Fin B × Fin 2 ≃ Fin (2 * B) :=
        { toFun := fun p ↦ ⟨p.2.val + 2 * p.1.val, by omega⟩
          invFun := fun j ↦
            (⟨j.val / 2, by omega⟩, ⟨j.val % 2, by omega⟩)
          left_inv := by
            intro p
            apply Prod.ext
            · apply Fin.ext
              simp
              omega
            · apply Fin.ext
              simp
          right_inv := by
            intro j
            apply Fin.ext
            simp
            omega }
      calc
        (∑ j : Fin (2 * B), F j) = ∑ p : Fin B × Fin 2, F (e p) := by
          exact (Equiv.sum_comp e F).symm
        _ = ∑ p : Fin B × Fin 2,
            (if p.2.val = 0 then H0 p.1 else H1 p.1) := by
          apply Finset.sum_congr rfl
          intro p _hp
          rcases p with ⟨i, a⟩
          fin_cases a
          · have heval : (e (i, 0)).val = 2 * i.val := by simp [e]
            simp [F, H0, H1]
            rw [heval]
            have hmod : (2 * i.val) % 2 = 0 := by omega
            have hdiv : (2 * i.val) / 2 = i.val := by omega
            rw [hmod, hdiv]
            simp
          · have heval : (e (i, 1)).val = 1 + 2 * i.val := by simp [e]
            simp [F, H0, H1]
            rw [heval]
            have hmod : (1 + 2 * i.val) % 2 = 1 := by omega
            have hdiv : (1 + 2 * i.val) / 2 = i.val := by omega
            rw [hmod, hdiv]
            simp
        _ = ∑ i : Fin B, (H0 i + H1 i) := by
          simp [Fintype.sum_prod_type, Fin.sum_univ_two]
        _ = ∑ i : Fin B,
            (R * relu (x 0 - ((i.val + 1 : ℕ) : ℝ)) +
              (-R) * relu (x 0 - ((i.val + 1 : ℕ) : ℝ) - R⁻¹)) := by
          rfl
    _ = ∑ i : Fin B, reluStepFunctionApprox R (i.val + 1 : ℝ) (x 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [reluStepFunctionApprox]
      ring
    _ = ∑ j ∈ Finset.Icc 1 B, reluStepFunctionApprox R (j : ℝ) (x 0) := by
      refine Finset.sum_bij (s := Finset.univ) (t := Finset.Icc 1 B)
        (i := fun a _ ↦ a.val + 1) ?_ ?_ ?_ ?_
      · intro a _ha
        simp
      · intro a₁ _ha₁ a₂ _ha₂ heq
        apply Fin.ext
        have heq' : a₁.val + 1 = a₂.val + 1 := by simpa using heq
        omega
      · intro j hj
        have hj' : 1 ≤ j ∧ j ≤ B := by simpa using hj
        refine ⟨⟨j - 1, by omega⟩, by simp, ?_⟩
        change (j - 1) + 1 = j
        omega
      · intro a _ha
        simpa
    _ = truncatedFloorReLUFunction R B (x 0) := rfl

private theorem reluApproxTruncatedFloorNet_realize_eq_floor_on_gap
    {R : ℝ} {B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (z : ℝ) (hz0 : 0 ≤ z) (hzB : z < (B : ℝ) + 1)
    (hgap : awayFromFiniteIntegerGrid R B z) :
    (reluApproxTruncatedFloorNet R B).realize (fun _ ↦ z) =
      (Nat.floor z : ℝ) := by
  rw [reluApproxTruncatedFloorNet_realize]
  exact
    (truncatedFloorReLUFunction_reluNetworkClass_and_eq_floor_on_away_integer_grid
      hB hR).2 z hz0 hzB hgap


/-! ## Concrete fixed-base digit/tail macro

The recursive construction does not merely evaluate a floor network.  At each
fine-grid step it must retain the decoded digit and replace the code tail `z`
by `base * z - digit`.  The following matrices embed both operations in one
two-layer signed-register macro.  The first two feature channels carry the
positive and negative parts of `base * z`; the remaining `2 * B` channels are
the explicit truncated-floor decoder above. -/

/-- Feature matrix for one fixed-base digit/tail update.  State coordinate zero
is the current code tail; coordinate one stores the most recently decoded digit. -/
private noncomputable def reluApproxFloorTailFeatureMatrix (base : ℝ) (B : ℕ) :
    Matrix (Fin (2 + 2 * B)) (Fin 2) ℝ :=
  Fin.addCases
    (fun i : Fin 2 ↦ fun j : Fin 2 ↦
      if j.val = 0 then (if i.val = 0 then base else -base) else 0)
    (fun _k : Fin (2 * B) ↦ fun j : Fin 2 ↦
      if j.val = 0 then base else 0)

/-- Feature biases for one fixed-base digit/tail update. -/
private noncomputable def reluApproxFloorTailFeatureBias (R : ℝ) (B : ℕ) :
    Fin (2 + 2 * B) → ℝ :=
  Fin.addCases (fun _ : Fin 2 ↦ 0)
    (reluApproxTruncatedFloorNet R B).input.bias

/-- Update matrix which writes the fractional remainder into coordinate zero
and the decoder output into coordinate one.  This ordering permits iteration. -/
private noncomputable def reluApproxFloorTailUpdateMatrix (R : ℝ) (B : ℕ) :
    Matrix (Fin 2) (Fin (2 + 2 * B)) ℝ :=
  fun i ↦
    Fin.addCases
      (fun q : Fin 2 ↦
        if i.val = 0 then (if q.val = 0 then 1 else -1) else 0)
      (fun k : Fin (2 * B) ↦
        if i.val = 0 then
          -(reluApproxTruncatedFloorNet R B).outputWeight k
        else
          (reluApproxTruncatedFloorNet R B).outputWeight k)

/-- The mathematical state produced by one fixed-base digit/tail update. -/
private noncomputable def reluApproxFloorTailState (R : ℝ) (B : ℕ)
    (base z : ℝ) : Fin 2 → ℝ :=
  fun i ↦
    if i.val = 0 then base * z - truncatedFloorReLUFunction R B (base * z)
    else truncatedFloorReLUFunction R B (base * z)

/-- One concrete two-layer macro simultaneously decodes the next digit and
updates the fractional code tail. -/
private theorem reluApproxFloorTailMacro_exact (base R : ℝ) (B : ℕ)
    (u : Fin 2 → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxFloorTailUpdateMatrix R B) (fun _ ↦ 0)
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxFloorTailFeatureMatrix base B)
            (reluApproxFloorTailFeatureBias R B) u i)) =
      reluApproxFloorTailState R B base (u 0) := by
  have hfloor := reluApproxTruncatedFloorNet_realize R B
    (fun _ : Fin 1 ↦ base * u 0)
  simp only [reluApproxTruncatedFloorNet, FullyConnectedReLUNet.realize,
    FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec,
    DenseLayer.apply, Fin.sum_univ_one, add_zero] at hfloor
  have hdecode :
      (∑ k : Fin (2 * B),
        if k.val % 2 = 0 then
          R * relu (base * u 0 +
            (-1 + -((k.val / 2 : ℕ) : ℝ) -
              (if k.val % 2 = 0 then 0 else R⁻¹)))
        else
          -(R * relu (base * u 0 +
            (-1 + -((k.val / 2 : ℕ) : ℝ) -
              (if k.val % 2 = 0 then 0 else R⁻¹))))) =
        truncatedFloorReLUFunction R B (base * u 0) := by
    rw [← hfloor]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs <;> push_cast <;> ring
  funext i
  fin_cases i <;>
    simp only [reluApproxFiniteAffineMap, reluApproxFloorTailUpdateMatrix,
      reluApproxFloorTailState, Fin.sum_univ_add, Fin.addCases_left,
      Fin.addCases_right, Fin.sum_univ_two, Fin.isValue, if_pos, if_false,
      zero_mul, one_mul, neg_mul, add_zero, zero_add]
  all_goals norm_num at *
  · simp [reluApproxFloorTailFeatureMatrix,
      reluApproxFloorTailFeatureBias, reluApproxTruncatedFloorNet,
      reluApproxFiniteAffineMap, Fin.sum_univ_two]
    have hrelu : relu (base * u 0) + -relu (-(base * u 0)) = base * u 0 := by
      linarith [reluApproxSignedEncode_sub (base * u 0)]
    rw [hrelu]
    rw [hdecode]
    ring
  · rw [← hfloor]
    apply Finset.sum_congr rfl
    intro k _hk
    simp [reluApproxFloorTailFeatureMatrix,
      reluApproxFloorTailFeatureBias, reluApproxTruncatedFloorNet,
      reluApproxFiniteAffineMap, Fin.sum_univ_two]

/-- At a gap-separated readout, the first state coordinate is the exact
base-expansion remainder and the second is the exact natural-number digit. -/
private theorem reluApproxFloorTailMacro_eq_floor_on_gap
    {base R : ℝ} {B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (u : Fin 2 → ℝ) (hz0 : 0 ≤ base * u 0)
    (hzB : base * u 0 < (B : ℝ) + 1)
    (hgap : awayFromFiniteIntegerGrid R B (base * u 0)) :
    reluApproxFiniteAffineMap
        (reluApproxFloorTailUpdateMatrix R B) (fun _ ↦ 0)
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxFloorTailFeatureMatrix base B)
            (reluApproxFloorTailFeatureBias R B) u i)) =
      fun i ↦
        if i.val = 0 then base * u 0 - (Nat.floor (base * u 0) : ℝ)
        else (Nat.floor (base * u 0) : ℝ) := by
  rw [reluApproxFloorTailMacro_exact]
  have hfloor : truncatedFloorReLUFunction R B (base * u 0) =
      (Nat.floor (base * u 0) : ℝ) :=
    (truncatedFloorReLUFunction_reluNetworkClass_and_eq_floor_on_away_integer_grid
      hB hR).2 (base * u 0) hz0 hzB hgap
  funext i
  simp [reluApproxFloorTailState, hfloor]

/-- Exact mathematical iteration of the fixed-base digit/tail update.  The
zeroth state contains the input tail and no decoded digit. -/
private noncomputable def reluApproxFloorTailRecursion (R : ℝ) (B : ℕ)
    (base z : ℝ) : ℕ → Fin 2 → ℝ
  | 0 => fun i ↦ if i.val = 0 then z else 0
  | t + 1 =>
      reluApproxFloorTailState R B base
        (reluApproxFloorTailRecursion R B base z t 0)

/-- Affine input map which initializes the recursive decoder with one scalar
code tail. -/
private noncomputable def reluApproxFloorTailInputMatrix :
    Matrix (Fin 2) (Fin 1) ℝ :=
  fun i _ ↦ if i.val = 0 then 1 else 0

/-- A concrete fixed-width network which performs `T` successive fixed-base
digit/tail updates and reads out the last decoded digit. -/
private noncomputable def reluApproxFloorTailDecoderNet
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ) :
    FullyConnectedReLUNet 1 :=
  reluApproxSignedMacroRecursionNet
    reluApproxFloorTailInputMatrix (fun _ ↦ 0)
    (fun _ : Fin T ↦ reluApproxFloorTailFeatureMatrix base B)
    (fun _ : Fin T ↦ reluApproxFloorTailFeatureBias R B)
    (fun _ : Fin T ↦ reluApproxFloorTailUpdateMatrix R B)
    (fun _ : Fin T ↦ fun _ ↦ 0)
    (fun i : Fin 2 ↦ if i.val = 1 then 1 else 0) 0

private theorem reluApproxFloorTailMacroRecursion_eq
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ)
    (x : Fin 1 → ℝ) (t : ℕ) (ht : t ≤ T) :
    reluApproxSignedMacroRecursion
        reluApproxFloorTailInputMatrix (fun _ ↦ 0)
        (fun _ : Fin T ↦ reluApproxFloorTailFeatureMatrix base B)
        (fun _ : Fin T ↦ reluApproxFloorTailFeatureBias R B)
        (fun _ : Fin T ↦ reluApproxFloorTailUpdateMatrix R B)
        (fun _ : Fin T ↦ fun _ ↦ 0) x t =
      reluApproxFloorTailRecursion R B base (x 0) t := by
  induction t with
  | zero =>
      funext i
      fin_cases i <;>
        simp [reluApproxSignedMacroRecursion, reluApproxFloorTailRecursion,
          reluApproxFiniteAffineMap, reluApproxFloorTailInputMatrix,
          Fin.sum_univ_one]
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxSignedMacroRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxFloorTailMacro_exact base R B
        (reluApproxFloorTailRecursion R B base (x 0) t)

@[simp] theorem reluApproxFloorTailDecoderNet_depth
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ) :
    (reluApproxFloorTailDecoderNet R B base T).depth = 2 * T + 1 := rfl

@[simp] theorem reluApproxFloorTailDecoderNet_width
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ) :
    (reluApproxFloorTailDecoderNet R B base T).width = 6 + 2 * B := by
  change (2 + 2) + (2 + 2 * B) = 6 + 2 * B
  omega

/-- Every completed pair of hidden layers carries the exact recursive tail and
last decoded digit in signed-register form. -/
private theorem reluApproxFloorTailDecoderNet_hiddenState_even
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ)
    (x : Fin 1 → ℝ) (t : ℕ) (ht : t ≤ T) :
    (reluApproxFloorTailDecoderNet R B base T).hiddenState x (2 * t) =
      reluApproxSignedWorkspaceEncode (h := 2 + 2 * B)
        (reluApproxFloorTailRecursion R B base (x 0) t) := by
  unfold reluApproxFloorTailDecoderNet
  rw [reluApproxSignedMacroRecursionNet_hiddenState_even]
  rw [reluApproxFloorTailMacroRecursion_eq R B base T x t ht]
  exact ht

/-- The decoder network output is exactly the last digit coordinate of the
fixed-base recursion. -/
private theorem reluApproxFloorTailDecoderNet_realize
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ) (x : Fin 1 → ℝ) :
    (reluApproxFloorTailDecoderNet R B base T).realize x =
      reluApproxFloorTailRecursion R B base (x 0) T 1 := by
  unfold reluApproxFloorTailDecoderNet
  rw [reluApproxSignedMacroRecursionNet_realize]
  rw [reluApproxFloorTailMacroRecursion_eq R B base T x T le_rfl]
  simp [Fin.sum_univ_two]

private theorem reluApproxFloorTailDecoderNet_parameterCount
    (R : ℝ) (B : ℕ) (base : ℝ) (T : ℕ) :
    (reluApproxFloorTailDecoderNet R B base T).parameterCount =
      fullyConnectedReLUParameterCount 1 (2 * T + 1) (6 + 2 * B) := by
  change fullyConnectedReLUParameterCount 1 (2 * T + 1)
      ((2 + 2) + (2 + 2 * B)) =
    fullyConnectedReLUParameterCount 1 (2 * T + 1) (6 + 2 * B)
  congr 1
  omega


/-! ## Coupled Taylor-correction and code-tail update -/

/-- Feature matrix for one scalar Taylor-register update coupled to a
fixed-base correction-tail read.  The state is `(tail, coefficient, digit)`. -/
private noncomputable def reluApproxTaylorCorrectionFeatureMatrix
    (base : ℝ) (B : ℕ) :
    Matrix (Fin (4 + 2 * B)) (Fin 3) ℝ :=
  Fin.addCases
    (fun i : Fin 4 ↦ fun j : Fin 3 ↦
      if j.val = 0 then
        if i.val = 0 then base else if i.val = 1 then -base else 0
      else if j.val = 1 then
        if i.val = 2 then 1 else if i.val = 3 then -1 else 0
      else 0)
    (fun _k : Fin (2 * B) ↦ fun j : Fin 3 ↦
      if j.val = 0 then base else 0)

/-- Feature biases for the coupled Taylor-correction update. -/
private noncomputable def reluApproxTaylorCorrectionFeatureBias
    (R : ℝ) (B : ℕ) : Fin (4 + 2 * B) → ℝ :=
  Fin.addCases (fun _ : Fin 4 ↦ 0)
    (reluApproxTruncatedFloorNet R B).input.bias

/-- Update matrix for
`tail' = base*tail-digit`,
`coefficient' = alpha*coefficient + scale*digit + offset`, and
`digit' = digit`. -/
private noncomputable def reluApproxTaylorCorrectionUpdateMatrix
    (R alpha scale : ℝ) (B : ℕ) :
    Matrix (Fin 3) (Fin (4 + 2 * B)) ℝ :=
  fun i ↦
    Fin.addCases
      (fun q : Fin 4 ↦
        if i.val = 0 then
          if q.val = 0 then 1 else if q.val = 1 then -1 else 0
        else if i.val = 1 then
          if q.val = 2 then alpha else if q.val = 3 then -alpha else 0
        else 0)
      (fun k : Fin (2 * B) ↦
        if i.val = 0 then
          -(reluApproxTruncatedFloorNet R B).outputWeight k
        else if i.val = 1 then
          scale * (reluApproxTruncatedFloorNet R B).outputWeight k
        else
          (reluApproxTruncatedFloorNet R B).outputWeight k)

/-- Mathematical state update implemented by the coupled correction macro. -/
private noncomputable def reluApproxTaylorCorrectionState
    (R : ℝ) (B : ℕ) (base alpha scale offset : ℝ)
    (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let digit := truncatedFloorReLUFunction R B (base * u 0)
  fun i ↦
    if i.val = 0 then base * u 0 - digit
    else if i.val = 1 then alpha * u 1 + scale * digit + offset
    else digit

/-- A concrete two-layer macro performs the signed Taylor coefficient update
and fixed-base tail shift simultaneously. -/
private theorem reluApproxTaylorCorrectionMacro_exact
    (R : ℝ) (B : ℕ) (base alpha scale offset : ℝ)
    (u : Fin 3 → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxTaylorCorrectionUpdateMatrix R alpha scale B)
        (fun i ↦ if i.val = 1 then offset else 0)
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxTaylorCorrectionFeatureMatrix base B)
            (reluApproxTaylorCorrectionFeatureBias R B) u i)) =
      reluApproxTaylorCorrectionState R B base alpha scale offset u := by
  have hfloor := reluApproxTruncatedFloorNet_realize R B
    (fun _ : Fin 1 ↦ base * u 0)
  simp only [reluApproxTruncatedFloorNet, FullyConnectedReLUNet.realize,
    FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec,
    DenseLayer.apply, Fin.sum_univ_one, add_zero] at hfloor
  have hdecode :
      (∑ k : Fin (2 * B),
        (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu (reluApproxFiniteAffineMap
            (reluApproxTaylorCorrectionFeatureMatrix base B)
            (reluApproxTaylorCorrectionFeatureBias R B) u
            (Fin.natAdd 4 k))) =
        truncatedFloorReLUFunction R B (base * u 0) := by
    rw [← hfloor]
    apply Finset.sum_congr rfl
    intro k _hk
    congr 1
    simp [reluApproxTaylorCorrectionFeatureMatrix,
      reluApproxTaylorCorrectionFeatureBias,
      reluApproxTruncatedFloorNet, reluApproxFiniteAffineMap,
      Fin.sum_univ_three]
  have htail : relu (base * u 0) - relu (-(base * u 0)) = base * u 0 :=
    reluApproxSignedEncode_sub (base * u 0)
  have hcoeff : relu (u 1) - relu (-(u 1)) = u 1 :=
    reluApproxSignedEncode_sub (u 1)
  have hdecode' :
      (∑ k : Fin (2 * B),
        (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu (base * u 0 +
            (reluApproxTruncatedFloorNet R B).input.bias k)) =
        truncatedFloorReLUFunction R B (base * u 0) := by
    simpa [reluApproxFiniteAffineMap,
      reluApproxTaylorCorrectionFeatureMatrix,
      reluApproxTaylorCorrectionFeatureBias, Fin.sum_univ_three] using hdecode
  have htail' : relu (base * u 0) + -relu (-(base * u 0)) = base * u 0 := by
    linarith
  have hcoeff' :
      alpha * relu (u 1) + -(alpha * relu (-u 1)) = alpha * u 1 := by
    calc
      alpha * relu (u 1) + -(alpha * relu (-u 1)) =
          alpha * (relu (u 1) - relu (-u 1)) := by ring
      _ = alpha * u 1 := by rw [hcoeff]
  have hscaled :
      (∑ k : Fin (2 * B),
        scale * (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu (base * u 0 +
            (reluApproxTruncatedFloorNet R B).input.bias k)) =
        scale * truncatedFloorReLUFunction R B (base * u 0) := by
    calc
      (∑ k : Fin (2 * B),
          scale * (reluApproxTruncatedFloorNet R B).outputWeight k *
            relu (base * u 0 +
              (reluApproxTruncatedFloorNet R B).input.bias k)) =
          scale * ∑ k : Fin (2 * B),
            (reluApproxTruncatedFloorNet R B).outputWeight k *
              relu (base * u 0 +
                (reluApproxTruncatedFloorNet R B).input.bias k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = scale * truncatedFloorReLUFunction R B (base * u 0) := by
        rw [hdecode']
  funext i
  fin_cases i <;>
    simp only [reluApproxFiniteAffineMap,
      reluApproxTaylorCorrectionUpdateMatrix,
      reluApproxTaylorCorrectionState, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_four,
      Fin.isValue, if_pos, add_zero]
  all_goals norm_num at *
  · simp [reluApproxTaylorCorrectionFeatureMatrix,
      reluApproxTaylorCorrectionFeatureBias,
      reluApproxFiniteAffineMap, Fin.sum_univ_three]
    rw [htail', hdecode']
    ring
  · simp [reluApproxTaylorCorrectionFeatureMatrix,
      reluApproxTaylorCorrectionFeatureBias,
      reluApproxFiniteAffineMap, Fin.sum_univ_three]
    rw [hcoeff', hscaled]
  · simpa [reluApproxFiniteAffineMap,
      reluApproxTaylorCorrectionFeatureMatrix,
      reluApproxTaylorCorrectionFeatureBias, Fin.sum_univ_three] using hdecode

/-- Mathematical recursion for a scheduled sequence of coupled Taylor
coefficient and correction-tail updates. -/
private noncomputable def reluApproxTaylorCorrectionRecursion {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ)
    (x : Fin d → ℝ) : ℕ → Fin 3 → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxTaylorCorrectionState R B base
          (alpha ⟨t, ht⟩) (scale ⟨t, ht⟩) (offset ⟨t, ht⟩)
          (reluApproxTaylorCorrectionRecursion A0 b0 R B base
            alpha scale offset x t)
      else
        reluApproxTaylorCorrectionRecursion A0 b0 R B base
          alpha scale offset x t

/-- Concrete fully connected network for a scheduled scalar Taylor register
and its fixed-base correction tail. -/
private noncomputable def reluApproxTaylorCorrectionRecursionNet {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ) : FullyConnectedReLUNet d :=
  reluApproxSignedMacroRecursionNet A0 b0
    (fun _ : Fin T ↦ reluApproxTaylorCorrectionFeatureMatrix base B)
    (fun _ : Fin T ↦ reluApproxTaylorCorrectionFeatureBias R B)
    (fun t : Fin T ↦
      reluApproxTaylorCorrectionUpdateMatrix R (alpha t) (scale t) B)
    (fun t : Fin T ↦ fun i ↦ if i.val = 1 then offset t else 0)
    (fun i : Fin 3 ↦ if i.val = 1 then 1 else 0) 0

private theorem reluApproxTaylorCorrectionMacroRecursion_eq {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    reluApproxSignedMacroRecursion A0 b0
        (fun _ : Fin T ↦ reluApproxTaylorCorrectionFeatureMatrix base B)
        (fun _ : Fin T ↦ reluApproxTaylorCorrectionFeatureBias R B)
        (fun k : Fin T ↦
          reluApproxTaylorCorrectionUpdateMatrix R (alpha k) (scale k) B)
        (fun k : Fin T ↦ fun i ↦ if i.val = 1 then offset k else 0)
        x t =
      reluApproxTaylorCorrectionRecursion A0 b0 R B base
        alpha scale offset x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxSignedMacroRecursion,
        reluApproxTaylorCorrectionRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxTaylorCorrectionMacro_exact R B base
        (alpha ⟨t, htlt⟩) (scale ⟨t, htlt⟩) (offset ⟨t, htlt⟩)
        (reluApproxTaylorCorrectionRecursion A0 b0 R B base
          alpha scale offset x t)

@[simp] theorem reluApproxTaylorCorrectionRecursionNet_depth {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ) :
    (reluApproxTaylorCorrectionRecursionNet A0 b0 R B base
      alpha scale offset).depth = 2 * T + 1 := rfl

@[simp] theorem reluApproxTaylorCorrectionRecursionNet_width {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ) :
    (reluApproxTaylorCorrectionRecursionNet A0 b0 R B base
      alpha scale offset).width = 10 + 2 * B := by
  change (3 + 3) + (4 + 2 * B) = 10 + 2 * B
  omega

/-- The even hidden states of the scheduled network are exactly the signed
encodings of the coefficient/tail recursion. -/
private theorem reluApproxTaylorCorrectionRecursionNet_hiddenState_even {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    (reluApproxTaylorCorrectionRecursionNet A0 b0 R B base
      alpha scale offset).hiddenState x (2 * t) =
      reluApproxSignedWorkspaceEncode (h := 4 + 2 * B)
        (reluApproxTaylorCorrectionRecursion A0 b0 R B base
          alpha scale offset x t) := by
  unfold reluApproxTaylorCorrectionRecursionNet
  rw [reluApproxSignedMacroRecursionNet_hiddenState_even]
  rw [reluApproxTaylorCorrectionMacroRecursion_eq
    A0 b0 R B base alpha scale offset x t ht]
  exact ht

/-- The scheduled network reads out the terminal Taylor coefficient. -/
private theorem reluApproxTaylorCorrectionRecursionNet_realize {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ) (x : Fin d → ℝ) :
    (reluApproxTaylorCorrectionRecursionNet A0 b0 R B base
      alpha scale offset).realize x =
      reluApproxTaylorCorrectionRecursion A0 b0 R B base
        alpha scale offset x T 1 := by
  unfold reluApproxTaylorCorrectionRecursionNet
  rw [reluApproxSignedMacroRecursionNet_realize]
  rw [reluApproxTaylorCorrectionMacroRecursion_eq
    A0 b0 R B base alpha scale offset x T le_rfl]
  simp [Fin.sum_univ_three]

private theorem reluApproxTaylorCorrectionRecursionNet_parameterCount {d T : ℕ}
    (A0 : Matrix (Fin 3) (Fin d) ℝ) (b0 : Fin 3 → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (alpha scale offset : Fin T → ℝ) :
    (reluApproxTaylorCorrectionRecursionNet A0 b0 R B base
      alpha scale offset).parameterCount =
      fullyConnectedReLUParameterCount d (2 * T + 1) (10 + 2 * B) := by
  change fullyConnectedReLUParameterCount d (2 * T + 1)
      ((3 + 3) + (4 + 2 * B)) =
    fullyConnectedReLUParameterCount d (2 * T + 1) (10 + 2 * B)
  congr 1
  omega


/-! ## Floor-augmented affine state updates

The full Taylor transport couples different derivative registers.  It is
therefore useful to expose the preceding scalar construction in its natural
finite-dimensional form: preserve a signed copy of every state coordinate,
read one fixed-base tail through the floor decoder, and use the decoded digit
as one additional input to an arbitrary affine state transition. -/

/-- Feature matrix consisting of signed copies of all state coordinates and
one truncated-floor decoder applied to `base * u tail`. -/
noncomputable def reluApproxFloorAffineFeatureMatrix {s : ℕ}
    (base : ℝ) (B : ℕ) (tail : Fin s) :
    Matrix (Fin ((s + s) + 2 * B)) (Fin s) ℝ :=
  Fin.addCases
    (Fin.addCases
      (fun i : Fin s ↦ fun j : Fin s ↦ if j = i then 1 else 0)
      (fun i : Fin s ↦ fun j : Fin s ↦ if j = i then -1 else 0))
    (fun _k : Fin (2 * B) ↦ fun j : Fin s ↦
      if j = tail then base else 0)

/-- Bias vector for the signed-state and floor-decoder features. -/
noncomputable def reluApproxFloorAffineFeatureBias {s : ℕ}
    (R : ℝ) (B : ℕ) : Fin ((s + s) + 2 * B) → ℝ :=
  Fin.addCases (fun _ : Fin (s + s) ↦ 0)
    (reluApproxTruncatedFloorNet R B).input.bias

/-- Output matrix for an affine state map plus a coordinatewise multiple of
the decoded floor digit. -/
noncomputable def reluApproxFloorAffineUpdateMatrix {s : ℕ}
    (R : ℝ) (B : ℕ) (P : Matrix (Fin s) (Fin s) ℝ)
    (digitCoeff : Fin s → ℝ) :
    Matrix (Fin s) (Fin ((s + s) + 2 * B)) ℝ :=
  fun i ↦
    Fin.addCases
      (Fin.addCases (fun j : Fin s ↦ P i j) (fun j : Fin s ↦ -P i j))
      (fun k : Fin (2 * B) ↦
        digitCoeff i * (reluApproxTruncatedFloorNet R B).outputWeight k)

/-- Mathematical update represented by the floor-augmented affine macro. -/
noncomputable def reluApproxFloorAffineState {s : ℕ}
    (R : ℝ) (B : ℕ) (base : ℝ) (tail : Fin s)
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (u : Fin s → ℝ) : Fin s → ℝ :=
  fun i ↦ reluApproxFiniteAffineMap P bias u i +
    digitCoeff i * truncatedFloorReLUFunction R B (base * u tail)

/-- Exact compiler law for an arbitrary affine state transition augmented by
one fixed-base floor read.  This is the finite-dimensional primitive needed
for coupled Taylor transport. -/
theorem reluApproxFloorAffineMacro_exact {s : ℕ}
    (R : ℝ) (B : ℕ) (base : ℝ) (tail : Fin s)
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (u : Fin s → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxFloorAffineUpdateMatrix R B P digitCoeff) bias
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxFloorAffineFeatureMatrix base B tail)
            (reluApproxFloorAffineFeatureBias R B) u i)) =
      reluApproxFloorAffineState R B base tail P bias digitCoeff u := by
  have hsigned :
      (fun q : Fin (s + s) ↦ relu
        (reluApproxFiniteAffineMap
          (reluApproxFloorAffineFeatureMatrix base B tail)
          (reluApproxFloorAffineFeatureBias R B) u
          (Fin.castAdd (2 * B) q))) =
        reluApproxSignedEncode u := by
    funext q
    refine Fin.addCases ?_ ?_ q
    · intro j
      rw [reluApproxSignedEncode_castAdd]
      simp [reluApproxFiniteAffineMap,
        reluApproxFloorAffineFeatureMatrix,
        reluApproxFloorAffineFeatureBias]
    · intro j
      rw [reluApproxSignedEncode_natAdd]
      simp only [reluApproxFiniteAffineMap,
        reluApproxFloorAffineFeatureMatrix,
        reluApproxFloorAffineFeatureBias, Fin.addCases_left]
      rw [Fin.addCases_right]
      simp
  have hdecoderFeature : ∀ k : Fin (2 * B),
      reluApproxFiniteAffineMap
          (reluApproxFloorAffineFeatureMatrix base B tail)
          (reluApproxFloorAffineFeatureBias R B) u
          (Fin.natAdd (s + s) k) =
        base * u tail + (reluApproxTruncatedFloorNet R B).input.bias k := by
    intro k
    simp [reluApproxFiniteAffineMap,
      reluApproxFloorAffineFeatureMatrix,
      reluApproxFloorAffineFeatureBias]
  have hdecode :
      (∑ k : Fin (2 * B),
        (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu
            (reluApproxFiniteAffineMap
              (reluApproxFloorAffineFeatureMatrix base B tail)
              (reluApproxFloorAffineFeatureBias R B) u
              (Fin.natAdd (s + s) k))) =
        truncatedFloorReLUFunction R B (base * u tail) := by
    have hfloor := reluApproxTruncatedFloorNet_realize R B
      (fun _ : Fin 1 ↦ base * u tail)
    simp only [reluApproxTruncatedFloorNet, FullyConnectedReLUNet.realize,
      FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec,
      DenseLayer.apply, Fin.sum_univ_one, add_zero] at hfloor
    rw [← hfloor]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hdecoderFeature k]
    simp [reluApproxTruncatedFloorNet]
  funext i
  rw [reluApproxFiniteAffineMap]
  rw [Fin.sum_univ_add]
  simp only [reluApproxFloorAffineUpdateMatrix,
    Fin.addCases_left, Fin.addCases_right]
  have hstatePart :
      (∑ q : Fin (s + s),
        Fin.addCases (fun j : Fin s ↦ P i j) (fun j : Fin s ↦ -P i j) q *
          relu
            (reluApproxFiniteAffineMap
              (reluApproxFloorAffineFeatureMatrix base B tail)
              (reluApproxFloorAffineFeatureBias R B) u
              (Fin.castAdd (2 * B) q))) =
        ∑ j : Fin s, P i j * u j := by
    calc
      (∑ q : Fin (s + s),
          Fin.addCases (fun j : Fin s ↦ P i j) (fun j : Fin s ↦ -P i j) q *
            relu
              (reluApproxFiniteAffineMap
                (reluApproxFloorAffineFeatureMatrix base B tail)
                (reluApproxFloorAffineFeatureBias R B) u
                (Fin.castAdd (2 * B) q))) =
          ∑ q : Fin (s + s),
            Fin.addCases (fun j : Fin s ↦ P i j) (fun j : Fin s ↦ -P i j) q *
              reluApproxSignedEncode u q := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [congrFun hsigned q]
      _ = ∑ j : Fin s, P i j * u j :=
        reluApprox_sum_signedEncode (P i) u
  rw [hstatePart]
  have hdigitPart :
      (∑ k : Fin (2 * B),
        digitCoeff i * (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu
            (reluApproxFiniteAffineMap
              (reluApproxFloorAffineFeatureMatrix base B tail)
              (reluApproxFloorAffineFeatureBias R B) u
              (Fin.natAdd (s + s) k))) =
        digitCoeff i * truncatedFloorReLUFunction R B (base * u tail) := by
    calc
      (∑ k : Fin (2 * B),
          digitCoeff i * (reluApproxTruncatedFloorNet R B).outputWeight k *
            relu
              (reluApproxFiniteAffineMap
                (reluApproxFloorAffineFeatureMatrix base B tail)
                (reluApproxFloorAffineFeatureBias R B) u
                (Fin.natAdd (s + s) k))) =
          digitCoeff i * ∑ k : Fin (2 * B),
            (reluApproxTruncatedFloorNet R B).outputWeight k *
              relu
                (reluApproxFiniteAffineMap
                  (reluApproxFloorAffineFeatureMatrix base B tail)
                  (reluApproxFloorAffineFeatureBias R B) u
                  (Fin.natAdd (s + s) k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = digitCoeff i * truncatedFloorReLUFunction R B (base * u tail) := by
        rw [hdecode]
  rw [hdigitPart]
  simp only [reluApproxFloorAffineState, reluApproxFiniteAffineMap]
  ring

/-- Mathematical recursion for a scheduled sequence of floor-augmented
affine state transitions.  Each step may read a different tail coordinate and
apply a different affine transport to the complete state. -/
private noncomputable def reluApproxFloorAffineRecursion {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) : ℕ → Fin s → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxFloorAffineState R B base (tail ⟨t, ht⟩)
          (P ⟨t, ht⟩) (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩)
          (reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
            digitCoeff x t)
      else
        reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x t

/-- Concrete fully connected ReLU network implementing a scheduled sequence
of floor-augmented affine state transitions. -/
private noncomputable def reluApproxFloorAffineRecursionNet {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    FullyConnectedReLUNet d :=
  reluApproxSignedMacroRecursionNet A0 b0
    (fun t : Fin T ↦ reluApproxFloorAffineFeatureMatrix base B (tail t))
    (fun _ : Fin T ↦ reluApproxFloorAffineFeatureBias R B)
    (fun t : Fin T ↦
      reluApproxFloorAffineUpdateMatrix R B (P t) (digitCoeff t))
    bias outputWeight outputBias

private theorem reluApproxFloorAffineMacroRecursion_eq {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    reluApproxSignedMacroRecursion A0 b0
        (fun k : Fin T ↦ reluApproxFloorAffineFeatureMatrix base B (tail k))
        (fun _ : Fin T ↦ reluApproxFloorAffineFeatureBias R B)
        (fun k : Fin T ↦
          reluApproxFloorAffineUpdateMatrix R B (P k) (digitCoeff k))
        bias x t =
      reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
        digitCoeff x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxSignedMacroRecursion,
        reluApproxFloorAffineRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxFloorAffineMacro_exact R B base (tail ⟨t, htlt⟩)
        (P ⟨t, htlt⟩) (bias ⟨t, htlt⟩) (digitCoeff ⟨t, htlt⟩)
        (reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x t)

@[simp] theorem reluApproxFloorAffineRecursionNet_depth {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).depth = 2 * T + 1 := rfl

@[simp] theorem reluApproxFloorAffineRecursionNet_width {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).width = 4 * s + 2 * B := by
  change (s + s) + ((s + s) + 2 * B) = 4 * s + 2 * B
  omega

/-- Every even hidden state is the signed workspace encoding of the exact
floor-augmented affine recursion. -/
private theorem reluApproxFloorAffineRecursionNet_hiddenState_even {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).hiddenState x (2 * t) =
      reluApproxSignedWorkspaceEncode (h := (s + s) + 2 * B)
        (reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x t) := by
  unfold reluApproxFloorAffineRecursionNet
  have hstate := reluApproxSignedMacroRecursionNet_hiddenState_even
    A0 b0
    (fun k : Fin T ↦ reluApproxFloorAffineFeatureMatrix base B (tail k))
    (fun _ : Fin T ↦ reluApproxFloorAffineFeatureBias R B)
    (fun k : Fin T ↦
      reluApproxFloorAffineUpdateMatrix R B (P k) (digitCoeff k))
    bias outputWeight outputBias x t ht
  rw [hstate]
  rw [reluApproxFloorAffineMacroRecursion_eq
    A0 b0 R B base tail P bias digitCoeff x t ht]

/-- Exact terminal output formula for the concrete scheduled network. -/
private theorem reluApproxFloorAffineRecursionNet_realize {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).realize x =
      (∑ i : Fin s, outputWeight i *
        reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x T i) + outputBias := by
  unfold reluApproxFloorAffineRecursionNet
  rw [reluApproxSignedMacroRecursionNet_realize]
  rw [reluApproxFloorAffineMacroRecursion_eq
    A0 b0 R B base tail P bias digitCoeff x T le_rfl]

private theorem reluApproxFloorAffineRecursionNet_parameterCount {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).parameterCount =
      fullyConnectedReLUParameterCount d (2 * T + 1) (4 * s + 2 * B) := by
  change fullyConnectedReLUParameterCount d (2 * T + 1)
      ((s + s) + ((s + s) + 2 * B)) =
    fullyConnectedReLUParameterCount d (2 * T + 1) (4 * s + 2 * B)
  congr 1
  omega

/-- Pad the concrete floor-augmented affine recursion network to prescribed
depth and width budgets without changing its terminal affine readout. -/
private theorem exists_reluApproxFloorAffineRecursionNet_exactDepth
    {d s T D W : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (hdepth : 2 * T + 1 ≤ D) (hwidth : 4 * s + 2 * B ≤ W) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = D ∧ N.width ≤ W ∧
        N.parameterCount ≤ fullyConnectedReLUParameterCount d D W ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            (∑ i : Fin s, outputWeight i *
              reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
                digitCoeff x T i) + outputBias := by
  have hworkspace : (s + s) + ((s + s) + 2 * B) ≤ W := by
    omega
  rcases exists_reluApproxSignedMacroRecursionNet_exactDepth
      A0 b0
      (fun t : Fin T ↦ reluApproxFloorAffineFeatureMatrix base B (tail t))
      (fun _ : Fin T ↦ reluApproxFloorAffineFeatureBias R B)
      (fun t : Fin T ↦
        reluApproxFloorAffineUpdateMatrix R B (P t) (digitCoeff t))
      bias outputWeight outputBias hdepth hworkspace with
    ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x
  rw [hNrealize]
  rw [reluApproxFloorAffineMacroRecursion_eq
    A0 b0 R B base tail P bias digitCoeff x T le_rfl]

/-- Arrange `q` two-layer floor-affine macros per cell and pad to the exact
shallow ReLU block depth `cells * (2*q + 1)`.  The spare layer in each cell
absorbs the initial/final alignment while preserving fixed width. -/
private theorem exists_reluApproxFloorAffineBlockScheduleNet
    {d s cells q : ℕ} (hCells : 0 < cells)
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (R : ℝ) (B : ℕ) (base : ℝ)
    (tail : Fin (cells * q) → Fin s)
    (P : Fin (cells * q) → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin (cells * q) → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = cells * (2 * q + 1) ∧
        N.width ≤ 4 * s + 2 * B ∧
        N.parameterCount ≤
          fullyConnectedReLUParameterCount d (cells * (2 * q + 1))
            (4 * s + 2 * B) ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            (∑ i : Fin s, outputWeight i *
              reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
                digitCoeff x (cells * q) i) + outputBias := by
  have hdepth : 2 * (cells * q) + 1 ≤ cells * (2 * q + 1) := by
    calc
      2 * (cells * q) + 1 = 2 * cells * q + 1 := by ring
      _ ≤ 2 * cells * q + cells :=
        Nat.add_le_add_left (Nat.succ_le_iff.mpr hCells) (2 * cells * q)
      _ = cells * (2 * q + 1) := by ring
  exact exists_reluApproxFloorAffineRecursionNet_exactDepth
    A0 b0 R B base tail P bias digitCoeff outputWeight outputBias
    hdepth le_rfl

/-- Ideal integer-floor version of one floor-augmented affine update. -/
private noncomputable def reluApproxFloorAffineIdealState {s : ℕ}
    (base : ℝ) (tail : Fin s)
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (u : Fin s → ℝ) : Fin s → ℝ :=
  fun i ↦ reluApproxFiniteAffineMap P bias u i +
    digitCoeff i * (Nat.floor (base * u tail) : ℝ)

/-- On the decoder's valid range and away from its ramps, the concrete
two-layer macro performs the ideal integer-floor transition exactly. -/
private theorem reluApproxFloorAffineMacro_eq_ideal_on_gap {s : ℕ}
    {R : ℝ} {B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (base : ℝ) (tail : Fin s)
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (u : Fin s → ℝ)
    (hz0 : 0 ≤ base * u tail) (hzB : base * u tail < (B : ℝ) + 1)
    (hgap : awayFromFiniteIntegerGrid R B (base * u tail)) :
    reluApproxFiniteAffineMap
        (reluApproxFloorAffineUpdateMatrix R B P digitCoeff) bias
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxFloorAffineFeatureMatrix base B tail)
            (reluApproxFloorAffineFeatureBias R B) u i)) =
      reluApproxFloorAffineIdealState base tail P bias digitCoeff u := by
  rw [reluApproxFloorAffineMacro_exact]
  have hfloor : truncatedFloorReLUFunction R B (base * u tail) =
      (Nat.floor (base * u tail) : ℝ) :=
    (truncatedFloorReLUFunction_reluNetworkClass_and_eq_floor_on_away_integer_grid
      hB hR).2 (base * u tail) hz0 hzB hgap
  funext i
  simp only [reluApproxFloorAffineState,
    reluApproxFloorAffineIdealState]
  rw [hfloor]

/-- Paper-style base-tail hypotheses imply that the concrete macro decodes
the prescribed next digit.  The positive finite tail is the separation device
used in the shallow ReLU recursive correction code. -/
private theorem reluApproxFloorAffineMacro_eq_of_bounded_baseTail {s : ℕ}
    (dExp : ℝ) (c : ℕ) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : ℕ) (hbase : 4 + 2 * c ≤ baseNat)
    (aNext : ℕ) (haLower : 1 ≤ aNext) (haUpper : aNext ≤ 2 * c + 3)
    (tailLength : ℕ) (hTailLength : 1 ≤ tailLength)
    (tailDigit : Fin tailLength → ℕ)
    (hTailLower : ∀ j : Fin tailLength, 1 ≤ tailDigit j)
    (hTailUpper : ∀ j : Fin tailLength, tailDigit j ≤ 2 * c + 3)
    (floorBound : ℕ) (hFloorBound : floorBound + 1 = baseNat)
    (R : ℝ) (hR : 0 < R)
    (hRsep : 1 / R < (baseNat : ℝ) ^ (-(tailLength : ℤ)))
    (stateTail : Fin s)
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (u : Fin s → ℝ)
    (hcode : (baseNat : ℝ) * u stateTail =
      (aNext : ℝ) + ∑ j : Fin tailLength,
        (tailDigit j : ℝ) / (baseNat : ℝ) ^ (j.val + 1)) :
    reluApproxFiniteAffineMap
        (reluApproxFloorAffineUpdateMatrix R floorBound P digitCoeff) bias
        (fun i ↦ relu
          (reluApproxFiniteAffineMap
            (reluApproxFloorAffineFeatureMatrix
              (baseNat : ℝ) floorBound stateTail)
            (reluApproxFloorAffineFeatureBias R floorBound) u i)) =
      fun i ↦ reluApproxFiniteAffineMap P bias u i +
        digitCoeff i * (aNext : ℝ) := by
  let signedDigit : ℤ := (aNext : ℤ) - (c + 2 : ℤ)
  have hshift : (aNext : ℤ) = signedDigit + (c + 2 : ℤ) := by
    dsimp [signedDigit]
    ring
  rcases reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
      dExp c hc baseNat hbase aNext signedDigit hshift haLower haUpper
      tailLength hTailLength tailDigit hTailLower hTailUpper
      ((baseNat : ℝ) * u stateTail) hcode floorBound hFloorBound R hR hRsep with
    ⟨_hgap, _hclass, htruncated, hfloor, _hsigned⟩
  rw [reluApproxFloorAffineMacro_exact]
  funext i
  simp only [reluApproxFloorAffineState]
  rw [htruncated, hfloor]

/-- Ideal scheduled recursion obtained by replacing every truncated ReLU
floor read by the corresponding natural-number floor. -/
private noncomputable def reluApproxFloorAffineIdealRecursion {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (base : ℝ) (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) : ℕ → Fin s → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxFloorAffineIdealState base (tail ⟨t, ht⟩)
          (P ⟨t, ht⟩) (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩)
          (reluApproxFloorAffineIdealRecursion A0 b0 base tail P bias
            digitCoeff x t)
      else
        reluApproxFloorAffineIdealRecursion A0 b0 base tail P bias
          digitCoeff x t

/-- If every scheduled decoder input stays in range and away from its ramp
intervals, the concrete ReLU recursion agrees with the ideal floor recursion
at every time up to `T`. -/
private theorem reluApproxFloorAffineRecursion_eq_ideal_on_gap {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    {R : ℝ} {B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (base : ℝ) (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ)
    (hvalid : ∀ k : Fin T,
      let z := base *
        reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x k.val (tail k)
      0 ≤ z ∧ z < (B : ℝ) + 1 ∧ awayFromFiniteIntegerGrid R B z)
    (t : ℕ) (ht : t ≤ T) :
    reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
        digitCoeff x t =
      reluApproxFloorAffineIdealRecursion A0 b0 base tail P bias
        digitCoeff x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      let k : Fin T := ⟨t, htlt⟩
      have hk := hvalid k
      dsimp only at hk
      have hfloor :
          truncatedFloorReLUFunction R B
              (base * reluApproxFloorAffineRecursion A0 b0 R B base
                tail P bias digitCoeff x t (tail k)) =
            (Nat.floor
              (base * reluApproxFloorAffineRecursion A0 b0 R B base
                tail P bias digitCoeff x t (tail k)) : ℝ) :=
        (truncatedFloorReLUFunction_reluNetworkClass_and_eq_floor_on_away_integer_grid
          hB hR).2 _ hk.1 hk.2.1 hk.2.2
      rw [reluApproxFloorAffineRecursion,
        reluApproxFloorAffineIdealRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)] at hfloor ⊢
      funext i
      simp only [reluApproxFloorAffineState,
        reluApproxFloorAffineIdealState]
      rw [hfloor]

/-- One affine state transition driven by an explicitly supplied natural
digit. -/
noncomputable def reluApproxFloorAffineDigitState {s : ℕ}
    (P : Matrix (Fin s) (Fin s) ℝ) (bias digitCoeff : Fin s → ℝ)
    (digit : ℕ) (u : Fin s → ℝ) : Fin s → ℝ :=
  fun i ↦ reluApproxFiniteAffineMap P bias u i + digitCoeff i * (digit : ℝ)

/-- Scheduled affine recursion driven by a prescribed sequence of natural
digits. -/
private noncomputable def reluApproxFloorAffineDigitRecursion {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (digit : Fin T → ℕ) (x : Fin d → ℝ) : ℕ → Fin s → ℝ
  | 0 => reluApproxFiniteAffineMap A0 b0 x
  | t + 1 =>
      if ht : t < T then
        reluApproxFloorAffineDigitState (P ⟨t, ht⟩)
          (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩) (digit ⟨t, ht⟩)
          (reluApproxFloorAffineDigitRecursion A0 b0 P bias digitCoeff
            digit x t)
      else
        reluApproxFloorAffineDigitRecursion A0 b0 P bias digitCoeff
          digit x t

/-- A paper-style positive base-tail certificate at every step identifies the
concrete truncated-floor recursion with its prescribed digit recursion.  One
extra positive tail block supplies separation even for the last used digit. -/
private theorem reluApproxFloorAffineRecursion_eq_digit_of_bounded_baseTail
    {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (dExp : ℝ) (c : ℕ) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : ℕ) (hbase : 4 + 2 * c ≤ baseNat)
    (floorBound : ℕ) (hFloorBound : floorBound + 1 = baseNat)
    (R : ℝ) (hR : 0 < R)
    (tailLength : Fin T → ℕ)
    (hTailLength : ∀ k : Fin T, 1 ≤ tailLength k)
    (hRsep : ∀ k : Fin T,
      1 / R < (baseNat : ℝ) ^ (-(tailLength k : ℤ)))
    (stateTail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (digit : Fin T → ℕ)
    (tailDigit : ∀ k : Fin T, Fin (tailLength k) → ℕ)
    (hDigitLower : ∀ k : Fin T, 1 ≤ digit k)
    (hDigitUpper : ∀ k : Fin T, digit k ≤ 2 * c + 3)
    (hTailLower : ∀ k : Fin T, ∀ j : Fin (tailLength k), 1 ≤ tailDigit k j)
    (hTailUpper : ∀ k : Fin T, ∀ j : Fin (tailLength k),
      tailDigit k j ≤ 2 * c + 3)
    (x : Fin d → ℝ)
    (hcode : ∀ k : Fin T,
      (baseNat : ℝ) *
          reluApproxFloorAffineRecursion A0 b0 R floorBound
            (baseNat : ℝ) stateTail P bias digitCoeff x k.val (stateTail k) =
        (digit k : ℝ) + ∑ j : Fin (tailLength k),
          (tailDigit k j : ℝ) / (baseNat : ℝ) ^ (j.val + 1))
    (t : ℕ) (ht : t ≤ T) :
    reluApproxFloorAffineRecursion A0 b0 R floorBound
        (baseNat : ℝ) stateTail P bias digitCoeff x t =
      reluApproxFloorAffineDigitRecursion A0 b0 P bias digitCoeff
        digit x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      let k : Fin T := ⟨t, htlt⟩
      let signedDigit : ℤ := (digit k : ℤ) - (c + 2 : ℤ)
      have hshift : (digit k : ℤ) = signedDigit + (c + 2 : ℤ) := by
        dsimp [signedDigit]
        ring
      rcases reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
          dExp c hc baseNat hbase (digit k) signedDigit hshift
          (hDigitLower k) (hDigitUpper k) (tailLength k) (hTailLength k)
          (tailDigit k) (hTailLower k) (hTailUpper k)
          ((baseNat : ℝ) *
            reluApproxFloorAffineRecursion A0 b0 R floorBound
              (baseNat : ℝ) stateTail P bias digitCoeff x t (stateTail k))
          (hcode k) floorBound hFloorBound R hR (hRsep k) with
        ⟨_hgap, _hclass, htruncated, hfloor, _hsigned⟩
      rw [ih (Nat.le_of_succ_le ht)] at htruncated hfloor
      rw [reluApproxFloorAffineRecursion,
        reluApproxFloorAffineDigitRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      funext i
      simp only [reluApproxFloorAffineState,
        reluApproxFloorAffineDigitState]
      rw [htruncated, hfloor]

/-- Terminal network readout in terms of the prescribed paper digits, under
the stepwise positive base-tail certificates. -/
private theorem reluApproxFloorAffineRecursionNet_realize_digit_of_bounded_baseTail
    {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    (dExp : ℝ) (c : ℕ) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : ℕ) (hbase : 4 + 2 * c ≤ baseNat)
    (floorBound : ℕ) (hFloorBound : floorBound + 1 = baseNat)
    (R : ℝ) (hR : 0 < R)
    (tailLength : Fin T → ℕ)
    (hTailLength : ∀ k : Fin T, 1 ≤ tailLength k)
    (hRsep : ∀ k : Fin T,
      1 / R < (baseNat : ℝ) ^ (-(tailLength k : ℤ)))
    (stateTail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (digit : Fin T → ℕ)
    (tailDigit : ∀ k : Fin T, Fin (tailLength k) → ℕ)
    (hDigitLower : ∀ k : Fin T, 1 ≤ digit k)
    (hDigitUpper : ∀ k : Fin T, digit k ≤ 2 * c + 3)
    (hTailLower : ∀ k : Fin T, ∀ j : Fin (tailLength k), 1 ≤ tailDigit k j)
    (hTailUpper : ∀ k : Fin T, ∀ j : Fin (tailLength k),
      tailDigit k j ≤ 2 * c + 3)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ)
    (hcode : ∀ k : Fin T,
      (baseNat : ℝ) *
          reluApproxFloorAffineRecursion A0 b0 R floorBound
            (baseNat : ℝ) stateTail P bias digitCoeff x k.val (stateTail k) =
        (digit k : ℝ) + ∑ j : Fin (tailLength k),
          (tailDigit k j : ℝ) / (baseNat : ℝ) ^ (j.val + 1)) :
    (reluApproxFloorAffineRecursionNet A0 b0 R floorBound
      (baseNat : ℝ) stateTail P bias digitCoeff outputWeight outputBias).realize x =
      (∑ i : Fin s, outputWeight i *
        reluApproxFloorAffineDigitRecursion A0 b0 P bias digitCoeff
          digit x T i) + outputBias := by
  rw [reluApproxFloorAffineRecursionNet_realize]
  rw [reluApproxFloorAffineRecursion_eq_digit_of_bounded_baseTail
    A0 b0 dExp c hc baseNat hbase floorBound hFloorBound R hR
    tailLength hTailLength hRsep stateTail P bias digitCoeff digit tailDigit
    hDigitLower hDigitUpper hTailLower hTailUpper x hcode T le_rfl]

/-- Under the stepwise gap assumptions, the concrete network's output is an
arbitrary affine readout of the ideal integer-floor recursion. -/
private theorem reluApproxFloorAffineRecursionNet_realize_ideal_on_gap {d s T : ℕ}
    (A0 : Matrix (Fin s) (Fin d) ℝ) (b0 : Fin s → ℝ)
    {R : ℝ} {B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (base : ℝ) (tail : Fin T → Fin s)
    (P : Fin T → Matrix (Fin s) (Fin s) ℝ)
    (bias digitCoeff : Fin T → Fin s → ℝ)
    (outputWeight : Fin s → ℝ) (outputBias : ℝ)
    (x : Fin d → ℝ)
    (hvalid : ∀ k : Fin T,
      let z := base *
        reluApproxFloorAffineRecursion A0 b0 R B base tail P bias
          digitCoeff x k.val (tail k)
      0 ≤ z ∧ z < (B : ℝ) + 1 ∧ awayFromFiniteIntegerGrid R B z) :
    (reluApproxFloorAffineRecursionNet A0 b0 R B base tail P bias
      digitCoeff outputWeight outputBias).realize x =
      (∑ i : Fin s, outputWeight i *
        reluApproxFloorAffineIdealRecursion A0 b0 base tail P bias
          digitCoeff x T i) + outputBias := by
  rw [reluApproxFloorAffineRecursionNet_realize]
  rw [reluApproxFloorAffineRecursion_eq_ideal_on_gap
    A0 b0 hR hB base tail P bias digitCoeff x hvalid T le_rfl]


/-! ## Vector-valued coarse-cell scan

The first paper pass selects several values at once: the coarse left endpoint,
the initial Taylor jet, and one correction-code tail for every Taylor register.
The scalar scan above is therefore lifted to a fixed finite payload dimension.
The dimension may depend on `d` and the Taylor order, but not on the grid
resolution. -/

/-- State size for the input, a vector accumulator, one violation register,
and positive/negative copies of the current payload. -/
def reluApproxVectorBoxScanStateSize (d m : ℕ) : ℕ :=
  d + (m + (1 + (m + m)))

/-- Common feature size of the two vector box-scan macros. -/
def reluApproxVectorBoxScanFeatureSize (d m : ℕ) : ℕ :=
  let s := reluApproxVectorBoxScanStateSize d m
  (s + s) + ((d + d) + (m + m))

/-- Canonical state between boxes. -/
noncomputable def reluApproxVectorBoxScanState {d m : ℕ}
    (x : Fin d → ℝ) (acc : Fin m → ℝ) :
    Fin (reluApproxVectorBoxScanStateSize d m) → ℝ :=
  Fin.addCases x <| Fin.addCases acc <|
    Fin.addCases (fun _ : Fin 1 ↦ 0) <|
      Fin.addCases (fun _ : Fin m ↦ 0) (fun _ : Fin m ↦ 0)

/-- State after loading one box and its vector payload. -/
private noncomputable def reluApproxVectorBoxScanLoadedState {d m : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ)
    (payload acc : Fin m → ℝ) :
    Fin (reluApproxVectorBoxScanStateSize d m) → ℝ :=
  Fin.addCases x <| Fin.addCases acc <|
    Fin.addCases (fun _ : Fin 1 ↦ reluApproxBoxViolation R lower upper x) <|
      Fin.addCases (fun k : Fin m ↦ relu (payload k))
        (fun k : Fin m ↦ relu (-payload k))

/-- Decode a state coordinate from the signed-copy prefix of a feature vector. -/
private noncomputable def reluApproxVectorBoxScanDecodeRow (d m : ℕ)
    (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases
    (Fin.addCases (fun j : Fin s ↦ if j = i then 1 else 0)
      (fun j : Fin s ↦ if j = i then -1 else 0))
    (fun _ ↦ 0)

/-- The signed-copy decode row evaluates to the original state coordinate. -/
private theorem reluApproxVectorBoxScanDecodeRow_dot {d m : ℕ}
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ)
    (v : Fin ((d + d) + (m + m)) → ℝ)
    (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
    (∑ j : Fin (reluApproxVectorBoxScanFeatureSize d m),
        reluApproxVectorBoxScanDecodeRow d m i j *
          Fin.addCases (reluApproxSignedEncode u) v j) = u i := by
  classical
  simp only [reluApproxVectorBoxScanFeatureSize,
    reluApproxVectorBoxScanDecodeRow, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [Fin.addCases_left, Fin.addCases_right,
    reluApproxSignedEncode_castAdd, reluApproxSignedEncode_natAdd]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · simpa [sub_eq_add_neg] using reluApproxSignedEncode_sub (u i)
  · intro b _hb hbi
    simp [hbi]
  · simp
  · intro b _hb hbi
    simp [hbi]
  · simp

/-- Feature matrix of the vector-payload load macro. -/
private noncomputable def reluApproxVectorBoxScanLoadFeatureMatrix (d m : ℕ) :
    Matrix (Fin (reluApproxVectorBoxScanFeatureSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases (reluApproxBoxScanCopyRows s) <|
    Fin.addCases
      (Fin.addCases
        (fun q j ↦ if j.val = q.val then -1 else 0)
        (fun q j ↦ if j.val = q.val then 1 else 0))
      (fun _ _ ↦ 0)

/-- Bias of the vector-payload load macro. -/
private noncomputable def reluApproxVectorBoxScanLoadFeatureBias {d m : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : Fin m → ℝ) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases (fun _ : Fin (s + s) ↦ 0) <|
    Fin.addCases
      (Fin.addCases (fun q ↦ lower q + R⁻¹) (fun q ↦ -upper q + R⁻¹))
      (Fin.addCases (fun k ↦ payload k) (fun k ↦ -payload k))

/-- Mathematical feature vector of the load macro. -/
private noncomputable def reluApproxVectorBoxScanLoadFeatures {d m : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : Fin m → ℝ)
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  Fin.addCases (reluApproxSignedEncode u) <|
    Fin.addCases
      (Fin.addCases
        (fun q : Fin d ↦ relu (lower q + R⁻¹ - u (Fin.castAdd _ q)))
        (fun q : Fin d ↦ relu (u (Fin.castAdd _ q) - upper q + R⁻¹)))
      (Fin.addCases (fun k : Fin m ↦ relu (payload k))
        (fun k : Fin m ↦ relu (-payload k)))

/-- The load feature matrix produces the advertised feature vector. -/
private theorem reluApproxVectorBoxScanLoadFeatures_exact {d m : ℕ}
    (R : ℝ) (lower upper : Fin d → ℝ) (payload : Fin m → ℝ)
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxVectorBoxScanLoadFeatureMatrix d m)
      (reluApproxVectorBoxScanLoadFeatureBias R lower upper payload) u i)) =
      reluApproxVectorBoxScanLoadFeatures R lower upper payload u := by
  classical
  let s := reluApproxVectorBoxScanStateSize d m
  have hsum_pos (k : Fin s) :
      (∑ j : Fin s, (if k = j then 1 else 0) * u j) = u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  have hsum_neg (k : Fin s) :
      (∑ j : Fin s, (if k = j then -1 else 0) * u j) = -u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  have hsum_coord_neg (q : Fin d) :
      (∑ j : Fin s, (if j.val = q.val then -1 else 0) * u j) =
        -u (Fin.castAdd (m + (1 + (m + m))) q) := by
    let k : Fin s := Fin.castAdd (m + (1 + (m + m))) q
    have hiff : ∀ j : Fin s, j.val = q.val ↔ j = k := by
      intro j
      constructor
      · intro h
        apply Fin.ext
        simpa [k] using h
      · intro h
        simpa [h, k]
    simp_rw [hiff]
    simpa [k, eq_comm] using hsum_neg k
  have hsum_coord_pos (q : Fin d) :
      (∑ j : Fin s, (if j.val = q.val then 1 else 0) * u j) =
        u (Fin.castAdd (m + (1 + (m + m))) q) := by
    let k : Fin s := Fin.castAdd (m + (1 + (m + m))) q
    have hiff : ∀ j : Fin s, j.val = q.val ↔ j = k := by
      intro j
      constructor
      · intro h
        apply Fin.ext
        simpa [k] using h
      · intro h
        simpa [h, k]
    simp_rw [hiff]
    simpa [k, eq_comm] using hsum_pos k
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanLoadFeatureMatrix,
        reluApproxVectorBoxScanLoadFeatureBias,
        reluApproxVectorBoxScanLoadFeatures,
        reluApproxBoxScanCopyRows, Fin.addCases_left, add_zero]
      rw [hsum_pos]
      exact (reluApproxSignedEncode_castAdd u k).symm
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanLoadFeatureMatrix,
        reluApproxVectorBoxScanLoadFeatureBias,
        reluApproxVectorBoxScanLoadFeatures,
        reluApproxBoxScanCopyRows, Fin.addCases_left,
        Fin.addCases_right, add_zero]
      rw [hsum_neg]
      exact (reluApproxSignedEncode_natAdd u k).symm
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanLoadFeatureMatrix,
          reluApproxVectorBoxScanLoadFeatureBias,
          reluApproxVectorBoxScanLoadFeatures,
          Fin.addCases_left, Fin.addCases_right, add_zero]
        rw [hsum_coord_neg]
        congr 1
        ring
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanLoadFeatureMatrix,
          reluApproxVectorBoxScanLoadFeatureBias,
          reluApproxVectorBoxScanLoadFeatures,
          Fin.addCases_left, Fin.addCases_right, add_zero]
        rw [hsum_coord_pos]
        congr 1
        ring
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanLoadFeatureMatrix,
          reluApproxVectorBoxScanLoadFeatureBias,
          reluApproxVectorBoxScanLoadFeatures]
      · intro k
        simp [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanLoadFeatureMatrix,
          reluApproxVectorBoxScanLoadFeatureBias,
          reluApproxVectorBoxScanLoadFeatures, Fin.addCases_right]
        have hk : k.addNat m = Fin.natAdd m k := by
          apply Fin.ext
          simp
        rw [hk, Fin.addCases_right, Fin.addCases_right]

/-! ### State-dependent vector box loads

The coarse scan above loads constants stored in the network weights.  In the
second pass of the paper the box faces and the values to be selected are
themselves registers of the running state.  The following variant exposes the
corresponding affine forms while retaining exactly the same feature ordering
and load/accumulate update matrices. -/

/-- Feature matrix for a vector box load whose two face tests and payload are
arbitrary affine functions of the current signed state. -/
noncomputable def reluApproxVectorBoxScanAffineLoadFeatureMatrix {d m : ℕ}
    (lowerArg upperArg : Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (payloadArg : Matrix (Fin m)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ) :
    Matrix (Fin (reluApproxVectorBoxScanFeatureSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases (reluApproxBoxScanCopyRows s) <|
    Fin.addCases (Fin.addCases lowerArg upperArg) <|
      Fin.addCases payloadArg (fun k j ↦ -payloadArg k j)

/-- Biases for a state-dependent vector box load. -/
noncomputable def reluApproxVectorBoxScanAffineLoadFeatureBias {d m : ℕ}
    (lowerBias upperBias : Fin d → ℝ) (payloadBias : Fin m → ℝ) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases (fun _ : Fin (s + s) ↦ 0) <|
    Fin.addCases (Fin.addCases lowerBias upperBias) <|
      Fin.addCases payloadBias (fun k ↦ -payloadBias k)

/-- Mathematical feature vector produced by a state-dependent vector box
load. -/
private noncomputable def reluApproxVectorBoxScanAffineLoadFeatures {d m : ℕ}
    (lowerArg upperArg : Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (payloadArg : Matrix (Fin m)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (lowerBias upperBias : Fin d → ℝ) (payloadBias : Fin m → ℝ)
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  Fin.addCases (reluApproxSignedEncode u) <|
    Fin.addCases
      (Fin.addCases
        (fun q ↦ relu (reluApproxFiniteAffineMap lowerArg lowerBias u q))
        (fun q ↦ relu (reluApproxFiniteAffineMap upperArg upperBias u q)))
      (Fin.addCases
        (fun k ↦ relu (reluApproxFiniteAffineMap payloadArg payloadBias u k))
        (fun k ↦ relu (-reluApproxFiniteAffineMap payloadArg payloadBias u k)))

set_option maxRecDepth 10000 in
/-- Exact feature-layer law for state-dependent box faces and payloads. -/
private theorem reluApproxVectorBoxScanAffineLoadFeatures_exact {d m : ℕ}
    (lowerArg upperArg : Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (payloadArg : Matrix (Fin m)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (lowerBias upperBias : Fin d → ℝ) (payloadBias : Fin m → ℝ)
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxVectorBoxScanAffineLoadFeatureMatrix lowerArg upperArg payloadArg)
      (reluApproxVectorBoxScanAffineLoadFeatureBias lowerBias upperBias payloadBias)
      u i)) =
      reluApproxVectorBoxScanAffineLoadFeatures lowerArg upperArg payloadArg
        lowerBias upperBias payloadBias u := by
  classical
  let s := reluApproxVectorBoxScanStateSize d m
  have hsum_pos (k : Fin s) :
      (∑ j : Fin s, (if k = j then 1 else 0) * u j) = u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  have hsum_neg (k : Fin s) :
      (∑ j : Fin s, (if k = j then -1 else 0) * u j) = -u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAffineLoadFeatureMatrix,
        reluApproxVectorBoxScanAffineLoadFeatureBias,
        reluApproxVectorBoxScanAffineLoadFeatures,
        reluApproxBoxScanCopyRows, Fin.addCases_left, add_zero]
      rw [hsum_pos]
      exact (reluApproxSignedEncode_castAdd u k).symm
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAffineLoadFeatureMatrix,
        reluApproxVectorBoxScanAffineLoadFeatureBias,
        reluApproxVectorBoxScanAffineLoadFeatures,
        reluApproxBoxScanCopyRows, Fin.addCases_left,
        Fin.addCases_right, add_zero]
      rw [hsum_neg]
      exact (reluApproxSignedEncode_natAdd u k).symm
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAffineLoadFeatureMatrix,
          reluApproxVectorBoxScanAffineLoadFeatureBias,
          reluApproxVectorBoxScanAffineLoadFeatures]
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAffineLoadFeatureMatrix,
          reluApproxVectorBoxScanAffineLoadFeatureBias,
          reluApproxVectorBoxScanAffineLoadFeatures,
          Fin.addCases_left, Fin.addCases_right]
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAffineLoadFeatureMatrix,
          reluApproxVectorBoxScanAffineLoadFeatureBias,
          reluApproxVectorBoxScanAffineLoadFeatures]
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAffineLoadFeatureMatrix,
          reluApproxVectorBoxScanAffineLoadFeatureBias,
          reluApproxVectorBoxScanAffineLoadFeatures,
          Fin.addCases_right]
        have hsum :
            (∑ x, -payloadArg k x * u x) =
              -(∑ x, payloadArg k x * u x) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        rw [hsum]
        ring

/-- Update matrix of the vector-payload load macro. -/
noncomputable def reluApproxVectorBoxScanLoadUpdateMatrix (d m : ℕ) :
    Matrix (Fin (reluApproxVectorBoxScanStateSize d m))
      (Fin (reluApproxVectorBoxScanFeatureSize d m)) ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  Fin.addCases
    (fun i : Fin d ↦ reluApproxVectorBoxScanDecodeRow d m (Fin.castAdd _ i)) <|
    Fin.addCases
      (fun k : Fin m ↦ reluApproxVectorBoxScanDecodeRow d m
        (Fin.natAdd d (Fin.castAdd _ k))) <|
      Fin.addCases
        (fun _ : Fin 1 ↦ Fin.addCases (fun _ : Fin (s + s) ↦ 0) <|
          Fin.addCases (fun _ : Fin (d + d) ↦ 1) (fun _ : Fin (m + m) ↦ 0)) <|
        Fin.addCases
          (fun k : Fin m ↦ Fin.addCases (fun _ : Fin (s + s) ↦ 0) <|
            Fin.addCases (fun _ : Fin (d + d) ↦ 0) <|
              Fin.addCases (fun j : Fin m ↦ if j = k then 1 else 0)
                (fun _ : Fin m ↦ 0))
          (fun k : Fin m ↦ Fin.addCases (fun _ : Fin (s + s) ↦ 0) <|
            Fin.addCases (fun _ : Fin (d + d) ↦ 0) <|
              Fin.addCases (fun _ : Fin m ↦ 0)
                (fun j : Fin m ↦ if j = k then 1 else 0))

/-- The vector load macro preserves the input and accumulator and fills all
work registers exactly. -/
private theorem reluApproxVectorBoxScanLoadUpdate_exact {d m : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ)
    (payload acc : Fin m → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanLoadUpdateMatrix d m) (fun _ ↦ 0)
        (reluApproxVectorBoxScanLoadFeatures R lower upper payload
          (reluApproxVectorBoxScanState x acc)) =
      reluApproxVectorBoxScanLoadedState R lower upper x payload acc := by
  classical
  let u := reluApproxVectorBoxScanState x acc
  have hdecode (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
      (∑ j : Fin (reluApproxVectorBoxScanFeatureSize d m),
          reluApproxVectorBoxScanDecodeRow d m i j *
            reluApproxVectorBoxScanLoadFeatures R lower upper payload u j) = u i := by
    simpa [reluApproxVectorBoxScanLoadFeatures] using
      (reluApproxVectorBoxScanDecodeRow_dot
        (u := u)
        (v := Fin.addCases
          (Fin.addCases
            (fun q : Fin d ↦ relu (lower q + R⁻¹ - u (Fin.castAdd _ q)))
            (fun q : Fin d ↦ relu (u (Fin.castAdd _ q) - upper q + R⁻¹)))
          (Fin.addCases (fun k : Fin m ↦ relu (payload k))
            (fun k : Fin m ↦ relu (-payload k)))) i)
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro q
    simp only [reluApproxFiniteAffineMap,
      reluApproxVectorBoxScanLoadUpdateMatrix, Fin.addCases_left, add_zero]
    rw [hdecode]
    simp [u, reluApproxVectorBoxScanState,
      reluApproxVectorBoxScanLoadedState]
  · intro r
    refine Fin.addCases ?_ ?_ r
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanLoadUpdateMatrix, Fin.addCases_left,
        Fin.addCases_right, add_zero]
      rw [hdecode]
      simp [u, reluApproxVectorBoxScanState,
        reluApproxVectorBoxScanLoadedState]
    · intro r
      refine Fin.addCases ?_ ?_ r
      · intro q
        fin_cases q
        simp [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanLoadUpdateMatrix,
          reluApproxVectorBoxScanLoadFeatures,
          reluApproxVectorBoxScanState,
          reluApproxVectorBoxScanLoadedState,
          reluApproxVectorBoxScanStateSize,
          reluApproxVectorBoxScanFeatureSize,
          reluApproxBoxViolation, Fin.sum_univ_add]
        have hsecond :
            (∑ q : Fin d,
                Fin.addCases
                  (fun p : Fin d ↦ relu (lower p + R⁻¹ - x p))
                  (fun p : Fin d ↦ relu (x p - upper p + R⁻¹))
                  (q.addNat d)) =
              ∑ q : Fin d, relu (x q - upper q + R⁻¹) := by
          apply Finset.sum_congr rfl
          intro q _hq
          have hq : q.addNat d = Fin.natAdd d q := by
            apply Fin.ext
            simp
          rw [hq, Fin.addCases_right]
        rw [hsecond, Finset.sum_add_distrib]
      · intro r
        refine Fin.addCases ?_ ?_ r
        · intro k
          simp [reluApproxFiniteAffineMap,
            reluApproxVectorBoxScanLoadUpdateMatrix,
            reluApproxVectorBoxScanLoadFeatures,
            reluApproxVectorBoxScanLoadedState,
            reluApproxVectorBoxScanFeatureSize, Fin.sum_univ_add]
          apply Finset.sum_eq_zero
          intro j _hj
          have hj : j.addNat m = Fin.natAdd m j := by
            apply Fin.ext
            simp
          rw [hj, Fin.addCases_right, Fin.addCases_right]
          simp
        · intro k
          simp only [reluApproxFiniteAffineMap,
            reluApproxVectorBoxScanLoadUpdateMatrix,
            reluApproxVectorBoxScanLoadedState, Fin.addCases_right, add_zero]
          simp [
            reluApproxVectorBoxScanLoadFeatures,
            reluApproxVectorBoxScanFeatureSize, Fin.sum_univ_add]
          have hidx (j : Fin m) : j.addNat m = Fin.natAdd m j := by
            apply Fin.ext
            simp
          have hterm (j : Fin m) :
              Fin.addCases (fun _ : Fin m ↦ (0 : ℝ))
                  (fun q : Fin m ↦ if q = k then 1 else 0) (j.addNat m) *
                Fin.addCases (fun q : Fin m ↦ relu (payload q))
                  (fun q : Fin m ↦ relu (-payload q)) (j.addNat m) =
                (if j = k then 1 else 0) * relu (-payload j) := by
            rw [hidx j, Fin.addCases_right, Fin.addCases_right]
          simp_rw [hterm]
          simp

/-- The fixed vector-load update has the same exact semantics when its box
faces and payload are supplied by affine forms of the canonical scan state. -/
private theorem reluApproxVectorBoxScanAffineLoadUpdate_exact {d m : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ)
    (payload acc : Fin m → ℝ)
    (lowerArg upperArg : Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (payloadArg : Matrix (Fin m)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (lowerBias upperBias : Fin d → ℝ) (payloadBias : Fin m → ℝ)
    (hlower : ∀ q,
      reluApproxFiniteAffineMap lowerArg lowerBias
          (reluApproxVectorBoxScanState x acc) q =
        lower q + R⁻¹ - x q)
    (hupper : ∀ q,
      reluApproxFiniteAffineMap upperArg upperBias
          (reluApproxVectorBoxScanState x acc) q =
        x q - upper q + R⁻¹)
    (hpayload : ∀ k,
      reluApproxFiniteAffineMap payloadArg payloadBias
          (reluApproxVectorBoxScanState x acc) k = payload k) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanLoadUpdateMatrix d m) (fun _ ↦ 0)
        (reluApproxVectorBoxScanAffineLoadFeatures
          lowerArg upperArg payloadArg lowerBias upperBias payloadBias
          (reluApproxVectorBoxScanState x acc)) =
      reluApproxVectorBoxScanLoadedState R lower upper x payload acc := by
  have hfeatures :
      reluApproxVectorBoxScanAffineLoadFeatures
          lowerArg upperArg payloadArg lowerBias upperBias payloadBias
          (reluApproxVectorBoxScanState x acc) =
        reluApproxVectorBoxScanLoadFeatures R lower upper payload
          (reluApproxVectorBoxScanState x acc) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [reluApproxVectorBoxScanAffineLoadFeatures,
        reluApproxVectorBoxScanLoadFeatures]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro q
        refine Fin.addCases ?_ ?_ q
        · intro k
          simp [reluApproxVectorBoxScanAffineLoadFeatures,
            reluApproxVectorBoxScanLoadFeatures,
            reluApproxVectorBoxScanState, hlower]
        · intro k
          simp [reluApproxVectorBoxScanAffineLoadFeatures,
            reluApproxVectorBoxScanLoadFeatures,
            reluApproxVectorBoxScanState, hupper]
          have hk : k.addNat d = Fin.natAdd d k := by
            apply Fin.ext
            simp
          rw [hk, Fin.addCases_right, Fin.addCases_right]
      · intro q
        refine Fin.addCases ?_ ?_ q
        · intro k
          simp [reluApproxVectorBoxScanAffineLoadFeatures,
            reluApproxVectorBoxScanLoadFeatures, hpayload]
        · intro k
          simp [reluApproxVectorBoxScanAffineLoadFeatures,
            reluApproxVectorBoxScanLoadFeatures, hpayload]
  rw [hfeatures]
  exact reluApproxVectorBoxScanLoadUpdate_exact R lower upper x payload acc

/-- Index of the shared violation register in the vector scan state. -/
private def reluApproxVectorBoxScanViolationIndex (d m : ℕ) :
    Fin (reluApproxVectorBoxScanStateSize d m) :=
  Fin.natAdd d (Fin.natAdd m (Fin.castAdd (m + m) (0 : Fin 1)))

/-- Index of the positive part of payload coordinate k. -/
private def reluApproxVectorBoxScanPositiveIndex (d m : ℕ) (k : Fin m) :
    Fin (reluApproxVectorBoxScanStateSize d m) :=
  Fin.natAdd d (Fin.natAdd m (Fin.natAdd 1 (Fin.castAdd m k)))

/-- Index of the negative part of payload coordinate k. -/
private def reluApproxVectorBoxScanNegativeIndex (d m : ℕ) (k : Fin m) :
    Fin (reluApproxVectorBoxScanStateSize d m) :=
  Fin.natAdd d (Fin.natAdd m (Fin.natAdd 1 (Fin.natAdd m k)))

/-- Index of an accumulator coordinate in the canonical vector-scan state. -/
private def reluApproxVectorBoxScanAccumulatorIndex (d m : ℕ) (k : Fin m) :
    Fin (reluApproxVectorBoxScanStateSize d m) :=
  Fin.natAdd d (Fin.castAdd (1 + (m + m)) k)

/-- A coordinate projection row on the canonical vector-scan state. -/
private noncomputable def reluApproxVectorBoxScanCoordinateRow {d m : ℕ}
    (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
    Fin (reluApproxVectorBoxScanStateSize d m) → ℝ :=
  fun j ↦ if j = i then 1 else 0

private theorem reluApproxVectorBoxScanCoordinateRow_dot {d m : ℕ}
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ)
    (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
    (∑ j, reluApproxVectorBoxScanCoordinateRow i j * u j) = u i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [reluApproxVectorBoxScanCoordinateRow]
  · intro j _hj hji
    simp [reluApproxVectorBoxScanCoordinateRow, hji]
  · simp

/-- Lower-face affine forms for a box centered at coordinates stored in the
running accumulator. -/
noncomputable def reluApproxVectorBoxScanCenteredLowerArg {d m : ℕ}
    (centerIndex : Fin d → Fin m) :
    Matrix (Fin d) (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  fun q j ↦
    reluApproxVectorBoxScanCoordinateRow
        (reluApproxVectorBoxScanAccumulatorIndex d m (centerIndex q)) j -
      reluApproxVectorBoxScanCoordinateRow (Fin.castAdd _ q) j

/-- Upper-face affine forms for the same state-dependent centered box. -/
noncomputable def reluApproxVectorBoxScanCenteredUpperArg {d m : ℕ}
    (centerIndex : Fin d → Fin m) :
    Matrix (Fin d) (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  fun q j ↦
    reluApproxVectorBoxScanCoordinateRow (Fin.castAdd _ q) j -
      reluApproxVectorBoxScanCoordinateRow
        (reluApproxVectorBoxScanAccumulatorIndex d m (centerIndex q)) j

/-- Payload affine forms which read one accumulator register per output and
optionally multiply it by a fixed gain (zero gains suppress preserved fields). -/
noncomputable def reluApproxVectorBoxScanAccumulatorPayloadArg {d m : ℕ}
    (source : Fin m → Fin m) (gain : Fin m → ℝ) :
    Matrix (Fin m) (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  fun k j ↦ gain k * reluApproxVectorBoxScanCoordinateRow
    (reluApproxVectorBoxScanAccumulatorIndex d m (source k)) j

/-- The centered lower-face forms evaluate to `center - radius + R⁻¹ - x`. -/
theorem reluApproxVectorBoxScanCenteredLowerArg_exact {d m : ℕ}
    (R radius : ℝ) (centerIndex : Fin d → Fin m)
    (x : Fin d → ℝ) (acc : Fin m → ℝ) (q : Fin d) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanCenteredLowerArg centerIndex)
        (fun _ ↦ R⁻¹ - radius)
        (reluApproxVectorBoxScanState x acc) q =
      (acc (centerIndex q) - radius) + R⁻¹ - x q := by
  classical
  simp only [reluApproxFiniteAffineMap,
    reluApproxVectorBoxScanCenteredLowerArg, sub_mul,
    Finset.sum_sub_distrib]
  rw [reluApproxVectorBoxScanCoordinateRow_dot,
    reluApproxVectorBoxScanCoordinateRow_dot]
  simp [reluApproxVectorBoxScanState,
    reluApproxVectorBoxScanAccumulatorIndex]
  ring

/-- The centered upper-face forms evaluate to `x - (center + radius) + R⁻¹`. -/
theorem reluApproxVectorBoxScanCenteredUpperArg_exact {d m : ℕ}
    (R radius : ℝ) (centerIndex : Fin d → Fin m)
    (x : Fin d → ℝ) (acc : Fin m → ℝ) (q : Fin d) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanCenteredUpperArg centerIndex)
        (fun _ ↦ R⁻¹ - radius)
        (reluApproxVectorBoxScanState x acc) q =
      x q - (acc (centerIndex q) + radius) + R⁻¹ := by
  classical
  simp only [reluApproxFiniteAffineMap,
    reluApproxVectorBoxScanCenteredUpperArg, sub_mul,
    Finset.sum_sub_distrib]
  rw [reluApproxVectorBoxScanCoordinateRow_dot,
    reluApproxVectorBoxScanCoordinateRow_dot]
  simp [reluApproxVectorBoxScanState,
    reluApproxVectorBoxScanAccumulatorIndex]
  ring

/-- Accumulator payload forms read exactly the requested source register. -/
theorem reluApproxVectorBoxScanAccumulatorPayloadArg_exact {d m : ℕ}
    (source : Fin m → Fin m) (gain : Fin m → ℝ)
    (x : Fin d → ℝ) (acc : Fin m → ℝ) (k : Fin m) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanAccumulatorPayloadArg source gain)
        (fun _ ↦ 0) (reluApproxVectorBoxScanState x acc) k =
      gain k * acc (source k) := by
  classical
  simp only [reluApproxFiniteAffineMap,
    reluApproxVectorBoxScanAccumulatorPayloadArg, add_zero]
  calc
    (∑ j, gain k *
        reluApproxVectorBoxScanCoordinateRow
          (reluApproxVectorBoxScanAccumulatorIndex d m (source k)) j *
        reluApproxVectorBoxScanState x acc j) =
        gain k * (∑ j,
          reluApproxVectorBoxScanCoordinateRow
            (reluApproxVectorBoxScanAccumulatorIndex d m (source k)) j *
          reluApproxVectorBoxScanState x acc j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = gain k * reluApproxVectorBoxScanState x acc
        (reluApproxVectorBoxScanAccumulatorIndex d m (source k)) := by
      rw [reluApproxVectorBoxScanCoordinateRow_dot]
    _ = gain k * acc (source k) := by
      simp [reluApproxVectorBoxScanState,
        reluApproxVectorBoxScanAccumulatorIndex]

/-- Feature matrix of the vector accumulator macro.  The final 2m rows are
the positive and negative outer box gates for every payload coordinate. -/
noncomputable def reluApproxVectorBoxScanAccFeatureMatrix
    (d m : ℕ) (R : ℝ) :
    Matrix (Fin (reluApproxVectorBoxScanFeatureSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  let violation := reluApproxVectorBoxScanViolationIndex d m
  Fin.addCases (reluApproxBoxScanCopyRows s) <|
    Fin.addCases (fun _ : Fin (d + d) ↦ fun _ ↦ 0) <|
      Fin.addCases
        (fun k j ↦
          (if j = reluApproxVectorBoxScanPositiveIndex d m k then 1 else 0) +
            (if j = violation then -(R ^ 2) else 0))
        (fun k j ↦
          (if j = reluApproxVectorBoxScanNegativeIndex d m k then 1 else 0) +
            (if j = violation then -(R ^ 2) else 0))

/-- Mathematical feature vector of the vector accumulator macro. -/
private noncomputable def reluApproxVectorBoxScanAccFeatures {d m : ℕ} (R : ℝ)
    (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  let violation := reluApproxVectorBoxScanViolationIndex d m
  Fin.addCases (reluApproxSignedEncode u) <|
    Fin.addCases (fun _ : Fin (d + d) ↦ 0) <|
      Fin.addCases
        (fun k : Fin m ↦ relu
          (u (reluApproxVectorBoxScanPositiveIndex d m k) -
            R ^ 2 * u violation))
        (fun k : Fin m ↦ relu
          (u (reluApproxVectorBoxScanNegativeIndex d m k) -
            R ^ 2 * u violation))

/-- One accumulator update row: decode the old accumulator coordinate from
the signed prefix and add the corresponding signed outer gate. -/
private noncomputable def reluApproxVectorBoxScanAccUpdateRow
    (d m : ℕ) (k : Fin m) :
    Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  let s := reluApproxVectorBoxScanStateSize d m
  let accIndex : Fin s := Fin.natAdd d (Fin.castAdd (1 + (m + m)) k)
  Fin.addCases
    (Fin.addCases
      (fun j : Fin s ↦ if j = accIndex then 1 else 0)
      (fun j : Fin s ↦ if j = accIndex then -1 else 0)) <|
    Fin.addCases (fun _ : Fin (d + d) ↦ 0) <|
      Fin.addCases
        (fun j : Fin m ↦ if j = k then 1 else 0)
        (fun j : Fin m ↦ if j = k then -1 else 0)

/-- Update matrix of the vector accumulator macro. -/
noncomputable def reluApproxVectorBoxScanAccUpdateMatrix (d m : ℕ) :
    Matrix (Fin (reluApproxVectorBoxScanStateSize d m))
      (Fin (reluApproxVectorBoxScanFeatureSize d m)) ℝ :=
  Fin.addCases
    (fun i : Fin d ↦ reluApproxVectorBoxScanDecodeRow d m (Fin.castAdd _ i)) <|
    Fin.addCases
      (fun k : Fin m ↦ reluApproxVectorBoxScanAccUpdateRow d m k)
      (fun _ ↦ 0)

/-- The accumulator feature matrix computes all vector box gates exactly. -/
private theorem reluApproxVectorBoxScanAccFeatures_exact {d m : ℕ}
    (R : ℝ) (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxVectorBoxScanAccFeatureMatrix d m R) (fun _ ↦ 0) u i)) =
      reluApproxVectorBoxScanAccFeatures R u := by
  classical
  let s := reluApproxVectorBoxScanStateSize d m
  have hsum_pos (k : Fin s) :
      (∑ j : Fin s, (if k = j then 1 else 0) * u j) = u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  have hsum_neg (k : Fin s) :
      (∑ j : Fin s, (if k = j then -1 else 0) * u j) = -u k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [Ne.symm hbk]
    · simp
  have hlinear (a b : Fin s) :
      (∑ j : Fin s,
          ((if j = a then 1 else 0) +
            (if j = b then -(R ^ 2) else 0)) * u j) =
        u a - R ^ 2 * u b := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    have ha :
        (∑ j : Fin s, (if j = a then 1 else 0) * u j) = u a := by
      simpa [eq_comm] using hsum_pos a
    have hb :
        (∑ j : Fin s, (if j = b then -(R ^ 2) else 0) * u j) =
          -(R ^ 2) * u b := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro q _hq hqb
        simp [hqb]
      · simp
    rw [ha, hb]
    ring
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAccFeatureMatrix,
        reluApproxBoxScanCopyRows,
        reluApproxVectorBoxScanAccFeatures, Fin.addCases_left, add_zero]
      rw [hsum_pos]
      exact (reluApproxSignedEncode_castAdd u k).symm
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAccFeatureMatrix,
        reluApproxBoxScanCopyRows,
        reluApproxVectorBoxScanAccFeatures,
        Fin.addCases_left, Fin.addCases_right, add_zero]
      rw [hsum_neg]
      exact (reluApproxSignedEncode_natAdd u k).symm
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro q
      simp [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAccFeatureMatrix,
        reluApproxVectorBoxScanAccFeatures, relu]
    · intro q
      refine Fin.addCases ?_ ?_ q
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAccFeatureMatrix,
          reluApproxVectorBoxScanAccFeatures,
          Fin.addCases_left, Fin.addCases_right, add_zero]
        rw [hlinear]
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxVectorBoxScanAccFeatureMatrix,
          reluApproxVectorBoxScanAccFeatures,
          Fin.addCases_left, Fin.addCases_right, add_zero]
        rw [hlinear]

/-- Signed-copy rows also decode accumulator-macro feature vectors. -/
private theorem reluApproxVectorBoxScanDecodeRow_dot_accFeatures {d m : ℕ}
    (R : ℝ) (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ)
    (i : Fin (reluApproxVectorBoxScanStateSize d m)) :
    (∑ j : Fin (reluApproxVectorBoxScanFeatureSize d m),
        reluApproxVectorBoxScanDecodeRow d m i j *
          reluApproxVectorBoxScanAccFeatures R u j) = u i := by
  simpa [reluApproxVectorBoxScanAccFeatures] using
    (reluApproxVectorBoxScanDecodeRow_dot
      (u := u)
      (v := Fin.addCases (fun _ : Fin (d + d) ↦ 0)
        (Fin.addCases
          (fun k : Fin m ↦ relu
            (u (reluApproxVectorBoxScanPositiveIndex d m k) -
              R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m)))
          (fun k : Fin m ↦ relu
            (u (reluApproxVectorBoxScanNegativeIndex d m k) -
              R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m))))) i)



/-- One accumulator update row decodes its old register and adds its two gate
features. -/
private theorem reluApproxVectorBoxScanAccUpdateRow_dot {d m : ℕ}
    (R : ℝ) (u : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ)
    (k : Fin m) :
    (∑ j : Fin (reluApproxVectorBoxScanFeatureSize d m),
        reluApproxVectorBoxScanAccUpdateRow d m k j *
          reluApproxVectorBoxScanAccFeatures R u j) =
      u (Fin.natAdd d (Fin.castAdd (1 + (m + m)) k)) +
        relu (u (reluApproxVectorBoxScanPositiveIndex d m k) -
          R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m)) -
        relu (u (reluApproxVectorBoxScanNegativeIndex d m k) -
          R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m)) := by
  classical
  let s := reluApproxVectorBoxScanStateSize d m
  let a : Fin s := Fin.natAdd d (Fin.castAdd (1 + (m + m)) k)
  have hsigned :
      (∑ j : Fin (s + s),
          Fin.addCases
              (fun q : Fin s ↦ if q = a then 1 else 0)
              (fun q : Fin s ↦ if q = a then -1 else 0) j *
            reluApproxSignedEncode u j) = u a := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    have hcast (q : Fin s) :
        reluApproxSignedEncode u (Fin.castAdd s q) = relu (u q) := by
      exact reluApproxSignedEncode_castAdd u q
    have hnat (q : Fin s) :
        reluApproxSignedEncode u (Fin.natAdd s q) = relu (-u q) := by
      exact reluApproxSignedEncode_natAdd u q
    simp_rw [hcast, hnat]
    have hpos :
        (∑ q : Fin s, (if q = a then 1 else 0) * relu (u q)) =
          relu (u a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro q _hq hqa
        simp [hqa]
      · simp
    have hneg :
        (∑ q : Fin s, (if q = a then -1 else 0) * relu (-u q)) =
          -relu (-u a) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro q _hq hqa
        simp [hqa]
      · simp
    rw [hpos, hneg]
    exact reluApproxSignedEncode_sub (u a)
  simp only [reluApproxVectorBoxScanFeatureSize]
  rw [Fin.sum_univ_add]
  simp only [reluApproxVectorBoxScanAccUpdateRow,
    reluApproxVectorBoxScanAccFeatures, Fin.addCases_left,
    Fin.addCases_right]
  rw [hsigned]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_mul,
    Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  have hposGate :
      (∑ q : Fin m,
          (if q = k then 1 else 0) *
            relu (u (reluApproxVectorBoxScanPositiveIndex d m q) -
              R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m))) =
        relu (u (reluApproxVectorBoxScanPositiveIndex d m k) -
          R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m)) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro q _hq hqk
      simp [hqk]
    · simp
  have hnegGate :
      (∑ q : Fin m,
          (if q = k then -1 else 0) *
            relu (u (reluApproxVectorBoxScanNegativeIndex d m q) -
              R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m))) =
        -relu (u (reluApproxVectorBoxScanNegativeIndex d m k) -
          R ^ 2 * u (reluApproxVectorBoxScanViolationIndex d m)) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro q _hq hqk
      simp [hqk]
    · simp
  rw [hposGate, hnegGate]
  dsimp [a]
  ring

/-- The accumulator macro adds every coordinate of the current vector box
gate and returns to the canonical scan-state shape. -/
private theorem reluApproxVectorBoxScanAccUpdate_exact {d m : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ)
    (payload acc : Fin m → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanAccUpdateMatrix d m) (fun _ ↦ 0)
        (reluApproxVectorBoxScanAccFeatures R
          (reluApproxVectorBoxScanLoadedState R lower upper x payload acc)) =
      reluApproxVectorBoxScanState x
        (fun k ↦ acc k + reluApproxBoxGate R lower upper x (payload k)) := by
  let u := reluApproxVectorBoxScanLoadedState R lower upper x payload acc
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro q
    simp only [reluApproxFiniteAffineMap,
      reluApproxVectorBoxScanAccUpdateMatrix, Fin.addCases_left, add_zero]
    rw [reluApproxVectorBoxScanDecodeRow_dot_accFeatures]
    simp [u, reluApproxVectorBoxScanLoadedState,
      reluApproxVectorBoxScanState]
  · intro tail
    refine Fin.addCases ?_ ?_ tail
    · intro k
      simp only [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAccUpdateMatrix,
        Fin.addCases_left, Fin.addCases_right, add_zero]
      rw [reluApproxVectorBoxScanAccUpdateRow_dot]
      simp [u, reluApproxVectorBoxScanLoadedState,
        reluApproxVectorBoxScanState,
        reluApproxVectorBoxScanViolationIndex,
        reluApproxVectorBoxScanPositiveIndex,
        reluApproxVectorBoxScanNegativeIndex,
        reluApproxBoxGate]
      have hk : k.addNat m = Fin.natAdd m k := by
        apply Fin.ext
        simp
      rw [hk, Fin.addCases_right]
      ring
    · intro work
      simp [reluApproxFiniteAffineMap,
        reluApproxVectorBoxScanAccUpdateMatrix,
        reluApproxVectorBoxScanState]
      refine Fin.addCases (fun _ ↦ ?_) (fun q ↦ ?_) work
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
        refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) q
        · rw [Fin.addCases_left]
        · rw [Fin.addCases_right]

/-- One complete state-dependent vector box cycle first loads affine box faces
and payload registers and then adds the resulting gated payload to the running
accumulator.  The cycle returns to canonical scan-state form. -/
theorem reluApproxVectorBoxScanAffineCycle_exact {d m : ℕ}
    (R : ℝ) (lower upper x : Fin d → ℝ)
    (payload acc : Fin m → ℝ)
    (lowerArg upperArg : Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (payloadArg : Matrix (Fin m)
      (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ)
    (lowerBias upperBias : Fin d → ℝ) (payloadBias : Fin m → ℝ)
    (hlower : ∀ q,
      reluApproxFiniteAffineMap lowerArg lowerBias
          (reluApproxVectorBoxScanState x acc) q =
        lower q + R⁻¹ - x q)
    (hupper : ∀ q,
      reluApproxFiniteAffineMap upperArg upperBias
          (reluApproxVectorBoxScanState x acc) q =
        x q - upper q + R⁻¹)
    (hpayload : ∀ k,
      reluApproxFiniteAffineMap payloadArg payloadBias
          (reluApproxVectorBoxScanState x acc) k = payload k) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanAccUpdateMatrix d m) (fun _ ↦ 0)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxVectorBoxScanAccFeatureMatrix d m R) (fun _ ↦ 0)
          (reluApproxFiniteAffineMap
            (reluApproxVectorBoxScanLoadUpdateMatrix d m) (fun _ ↦ 0)
            (fun j ↦ relu (reluApproxFiniteAffineMap
              (reluApproxVectorBoxScanAffineLoadFeatureMatrix
                lowerArg upperArg payloadArg)
              (reluApproxVectorBoxScanAffineLoadFeatureBias
                lowerBias upperBias payloadBias)
              (reluApproxVectorBoxScanState x acc) j))) i)) =
      reluApproxVectorBoxScanState x
        (fun k ↦ acc k + reluApproxBoxGate R lower upper x (payload k)) := by
  rw [reluApproxVectorBoxScanAffineLoadFeatures_exact]
  rw [reluApproxVectorBoxScanAffineLoadUpdate_exact
    R lower upper x payload acc lowerArg upperArg payloadArg
    lowerBias upperBias payloadBias hlower hupper hpayload]
  rw [reluApproxVectorBoxScanAccFeatures_exact]
  exact reluApproxVectorBoxScanAccUpdate_exact R lower upper x payload acc

/-- Input affine map for a vector box scan: copy x and zero all registers. -/
noncomputable def reluApproxVectorBoxScanInputMatrix (d m : ℕ) :
    Matrix (Fin (reluApproxVectorBoxScanStateSize d m)) (Fin d) ℝ :=
  Fin.addCases (fun i j ↦ if j = i then 1 else 0) (fun _ _ ↦ 0)

private theorem reluApproxVectorBoxScanInput_exact {d m : ℕ}
    (x : Fin d → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxVectorBoxScanInputMatrix d m) (fun _ ↦ 0) x =
      reluApproxVectorBoxScanState x (fun _ ↦ 0) := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp [reluApproxFiniteAffineMap,
      reluApproxVectorBoxScanInputMatrix,
      reluApproxVectorBoxScanState]
  · intro k
    simp [reluApproxFiniteAffineMap,
      reluApproxVectorBoxScanInputMatrix,
      reluApproxVectorBoxScanState]
    refine Fin.addCases (fun _ ↦ ?_) (fun q ↦ ?_) k
    · rw [Fin.addCases_left]
    · rw [Fin.addCases_right]
      refine Fin.addCases (fun _ ↦ ?_) (fun q' ↦ ?_) q
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
        refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) q'
        · rw [Fin.addCases_left]
        · rw [Fin.addCases_right]

/-- Alternating feature matrices for load and accumulate macros. -/
noncomputable def reluApproxVectorBoxScanFeatureSchedule {d m T : ℕ}
    (R : ℝ) :
    Fin (T * 2) →
      Matrix (Fin (reluApproxVectorBoxScanFeatureSize d m))
        (Fin (reluApproxVectorBoxScanStateSize d m)) ℝ :=
  fun k ↦ if k.val % 2 = 0 then
    reluApproxVectorBoxScanLoadFeatureMatrix d m
  else
    reluApproxVectorBoxScanAccFeatureMatrix d m R

/-- Alternating feature biases for load and accumulate macros. -/
noncomputable def reluApproxVectorBoxScanFeatureBiasSchedule {d m T : ℕ}
    (R : ℝ) (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) :
    Fin (T * 2) → Fin (reluApproxVectorBoxScanFeatureSize d m) → ℝ :=
  fun k ↦ if hk : k.val % 2 = 0 then
    reluApproxVectorBoxScanLoadFeatureBias R
      (lower ⟨k.val / 2, by omega⟩)
      (upper ⟨k.val / 2, by omega⟩)
      (payload ⟨k.val / 2, by omega⟩)
  else
    fun _ ↦ 0

/-- Alternating update matrices for load and accumulate macros. -/
noncomputable def reluApproxVectorBoxScanUpdateSchedule {d m T : ℕ} :
    Fin (T * 2) →
      Matrix (Fin (reluApproxVectorBoxScanStateSize d m))
        (Fin (reluApproxVectorBoxScanFeatureSize d m)) ℝ :=
  fun k ↦ if k.val % 2 = 0 then
    reluApproxVectorBoxScanLoadUpdateMatrix d m
  else
    reluApproxVectorBoxScanAccUpdateMatrix d m

/-- All update biases vanish in the vector box scan. -/
noncomputable def reluApproxVectorBoxScanUpdateBiasSchedule {d m T : ℕ} :
    Fin (T * 2) → Fin (reluApproxVectorBoxScanStateSize d m) → ℝ :=
  fun _ _ ↦ 0

/-- Mathematical accumulator after the first n boxes. -/
noncomputable def reluApproxVectorBoxScanAccumulator {d m T : ℕ}
    (R : ℝ) (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) (x : Fin d → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 =>
      if hn : n < T then
        fun k ↦ reluApproxVectorBoxScanAccumulator R lower upper payload x n k +
          reluApproxBoxGate R (lower ⟨n, hn⟩) (upper ⟨n, hn⟩) x
            (payload ⟨n, hn⟩ k)
      else
        reluApproxVectorBoxScanAccumulator R lower upper payload x n

/-- At every completed pair of macros, the recursion has accumulated exactly
the boxes processed so far. -/
theorem reluApproxVectorBoxScanRecursion_even {d m T : ℕ}
    (R : ℝ) (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) (x : Fin d → ℝ)
    (n : ℕ) (hn : n ≤ T) :
    reluApproxSignedMacroRecursion
        (reluApproxVectorBoxScanInputMatrix d m) (fun _ ↦ 0)
        (reluApproxVectorBoxScanFeatureSchedule R)
        (reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload)
        reluApproxVectorBoxScanUpdateSchedule
        reluApproxVectorBoxScanUpdateBiasSchedule x (2 * n) =
      reluApproxVectorBoxScanState x
        (reluApproxVectorBoxScanAccumulator R lower upper payload x n) := by
  induction n with
  | zero =>
      simp only [Nat.mul_zero, reluApproxSignedMacroRecursion]
      exact reluApproxVectorBoxScanInput_exact x
  | succ n ih =>
      have hnT : n < T := Nat.lt_of_succ_le hn
      have heven : 2 * n < T * 2 := by omega
      have hodd : 2 * n + 1 < T * 2 := by omega
      have hBodd :
          reluApproxVectorBoxScanFeatureSchedule R
              (⟨2 * n + 1, hodd⟩ : Fin (T * 2)) =
            reluApproxVectorBoxScanAccFeatureMatrix d m R := by
        simp [reluApproxVectorBoxScanFeatureSchedule]
      have hcodd :
          reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload
              (⟨2 * n + 1, hodd⟩ : Fin (T * 2)) = fun _ ↦ 0 := by
        simp [reluApproxVectorBoxScanFeatureBiasSchedule]
      have hAodd :
          reluApproxVectorBoxScanUpdateSchedule
              (⟨2 * n + 1, hodd⟩ : Fin (T * 2)) =
            reluApproxVectorBoxScanAccUpdateMatrix d m := by
        simp [reluApproxVectorBoxScanUpdateSchedule]
      have hbodd :
          reluApproxVectorBoxScanUpdateBiasSchedule
              (d := d) (m := m) (T := T)
              (⟨2 * n + 1, hodd⟩ : Fin (T * 2)) = fun _ ↦ 0 := rfl
      have hBcycles :
          reluApproxVectorBoxScanFeatureSchedule R
              (⟨2 * n, heven⟩ : Fin (T * 2)) =
            reluApproxVectorBoxScanLoadFeatureMatrix d m := by
        simp [reluApproxVectorBoxScanFeatureSchedule]
      have hceven :
          reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload
              (⟨2 * n, heven⟩ : Fin (T * 2)) =
            reluApproxVectorBoxScanLoadFeatureBias R
              (lower ⟨n, hnT⟩) (upper ⟨n, hnT⟩) (payload ⟨n, hnT⟩) := by
        simp [reluApproxVectorBoxScanFeatureBiasSchedule]
      have hAeven :
          reluApproxVectorBoxScanUpdateSchedule
              (⟨2 * n, heven⟩ : Fin (T * 2)) =
            reluApproxVectorBoxScanLoadUpdateMatrix d m := by
        simp [reluApproxVectorBoxScanUpdateSchedule]
      have hbeven :
          reluApproxVectorBoxScanUpdateBiasSchedule
              (d := d) (m := m) (T := T)
              (⟨2 * n, heven⟩ : Fin (T * 2)) = fun _ ↦ 0 := rfl
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [reluApproxSignedMacroRecursion]
      simp only [dif_pos hodd]
      rw [hBodd, hcodd, hAodd, hbodd]
      rw [reluApproxSignedMacroRecursion]
      simp only [dif_pos heven]
      rw [hBcycles, hceven, hAeven, hbeven]
      rw [ih (Nat.le_of_lt hnT)]
      rw [reluApproxVectorBoxScanLoadFeatures_exact]
      rw [reluApproxVectorBoxScanLoadUpdate_exact]
      rw [reluApproxVectorBoxScanAccFeatures_exact]
      rw [reluApproxVectorBoxScanAccUpdate_exact]
      simp [reluApproxVectorBoxScanAccumulator, hnT]

/-- The mathematical accumulator is the finite sum of vector box gates. -/
theorem reluApproxVectorBoxScanAccumulator_eq_sum {d m T : ℕ}
    (R : ℝ) (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) (x : Fin d → ℝ) (k : Fin m) :
    reluApproxVectorBoxScanAccumulator R lower upper payload x T k =
      ∑ i : Fin T,
        reluApproxBoxGate R (lower i) (upper i) x (payload i k) := by
  have hprefix : ∀ (n : ℕ), n ≤ T →
      reluApproxVectorBoxScanAccumulator R lower upper payload x n k =
        ∑ i ∈ Finset.range n,
          if hi : i < T then
            reluApproxBoxGate R (lower ⟨i, hi⟩) (upper ⟨i, hi⟩) x
              (payload ⟨i, hi⟩ k)
          else 0 := by
    intro n hn
    induction n with
    | zero =>
        simp [reluApproxVectorBoxScanAccumulator]
    | succ n ih =>
        have hnT : n < T := Nat.lt_of_succ_le hn
        rw [reluApproxVectorBoxScanAccumulator, dif_pos hnT,
          Finset.sum_range_succ, ih (Nat.le_of_lt hnT)]
        simp [hnT]
  rw [hprefix T le_rfl]
  symm
  simpa using
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ =>
        if hi : i < T then
          reluApproxBoxGate R (lower ⟨i, hi⟩) (upper ⟨i, hi⟩) x
            (payload ⟨i, hi⟩ k)
        else 0) T)

/-- Concrete fixed-width network for one coordinate of a vector box scan. -/
private theorem exists_reluApproxVectorBoxScanNet {d m T : ℕ}
    (hT : 0 < T) (R : ℝ)
    (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) (k : Fin m) :
    ∃ N : FullyConnectedReLUNet d,
      N.depth = T * 5 ∧
        N.width ≤
          (reluApproxVectorBoxScanStateSize d m +
            reluApproxVectorBoxScanStateSize d m) +
              reluApproxVectorBoxScanFeatureSize d m ∧
        N.parameterCount ≤
          fullyConnectedReLUParameterCount d (T * 5)
            ((reluApproxVectorBoxScanStateSize d m +
              reluApproxVectorBoxScanStateSize d m) +
                reluApproxVectorBoxScanFeatureSize d m) ∧
        ∀ x : Fin d → ℝ,
          N.realize x =
            ∑ i : Fin T,
              reluApproxBoxGate R (lower i) (upper i) x (payload i k) := by
  let a : Fin (reluApproxVectorBoxScanStateSize d m) :=
    Fin.natAdd d (Fin.castAdd (1 + (m + m)) k)
  let outputWeight : Fin (reluApproxVectorBoxScanStateSize d m) → ℝ :=
    fun i ↦ if i = a then 1 else 0
  rcases exists_reluApproxSignedMacroBlockScheduleNet
      (cells := T) (q := 2) hT
      (reluApproxVectorBoxScanInputMatrix d m) (fun _ ↦ 0)
      (reluApproxVectorBoxScanFeatureSchedule R)
      (reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload)
      reluApproxVectorBoxScanUpdateSchedule
      reluApproxVectorBoxScanUpdateBiasSchedule outputWeight 0 with
    ⟨N, hdepth, hwidth, hparam, hrealize⟩
  refine ⟨N, by simpa using hdepth, hwidth, by simpa using hparam, ?_⟩
  intro x
  rw [hrealize]
  have hrec :
      reluApproxSignedMacroRecursion
          (reluApproxVectorBoxScanInputMatrix d m) (fun _ ↦ 0)
          (reluApproxVectorBoxScanFeatureSchedule R)
          (reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload)
          reluApproxVectorBoxScanUpdateSchedule
          reluApproxVectorBoxScanUpdateBiasSchedule x (T * 2) =
        reluApproxVectorBoxScanState x
          (reluApproxVectorBoxScanAccumulator R lower upper payload x T) := by
    simpa [Nat.mul_comm] using
      (reluApproxVectorBoxScanRecursion_even
        R lower upper payload x T le_rfl)
  rw [hrec]
  have hselect :
      (∑ i : Fin (reluApproxVectorBoxScanStateSize d m),
          outputWeight i * reluApproxVectorBoxScanState x
            (reluApproxVectorBoxScanAccumulator R lower upper payload x T) i) =
        reluApproxVectorBoxScanAccumulator R lower upper payload x T k := by
    classical
    rw [Finset.sum_eq_single a]
    · simp [outputWeight, a, reluApproxVectorBoxScanState]
    · intro b _hb hba
      simp [outputWeight, hba]
    · simp [outputWeight]
  rw [hselect, add_zero]
  exact reluApproxVectorBoxScanAccumulator_eq_sum R lower upper payload x k

/-- If exactly one box is active on its safe interior and every other box is
outside its safe enlargement, the complete vector scan state contains that
box's payload after the final macro pair.  This state-level form is the bridge
used by the second pass of the shallow ReLU register machine. -/
theorem reluApproxVectorBoxScanRecursion_eq_payload_of_unique
    {d m T : ℕ} {R : ℝ} (hR : 0 < R)
    (lower upper : Fin T → Fin d → ℝ)
    (payload : Fin T → Fin m → ℝ) (x : Fin d → ℝ)
    (active : Fin T)
    (hpayload : ∀ i : Fin T, ∀ k : Fin m, |payload i k| ≤ R)
    (hactive : ∀ q : Fin d, lower active q + R⁻¹ ≤ x q ∧
      x q ≤ upper active q - R⁻¹)
    (hinactive : ∀ i : Fin T, i ≠ active → ∃ q : Fin d,
      x q ≤ lower i q ∨ upper i q ≤ x q) :
    reluApproxSignedMacroRecursion
        (reluApproxVectorBoxScanInputMatrix d m) (fun _ ↦ 0)
        (reluApproxVectorBoxScanFeatureSchedule R)
        (reluApproxVectorBoxScanFeatureBiasSchedule R lower upper payload)
        reluApproxVectorBoxScanUpdateSchedule
        reluApproxVectorBoxScanUpdateBiasSchedule x (2 * T) =
      reluApproxVectorBoxScanState x (payload active) := by
  rw [reluApproxVectorBoxScanRecursion_even R lower upper payload x T le_rfl]
  congr 1
  funext k
  rw [reluApproxVectorBoxScanAccumulator_eq_sum]
  exact reluApprox_sum_boxGate_eq_payload_of_unique hR lower upper
    (fun i ↦ payload i k) x active (fun i ↦ hpayload i k) hactive hinactive

/-! ## Common-workspace embeddings and sequential macro schedules

The two passes of the shallow ReLU machine use different nonlinear feature
blocks.  These embeddings place either block in a common direct-sum feature
workspace without changing the represented state update. -/

/-- Put a nonlinear feature block in the left part of a larger workspace. -/
private noncomputable def reluApproxFeatureMatrixPadLeft {s h₁ h₂ : ℕ}
    (B : Matrix (Fin h₁) (Fin s) ℝ) :
    Matrix (Fin (h₁ + h₂)) (Fin s) ℝ :=
  Fin.addCases B (fun _ _ ↦ 0)

/-- Bias companion of `reluApproxFeatureMatrixPadLeft`. -/
private noncomputable def reluApproxFeatureBiasPadLeft {h₁ h₂ : ℕ}
    (c : Fin h₁ → ℝ) : Fin (h₁ + h₂) → ℝ :=
  Fin.addCases c (fun _ ↦ 0)

/-- Read only the left feature block in a state update. -/
private noncomputable def reluApproxUpdateMatrixPadLeft {s h₁ h₂ : ℕ}
    (A : Matrix (Fin s) (Fin h₁) ℝ) :
    Matrix (Fin s) (Fin (h₁ + h₂)) ℝ :=
  fun i ↦ Fin.addCases (A i) (fun _ ↦ 0)

/-- Put a nonlinear feature block in the right part of a larger workspace. -/
private noncomputable def reluApproxFeatureMatrixPadRight {s h₁ h₂ : ℕ}
    (B : Matrix (Fin h₂) (Fin s) ℝ) :
    Matrix (Fin (h₁ + h₂)) (Fin s) ℝ :=
  Fin.addCases (fun _ _ ↦ 0) B

/-- Bias companion of `reluApproxFeatureMatrixPadRight`. -/
private noncomputable def reluApproxFeatureBiasPadRight {h₁ h₂ : ℕ}
    (c : Fin h₂ → ℝ) : Fin (h₁ + h₂) → ℝ :=
  Fin.addCases (fun _ ↦ 0) c

/-- Read only the right feature block in a state update. -/
private noncomputable def reluApproxUpdateMatrixPadRight {s h₁ h₂ : ℕ}
    (A : Matrix (Fin s) (Fin h₂) ℝ) :
    Matrix (Fin s) (Fin (h₁ + h₂)) ℝ :=
  fun i ↦ Fin.addCases (fun _ ↦ 0) (A i)

private theorem reluApproxMacro_padLeft_exact {s h₁ h₂ : ℕ}
    (B : Matrix (Fin h₁) (Fin s) ℝ) (c : Fin h₁ → ℝ)
    (A : Matrix (Fin s) (Fin h₁) ℝ) (b : Fin s → ℝ)
    (u : Fin s → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxUpdateMatrixPadLeft (h₂ := h₂) A) b
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxFeatureMatrixPadLeft (h₂ := h₂) B)
          (reluApproxFeatureBiasPadLeft (h₂ := h₂) c) u i)) =
      reluApproxFiniteAffineMap A b
        (fun i ↦ relu (reluApproxFiniteAffineMap B c u i)) := by
  funext i
  simp only [reluApproxFiniteAffineMap, Fin.sum_univ_add,
    reluApproxUpdateMatrixPadLeft, Fin.addCases_left,
    Fin.addCases_right, reluApproxFeatureMatrixPadLeft,
    reluApproxFeatureBiasPadLeft, zero_mul, Finset.sum_const_zero, add_zero]

private theorem reluApproxMacro_padRight_exact {s h₁ h₂ : ℕ}
    (B : Matrix (Fin h₂) (Fin s) ℝ) (c : Fin h₂ → ℝ)
    (A : Matrix (Fin s) (Fin h₂) ℝ) (b : Fin s → ℝ)
    (u : Fin s → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxUpdateMatrixPadRight (h₁ := h₁) A) b
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxFeatureMatrixPadRight (h₁ := h₁) B)
          (reluApproxFeatureBiasPadRight (h₁ := h₁) c) u i)) =
      reluApproxFiniteAffineMap A b
        (fun i ↦ relu (reluApproxFiniteAffineMap B c u i)) := by
  funext i
  simp only [reluApproxFiniteAffineMap, Fin.sum_univ_add,
    reluApproxUpdateMatrixPadRight, Fin.addCases_left,
    Fin.addCases_right, reluApproxFeatureMatrixPadRight,
    reluApproxFeatureBiasPadRight, zero_mul, Finset.sum_const_zero, zero_add]

/-- Concatenate two macro schedules while retaining a common feature width. -/
noncomputable def reluApproxConcatFeatureSchedule {s h₁ h₂ T₁ T₂ : ℕ}
    (B₁ : Fin T₁ → Matrix (Fin h₁) (Fin s) ℝ)
    (B₂ : Fin T₂ → Matrix (Fin h₂) (Fin s) ℝ) :
    Fin (T₁ + T₂) → Matrix (Fin (h₁ + h₂)) (Fin s) ℝ :=
  Fin.addCases
    (fun k ↦ reluApproxFeatureMatrixPadLeft (h₂ := h₂) (B₁ k))
    (fun k ↦ reluApproxFeatureMatrixPadRight (h₁ := h₁) (B₂ k))

noncomputable def reluApproxConcatFeatureBiasSchedule {h₁ h₂ T₁ T₂ : ℕ}
    (c₁ : Fin T₁ → Fin h₁ → ℝ) (c₂ : Fin T₂ → Fin h₂ → ℝ) :
    Fin (T₁ + T₂) → Fin (h₁ + h₂) → ℝ :=
  Fin.addCases
    (fun k ↦ reluApproxFeatureBiasPadLeft (h₂ := h₂) (c₁ k))
    (fun k ↦ reluApproxFeatureBiasPadRight (h₁ := h₁) (c₂ k))

noncomputable def reluApproxConcatUpdateSchedule {s h₁ h₂ T₁ T₂ : ℕ}
    (A₁ : Fin T₁ → Matrix (Fin s) (Fin h₁) ℝ)
    (A₂ : Fin T₂ → Matrix (Fin s) (Fin h₂) ℝ) :
    Fin (T₁ + T₂) → Matrix (Fin s) (Fin (h₁ + h₂)) ℝ :=
  Fin.addCases
    (fun k ↦ reluApproxUpdateMatrixPadLeft (h₂ := h₂) (A₁ k))
    (fun k ↦ reluApproxUpdateMatrixPadRight (h₁ := h₁) (A₂ k))

noncomputable def reluApproxConcatUpdateBiasSchedule {s T₁ T₂ : ℕ}
    (b₁ : Fin T₁ → Fin s → ℝ) (b₂ : Fin T₂ → Fin s → ℝ) :
    Fin (T₁ + T₂) → Fin s → ℝ :=
  Fin.addCases b₁ b₂

/-- State recursion for a macro schedule started from an already computed
state, rather than from an affine map of the external input. -/
noncomputable def reluApproxMacroRecursionFrom {s h T : ℕ}
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (u₀ : Fin s → ℝ) : ℕ → Fin s → ℝ
  | 0 => u₀
  | t + 1 =>
      if ht : t < T then
        reluApproxFiniteAffineMap (A ⟨t, ht⟩) (b ⟨t, ht⟩)
          (fun i ↦ relu (reluApproxFiniteAffineMap (B ⟨t, ht⟩) (c ⟨t, ht⟩)
            (reluApproxMacroRecursionFrom B c A b u₀ t) i))
      else
        reluApproxMacroRecursionFrom B c A b u₀ t

/-- Run a suffix of a macro schedule from an already computed state.  The
`start` offset is kept explicit so a fixed-size cell program can be iterated
inside one flat network schedule. -/
noncomputable def reluApproxMacroRecursionFromOffset {s h T : ℕ}
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (start : ℕ) (u₀ : Fin s → ℝ) : ℕ → Fin s → ℝ
  | 0 => u₀
  | t + 1 =>
      if ht : start + t < T then
        reluApproxFiniteAffineMap (A ⟨start + t, ht⟩) (b ⟨start + t, ht⟩)
          (fun i ↦ relu (reluApproxFiniteAffineMap
            (B ⟨start + t, ht⟩) (c ⟨start + t, ht⟩)
            (reluApproxMacroRecursionFromOffset B c A b start u₀ t) i))
      else
        reluApproxMacroRecursionFromOffset B c A b start u₀ t

/-- Splitting a flat macro recursion at `start` is exactly the corresponding
offset recursion initialized by the prefix state. -/
theorem reluApproxMacroRecursionFrom_add_eq_offset {s h T : ℕ}
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (u₀ : Fin s → ℝ) (start len : ℕ) (hbound : start + len ≤ T) :
    reluApproxMacroRecursionFrom B c A b u₀ (start + len) =
      reluApproxMacroRecursionFromOffset B c A b start
        (reluApproxMacroRecursionFrom B c A b u₀ start) len := by
  revert hbound
  induction len with
  | zero =>
      intro _hbound
      simp [reluApproxMacroRecursionFromOffset]
  | succ len ih =>
      intro hbound
      have hlt : start + len < T := by omega
      have hprev : start + len ≤ T := hlt.le
      rw [show start + (len + 1) = (start + len) + 1 by omega]
      rw [reluApproxMacroRecursionFrom,
        reluApproxMacroRecursionFromOffset]
      simp only [dif_pos hlt]
      rw [ih hprev]

/-- A concatenated common-workspace schedule first runs the left program and
then runs the right program from the exact terminal state of the left one. -/
theorem reluApproxSignedMacroRecursion_concat {d s h₁ h₂ T₁ T₂ : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) (b₀ : Fin s → ℝ)
    (B₁ : Fin T₁ → Matrix (Fin h₁) (Fin s) ℝ)
    (c₁ : Fin T₁ → Fin h₁ → ℝ)
    (A₁ : Fin T₁ → Matrix (Fin s) (Fin h₁) ℝ)
    (b₁ : Fin T₁ → Fin s → ℝ)
    (B₂ : Fin T₂ → Matrix (Fin h₂) (Fin s) ℝ)
    (c₂ : Fin T₂ → Fin h₂ → ℝ)
    (A₂ : Fin T₂ → Matrix (Fin s) (Fin h₂) ℝ)
    (b₂ : Fin T₂ → Fin s → ℝ) (x : Fin d → ℝ) :
    reluApproxSignedMacroRecursion A₀ b₀
        (reluApproxConcatFeatureSchedule B₁ B₂)
        (reluApproxConcatFeatureBiasSchedule c₁ c₂)
        (reluApproxConcatUpdateSchedule A₁ A₂)
        (reluApproxConcatUpdateBiasSchedule b₁ b₂) x (T₁ + T₂) =
      reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
        (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x T₁) T₂ := by
  let BC := reluApproxConcatFeatureSchedule B₁ B₂
  let cC := reluApproxConcatFeatureBiasSchedule c₁ c₂
  let AC := reluApproxConcatUpdateSchedule A₁ A₂
  let bC := reluApproxConcatUpdateBiasSchedule b₁ b₂
  have hprefix : ∀ n : ℕ, n ≤ T₁ →
      reluApproxSignedMacroRecursion A₀ b₀ BC cC AC bC x n =
        reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        have hnlt : n < T₁ := Nat.lt_of_succ_le hn
        have hnltC : n < T₁ + T₂ := lt_of_lt_of_le hnlt (Nat.le_add_right T₁ T₂)
        let k₁ : Fin T₁ := ⟨n, hnlt⟩
        have hk : (⟨n, hnltC⟩ : Fin (T₁ + T₂)) = Fin.castAdd T₂ k₁ := by
          ext
          rfl
        rw [reluApproxSignedMacroRecursion, reluApproxSignedMacroRecursion]
        simp only [dif_pos hnltC, dif_pos hnlt]
        rw [ih (Nat.le_of_lt hnlt)]
        rw [show (⟨n, hnltC⟩ : Fin (T₁ + T₂)) = Fin.castAdd T₂ k₁ from hk]
        simp only [AC, bC, BC, cC, reluApproxConcatUpdateSchedule,
          reluApproxConcatUpdateBiasSchedule, reluApproxConcatFeatureSchedule,
          reluApproxConcatFeatureBiasSchedule, Fin.addCases_left]
        change reluApproxFiniteAffineMap
            (reluApproxUpdateMatrixPadLeft (h₂ := h₂) (A₁ k₁)) (b₁ k₁)
            (fun i ↦ relu (reluApproxFiniteAffineMap
              (reluApproxFeatureMatrixPadLeft (h₂ := h₂) (B₁ k₁))
              (reluApproxFeatureBiasPadLeft (h₂ := h₂) (c₁ k₁))
              (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x n) i)) = _
        exact reluApproxMacro_padLeft_exact (h₂ := h₂)
          (B₁ k₁) (c₁ k₁) (A₁ k₁) (b₁ k₁)
          (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x n)
  have hsuffix : ∀ n : ℕ, n ≤ T₂ →
      reluApproxSignedMacroRecursion A₀ b₀ BC cC AC bC x (T₁ + n) =
        reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
          (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x T₁) n := by
    intro n hn
    induction n with
    | zero =>
        simpa using hprefix T₁ le_rfl
    | succ n ih =>
        have hnlt : n < T₂ := Nat.lt_of_succ_le hn
        have hidx : T₁ + n < T₁ + T₂ := Nat.add_lt_add_left hnlt T₁
        let k₂ : Fin T₂ := ⟨n, hnlt⟩
        have hk : (⟨T₁ + n, hidx⟩ : Fin (T₁ + T₂)) = Fin.natAdd T₁ k₂ := by
          ext
          rfl
        rw [show T₁ + (n + 1) = (T₁ + n) + 1 by omega]
        rw [reluApproxSignedMacroRecursion, reluApproxMacroRecursionFrom]
        simp only [dif_pos hidx, dif_pos hnlt]
        rw [ih (Nat.le_of_lt hnlt)]
        rw [show (⟨T₁ + n, hidx⟩ : Fin (T₁ + T₂)) = Fin.natAdd T₁ k₂ from hk]
        simp only [AC, bC, BC, cC, reluApproxConcatUpdateSchedule,
          reluApproxConcatUpdateBiasSchedule, reluApproxConcatFeatureSchedule,
          reluApproxConcatFeatureBiasSchedule, Fin.addCases_right]
        change reluApproxFiniteAffineMap
            (reluApproxUpdateMatrixPadRight (h₁ := h₁) (A₂ k₂)) (b₂ k₂)
            (fun i ↦ relu (reluApproxFiniteAffineMap
              (reluApproxFeatureMatrixPadRight (h₁ := h₁) (B₂ k₂))
              (reluApproxFeatureBiasPadRight (h₁ := h₁) (c₂ k₂))
              (reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
                (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x T₁) n) i)) = _
        exact reluApproxMacro_padRight_exact (h₁ := h₁)
          (B₂ k₂) (c₂ k₂) (A₂ k₂) (b₂ k₂)
          (reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
            (reluApproxSignedMacroRecursion A₀ b₀ B₁ c₁ A₁ b₁ x T₁) n)
  simpa [BC, cC, AC, bC] using hsuffix T₂ le_rfl

/-- Concatenation has the same exact semantics when the first schedule starts
from an already loaded state.  This is the composition rule used to repeat
state-dependent fine-grid rounds. -/
theorem reluApproxMacroRecursionFrom_concat {s h₁ h₂ T₁ T₂ : ℕ}
    (B₁ : Fin T₁ → Matrix (Fin h₁) (Fin s) ℝ)
    (c₁ : Fin T₁ → Fin h₁ → ℝ)
    (A₁ : Fin T₁ → Matrix (Fin s) (Fin h₁) ℝ)
    (b₁ : Fin T₁ → Fin s → ℝ)
    (B₂ : Fin T₂ → Matrix (Fin h₂) (Fin s) ℝ)
    (c₂ : Fin T₂ → Fin h₂ → ℝ)
    (A₂ : Fin T₂ → Matrix (Fin s) (Fin h₂) ℝ)
    (b₂ : Fin T₂ → Fin s → ℝ) (u₀ : Fin s → ℝ) :
    reluApproxMacroRecursionFrom
        (reluApproxConcatFeatureSchedule B₁ B₂)
        (reluApproxConcatFeatureBiasSchedule c₁ c₂)
        (reluApproxConcatUpdateSchedule A₁ A₂)
        (reluApproxConcatUpdateBiasSchedule b₁ b₂) u₀ (T₁ + T₂) =
      reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
        (reluApproxMacroRecursionFrom B₁ c₁ A₁ b₁ u₀ T₁) T₂ := by
  let BC := reluApproxConcatFeatureSchedule B₁ B₂
  let cC := reluApproxConcatFeatureBiasSchedule c₁ c₂
  let AC := reluApproxConcatUpdateSchedule A₁ A₂
  let bC := reluApproxConcatUpdateBiasSchedule b₁ b₂
  have hprefix : ∀ n : ℕ, n ≤ T₁ →
      reluApproxMacroRecursionFrom BC cC AC bC u₀ n =
        reluApproxMacroRecursionFrom B₁ c₁ A₁ b₁ u₀ n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        have hnlt : n < T₁ := Nat.lt_of_succ_le hn
        have hnltC : n < T₁ + T₂ :=
          lt_of_lt_of_le hnlt (Nat.le_add_right T₁ T₂)
        let k₁ : Fin T₁ := ⟨n, hnlt⟩
        have hk : (⟨n, hnltC⟩ : Fin (T₁ + T₂)) = Fin.castAdd T₂ k₁ := by
          ext
          rfl
        rw [reluApproxMacroRecursionFrom, reluApproxMacroRecursionFrom]
        simp only [dif_pos hnltC, dif_pos hnlt]
        rw [ih (Nat.le_of_lt hnlt)]
        rw [show (⟨n, hnltC⟩ : Fin (T₁ + T₂)) = Fin.castAdd T₂ k₁ from hk]
        simp only [AC, bC, BC, cC, reluApproxConcatUpdateSchedule,
          reluApproxConcatUpdateBiasSchedule, reluApproxConcatFeatureSchedule,
          reluApproxConcatFeatureBiasSchedule, Fin.addCases_left]
        exact reluApproxMacro_padLeft_exact (h₂ := h₂)
          (B₁ k₁) (c₁ k₁) (A₁ k₁) (b₁ k₁)
          (reluApproxMacroRecursionFrom B₁ c₁ A₁ b₁ u₀ n)
  have hsuffix : ∀ n : ℕ, n ≤ T₂ →
      reluApproxMacroRecursionFrom BC cC AC bC u₀ (T₁ + n) =
        reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
          (reluApproxMacroRecursionFrom B₁ c₁ A₁ b₁ u₀ T₁) n := by
    intro n hn
    induction n with
    | zero =>
        simpa using hprefix T₁ le_rfl
    | succ n ih =>
        have hnlt : n < T₂ := Nat.lt_of_succ_le hn
        have hidx : T₁ + n < T₁ + T₂ := Nat.add_lt_add_left hnlt T₁
        let k₂ : Fin T₂ := ⟨n, hnlt⟩
        have hk : (⟨T₁ + n, hidx⟩ : Fin (T₁ + T₂)) = Fin.natAdd T₁ k₂ := by
          ext
          rfl
        rw [show T₁ + (n + 1) = (T₁ + n) + 1 by omega]
        rw [reluApproxMacroRecursionFrom, reluApproxMacroRecursionFrom]
        simp only [dif_pos hidx, dif_pos hnlt]
        rw [ih (Nat.le_of_lt hnlt)]
        rw [show (⟨T₁ + n, hidx⟩ : Fin (T₁ + T₂)) = Fin.natAdd T₁ k₂ from hk]
        simp only [AC, bC, BC, cC, reluApproxConcatUpdateSchedule,
          reluApproxConcatUpdateBiasSchedule, reluApproxConcatFeatureSchedule,
          reluApproxConcatFeatureBiasSchedule, Fin.addCases_right]
        exact reluApproxMacro_padRight_exact (h₁ := h₁)
          (B₂ k₂) (c₂ k₂) (A₂ k₂) (b₂ k₂)
          (reluApproxMacroRecursionFrom B₂ c₂ A₂ b₂
            (reluApproxMacroRecursionFrom B₁ c₁ A₁ b₁ u₀ T₁) n)
  simpa [BC, cC, AC, bC] using hsuffix T₂ le_rfl

/-! ## Persistent-state network workspace

The terminal polynomial computation in the shallow ReLU machine must run a
ReLU layer on temporary registers while retaining the selected input, center,
Taylor coefficients, and code tails.  The following macro performs exactly
that operation: it preserves a prefix of `p` real registers and replaces a
workspace of `w` registers by the ReLU output of an arbitrary dense layer.
-/

/-- Feature width needed to preserve `p` signed registers while evaluating a
`w`-output dense layer. -/
def reluApproxPersistentWorkFeatureSize (p w : ℕ) : ℕ :=
  (p + p) + w

/-- Features consisting of positive/negative copies of the persistent prefix
and the preactivations of an arbitrary dense layer on the complete state. -/
private noncomputable def reluApproxPersistentWorkFeatureMatrix {p w : ℕ}
    (L : DenseLayer (p + w) w) :
    Matrix (Fin (reluApproxPersistentWorkFeatureSize p w)) (Fin (p + w)) ℝ :=
  Fin.addCases
    (Fin.addCases
      (fun i j ↦ if j = Fin.castAdd w i then 1 else 0)
      (fun i j ↦ if j = Fin.castAdd w i then -1 else 0))
    L.weight

/-- Bias companion of `reluApproxPersistentWorkFeatureMatrix`. -/
private noncomputable def reluApproxPersistentWorkFeatureBias {p w : ℕ}
    (L : DenseLayer (p + w) w) :
    Fin (reluApproxPersistentWorkFeatureSize p w) → ℝ :=
  Fin.addCases (fun _ : Fin (p + p) ↦ 0) L.bias

@[simp] theorem reluApproxPersistentWorkFeatureMatrix_pos {p w : ℕ}
    (L : DenseLayer (p + w) w) (i : Fin p) (j : Fin (p + w)) :
    reluApproxPersistentWorkFeatureMatrix L
        (Fin.castAdd w (Fin.castAdd p i)) j =
      (if j = Fin.castAdd w i then 1 else 0) := by
  unfold reluApproxPersistentWorkFeatureMatrix
  rw [Fin.addCases_left, Fin.addCases_left]

@[simp] theorem reluApproxPersistentWorkFeatureMatrix_neg {p w : ℕ}
    (L : DenseLayer (p + w) w) (i : Fin p) (j : Fin (p + w)) :
    reluApproxPersistentWorkFeatureMatrix L
        (Fin.castAdd w (Fin.natAdd p i)) j =
      (if j = Fin.castAdd w i then -1 else 0) := by
  unfold reluApproxPersistentWorkFeatureMatrix
  rw [Fin.addCases_left, Fin.addCases_right]

@[simp] theorem reluApproxPersistentWorkFeatureMatrix_work {p w : ℕ}
    (L : DenseLayer (p + w) w) (i : Fin w) (j : Fin (p + w)) :
    reluApproxPersistentWorkFeatureMatrix L
        (Fin.natAdd (p + p) i) j = L.weight i j := by
  unfold reluApproxPersistentWorkFeatureMatrix
  rw [Fin.addCases_right]

@[simp] theorem reluApproxPersistentWorkFeatureBias_signed {p w : ℕ}
    (L : DenseLayer (p + w) w) (i : Fin (p + p)) :
    reluApproxPersistentWorkFeatureBias L (Fin.castAdd w i) = 0 := by
  exact Fin.addCases_left i

@[simp] theorem reluApproxPersistentWorkFeatureBias_work {p w : ℕ}
    (L : DenseLayer (p + w) w) (i : Fin w) :
    reluApproxPersistentWorkFeatureBias L (Fin.natAdd (p + p) i) = L.bias i := by
  exact Fin.addCases_right i

/-- Update matrix which decodes the persistent signed pairs and copies the
dense-layer ReLU outputs into the work suffix. -/
private noncomputable def reluApproxPersistentWorkUpdateMatrix (p w : ℕ) :
    Matrix (Fin (p + w)) (Fin (reluApproxPersistentWorkFeatureSize p w)) ℝ :=
  Fin.addCases
    (fun i ↦ Fin.addCases
      (Fin.addCases (fun j ↦ if j = i then 1 else 0)
        (fun j ↦ if j = i then -1 else 0))
      (fun _ ↦ 0))
    (fun i ↦ Fin.addCases (fun _ : Fin (p + p) ↦ 0)
      (fun j ↦ if j = i then 1 else 0))

/-- The feature layer is the signed persistent prefix followed by the dense
layer's ReLU output. -/
private theorem reluApproxPersistentWorkFeatures_exact {p w : ℕ}
    (L : DenseLayer (p + w) w) (u : Fin (p + w) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxPersistentWorkFeatureMatrix L)
      (reluApproxPersistentWorkFeatureBias L) u i)) =
      Fin.addCases
        (reluApproxSignedEncode (fun k : Fin p ↦ u (Fin.castAdd w k)))
        (L.reluApply u) := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have hsum :
          (∑ q : Fin (p + w),
            reluApproxPersistentWorkFeatureMatrix L
                (Fin.castAdd w (Fin.castAdd p k)) q * u q) =
            u (Fin.castAdd w k) := by
        rw [Finset.sum_eq_single (Fin.castAdd w k)]
        · rw [reluApproxPersistentWorkFeatureMatrix_pos]
          simp
        · intro q _hq hq
          rw [reluApproxPersistentWorkFeatureMatrix_pos]
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxPersistentWorkFeatureBias, Fin.addCases_left]
      rw [hsum]
      simp [reluApproxSignedEncode]
    · intro k
      have hsum :
          (∑ q : Fin (p + w),
            reluApproxPersistentWorkFeatureMatrix L
                (Fin.castAdd w (Fin.natAdd p k)) q * u q) =
            -u (Fin.castAdd w k) := by
        rw [Finset.sum_eq_single (Fin.castAdd w k)]
        · rw [reluApproxPersistentWorkFeatureMatrix_neg]
          simp
        · intro q _hq hq
          rw [reluApproxPersistentWorkFeatureMatrix_neg]
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxPersistentWorkFeatureBias, Fin.addCases_left]
      rw [hsum]
      rw [reluApproxSignedEncode_natAdd]
      simp
  · intro k
    simp [reluApproxFiniteAffineMap, reluApproxPersistentWorkFeatureMatrix,
      reluApproxPersistentWorkFeatureBias, DenseLayer.reluApply, DenseLayer.apply,
      reluVec, Fin.addCases_right]

/-- One signed-state macro preserves the persistent prefix and evaluates the
given dense ReLU layer in the work suffix. -/
private theorem reluApproxPersistentWorkMacro_exact {p w : ℕ}
    (L : DenseLayer (p + w) w) (u : Fin (p + w) → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxPersistentWorkUpdateMatrix p w) (fun _ ↦ 0)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxPersistentWorkFeatureMatrix L)
          (reluApproxPersistentWorkFeatureBias L) u i)) =
      Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd w i)) (L.reluApply u) := by
  classical
  rw [reluApproxPersistentWorkFeatures_exact]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxPersistentWorkUpdateMatrix,
      reluApproxPersistentWorkFeatureSize, Fin.addCases_left,
      Fin.sum_univ_add, Fin.addCases_right, zero_mul,
      Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · rw [reluApproxSignedEncode_natAdd]
      simpa using reluApproxSignedEncode_sub (u (Fin.castAdd w k))
    · intro b _hb hbk
      simp [hbk]
    · simp
    · intro b _hb hbk
      simp [hbk]
    · simp
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxPersistentWorkUpdateMatrix,
      reluApproxPersistentWorkFeatureSize, Fin.addCases_right,
      Fin.sum_univ_add, Fin.addCases_left, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _hb hbk
      simp [hbk]
    · simp

/-! ## Persistent dense computations -/

/-- Regard a dense layer on the work suffix as a layer on the complete state,
ignoring the persistent prefix. -/
private noncomputable def reluApproxLiftWorkDenseLayer {p w : ℕ}
    (L : DenseLayer w w) : DenseLayer (p + w) w where
  weight i := Fin.addCases (fun _ : Fin p ↦ 0) (L.weight i)
  bias := L.bias

private theorem reluApproxLiftWorkDenseLayer_reluApply {p w : ℕ}
    (L : DenseLayer w w) (a : Fin p → ℝ) (v : Fin w → ℝ) :
    (reluApproxLiftWorkDenseLayer L).reluApply (Fin.addCases a v) =
      L.reluApply v := by
  classical
  funext i
  simp [reluApproxLiftWorkDenseLayer, DenseLayer.reluApply, DenseLayer.apply,
    reluVec, Fin.sum_univ_add]

/-- The first layer consumes the complete state; every later layer consumes
only the work suffix. -/
private noncomputable def reluApproxPersistentDenseScheduleLayer {p w T : ℕ}
    (input : DenseLayer (p + w) w) (hidden : Fin T → DenseLayer w w)
    (k : Fin (T + 1)) : DenseLayer (p + w) w :=
  if hk : k.val = 0 then input
  else reluApproxLiftWorkDenseLayer
    (hidden ⟨k.val - 1, by omega⟩)

/-- Work states generated by an input layer followed by `T` hidden layers. -/
private noncomputable def reluApproxDenseWorkRecursion {p w T : ℕ}
    (input : DenseLayer (p + w) w) (hidden : Fin T → DenseLayer w w)
    (u : Fin (p + w) → ℝ) : ℕ → Fin w → ℝ
  | 0 => input.reluApply u
  | k + 1 =>
      if hk : k < T then
        (hidden ⟨k, hk⟩).reluApply
          (reluApproxDenseWorkRecursion input hidden u k)
      else reluApproxDenseWorkRecursion input hidden u k

/-- Running a dense computation in the work suffix preserves the persistent
prefix and produces exactly the prescribed work recursion. -/
private theorem reluApproxPersistentDenseSchedule_exact {p w T : ℕ}
    (input : DenseLayer (p + w) w) (hidden : Fin T → DenseLayer w w)
    (u : Fin (p + w) → ℝ) :
    reluApproxMacroRecursionFrom
        (fun k ↦ reluApproxPersistentWorkFeatureMatrix
          (reluApproxPersistentDenseScheduleLayer input hidden k))
        (fun k ↦ reluApproxPersistentWorkFeatureBias
          (reluApproxPersistentDenseScheduleLayer input hidden k))
        (fun _ ↦ reluApproxPersistentWorkUpdateMatrix p w)
        (fun _ _ ↦ 0) u (T + 1) =
      Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd w i))
        (reluApproxDenseWorkRecursion input hidden u T) := by
  classical
  have hstep : ∀ k : ℕ, k ≤ T →
      reluApproxMacroRecursionFrom
          (fun j ↦ reluApproxPersistentWorkFeatureMatrix
            (reluApproxPersistentDenseScheduleLayer input hidden j))
          (fun j ↦ reluApproxPersistentWorkFeatureBias
            (reluApproxPersistentDenseScheduleLayer input hidden j))
          (fun _ ↦ reluApproxPersistentWorkUpdateMatrix p w)
          (fun _ _ ↦ 0) u (k + 1) =
        Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd w i))
          (reluApproxDenseWorkRecursion input hidden u k) := by
    intro k hk
    induction k with
    | zero =>
        rw [reluApproxMacroRecursionFrom, dif_pos (by omega)]
        simpa [reluApproxPersistentDenseScheduleLayer,
          reluApproxDenseWorkRecursion] using
          (reluApproxPersistentWorkMacro_exact input u)
    | succ k ih =>
        have hkT : k < T := Nat.lt_of_succ_le hk
        rw [reluApproxMacroRecursionFrom, dif_pos (by omega)]
        rw [ih (Nat.le_of_lt hkT)]
        simpa [reluApproxPersistentDenseScheduleLayer,
          reluApproxDenseWorkRecursion, hkT,
          reluApproxLiftWorkDenseLayer_reluApply] using
          (reluApproxPersistentWorkMacro_exact
            (reluApproxLiftWorkDenseLayer (hidden ⟨k, hkT⟩))
            (Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd w i))
              (reluApproxDenseWorkRecursion input hidden u k)))
  simpa using hstep T le_rfl

/-- The work recursion agrees with the hidden-state recursion of a concrete
network whenever its first dense layer has been realized on the ambient
persistent state.  This is the bridge used to run a multiplication or
polynomial subnetwork without discarding the state machine's registers. -/
private theorem reluApproxDenseWorkRecursion_eq_hiddenState {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (input : DenseLayer (p + N.width) N.width)
    (u : Fin (p + N.width) → ℝ) (x : Fin d → ℝ)
    (hinput : input.reluApply u = N.input.reluApply x)
    (t : ℕ) (ht : t ≤ N.depth - 1) :
    reluApproxDenseWorkRecursion input N.hidden u t =
      N.hiddenState x t := by
  induction t with
  | zero =>
      simpa [reluApproxDenseWorkRecursion,
        FullyConnectedReLUNet.hiddenState] using hinput
  | succ t ih =>
      have htlt : t < N.depth - 1 := Nat.lt_of_succ_le ht
      rw [reluApproxDenseWorkRecursion]
      simp only [htlt, ↓reduceDIte]
      rw [FullyConnectedReLUNet.hiddenState]
      simp only [htlt, ↓reduceDIte]
      rw [ih (Nat.le_of_lt htlt)]

/-- Exact persistent-state execution of all hidden layers of a concrete ReLU
network.  The prefix is unchanged and the work suffix is the terminal hidden
state of `N`; the schedule uses one macro for the input layer and one for each
hidden layer. -/
private theorem reluApproxPersistentNetworkSchedule_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (input : DenseLayer (p + N.width) N.width)
    (u : Fin (p + N.width) → ℝ) (x : Fin d → ℝ)
    (hinput : input.reluApply u = N.input.reluApply x) :
    reluApproxMacroRecursionFrom
        (fun k ↦ reluApproxPersistentWorkFeatureMatrix
          (reluApproxPersistentDenseScheduleLayer input N.hidden k))
        (fun k ↦ reluApproxPersistentWorkFeatureBias
          (reluApproxPersistentDenseScheduleLayer input N.hidden k))
        (fun _ ↦ reluApproxPersistentWorkUpdateMatrix p N.width)
        (fun _ _ ↦ 0) u ((N.depth - 1) + 1) =
      Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd N.width i))
        (N.hiddenState x (N.depth - 1)) := by
  rw [reluApproxPersistentDenseSchedule_exact]
  rw [reluApproxDenseWorkRecursion_eq_hiddenState N input u x hinput
    (N.depth - 1) le_rfl]

/-- Compose the input layer of a concrete network with an affine read from a
larger persistent register state.  The work suffix has the same width as the
network, so all later hidden layers can be run by
`reluApproxPersistentNetworkSchedule_exact`. -/
private noncomputable def reluApproxNetworkInputOfAffineRead {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) : DenseLayer (p + N.width) N.width where
  weight o j := ∑ q : Fin d, N.input.weight o q * readMatrix q j
  bias o := (∑ q : Fin d, N.input.weight o q * readBias q) + N.input.bias o

private theorem reluApproxNetworkInputOfAffineRead_apply {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) (u : Fin (p + N.width) → ℝ) :
    (reluApproxNetworkInputOfAffineRead N readMatrix readBias).apply u =
      N.input.apply (reluApproxFiniteAffineMap readMatrix readBias u) := by
  classical
  funext o
  simp only [reluApproxNetworkInputOfAffineRead, DenseLayer.apply,
    reluApproxFiniteAffineMap]
  calc
    (∑ x, (∑ q, N.input.weight o q * readMatrix q x) * u x) +
          ((∑ q, N.input.weight o q * readBias q) + N.input.bias o) =
        (∑ q, N.input.weight o q * (∑ x, readMatrix q x * u x)) +
          ((∑ q, N.input.weight o q * readBias q) + N.input.bias o) := by
      congr 1
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, N.input.weight o x *
          ((∑ j, readMatrix x j * u j) + readBias x) + N.input.bias o := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      ring

private theorem reluApproxNetworkInputOfAffineRead_reluApply {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) (u : Fin (p + N.width) → ℝ) :
    (reluApproxNetworkInputOfAffineRead N readMatrix readBias).reluApply u =
      N.input.reluApply
        (reluApproxFiniteAffineMap readMatrix readBias u) := by
  simp only [DenseLayer.reluApply, reluVec]
  rw [reluApproxNetworkInputOfAffineRead_apply]

/-- Run a concrete ReLU network on an affine read of the current state while
preserving the first `p` registers exactly. -/
private theorem reluApproxPersistentNetworkOfAffineRead_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) (u : Fin (p + N.width) → ℝ) :
    reluApproxMacroRecursionFrom
        (fun k ↦ reluApproxPersistentWorkFeatureMatrix
          (reluApproxPersistentDenseScheduleLayer
            (reluApproxNetworkInputOfAffineRead N readMatrix readBias)
            N.hidden k))
        (fun k ↦ reluApproxPersistentWorkFeatureBias
          (reluApproxPersistentDenseScheduleLayer
            (reluApproxNetworkInputOfAffineRead N readMatrix readBias)
            N.hidden k))
        (fun _ ↦ reluApproxPersistentWorkUpdateMatrix p N.width)
        (fun _ _ ↦ 0) u ((N.depth - 1) + 1) =
      Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd N.width i))
        (N.hiddenState
          (reluApproxFiniteAffineMap readMatrix readBias u)
          (N.depth - 1)) := by
  exact reluApproxPersistentNetworkSchedule_exact N
    (reluApproxNetworkInputOfAffineRead N readMatrix readBias) u
    (reluApproxFiniteAffineMap readMatrix readBias u)
    (reluApproxNetworkInputOfAffineRead_reluApply N readMatrix readBias u)

/-! ## Persistent network output writeback -/

/-- Update matrix which writes an affine network output into one designated
persistent register.  All other persistent registers are reconstructed from
their signed copies and the temporary work suffix is cleared. -/
private noncomputable def reluApproxPersistentNetworkOutputUpdateMatrix {p w : ℕ}
    (dst : Fin p) (outputWeight : Fin w → ℝ) :
    Matrix (Fin (p + w)) (Fin (reluApproxPersistentWorkFeatureSize p w)) ℝ :=
  Fin.addCases
    (fun i ↦ if i = dst then
      Fin.addCases (fun _ : Fin (p + p) ↦ 0) outputWeight
    else
      Fin.addCases
        (Fin.addCases (fun j ↦ if j = i then 1 else 0)
          (fun j ↦ if j = i then -1 else 0))
        (fun _ ↦ 0))
    (fun _ _ ↦ 0)

/-- Bias companion of `reluApproxPersistentNetworkOutputUpdateMatrix`. -/
private noncomputable def reluApproxPersistentNetworkOutputUpdateBias {p w : ℕ}
    (dst : Fin p) (outputBias : ℝ) : Fin (p + w) → ℝ :=
  Fin.addCases (fun i ↦ if i = dst then outputBias else 0) (fun _ ↦ 0)

/-- One macro reads a nonnegative terminal hidden state, writes the concrete
network's scalar affine output into `dst`, preserves every other persistent
register, and clears the work suffix. -/
private theorem reluApproxPersistentNetworkOutputWrite_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p) (x : Fin d → ℝ)
    (a : Fin p → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxPersistentNetworkOutputUpdateMatrix dst N.outputWeight)
        (reluApproxPersistentNetworkOutputUpdateBias dst N.outputBias)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxPersistentWorkFeatureMatrix
            (reluApproxLiftWorkDenseLayer
              (reluApproxIdentityDenseLayer N.width)))
          (reluApproxPersistentWorkFeatureBias
            (reluApproxLiftWorkDenseLayer
              (reluApproxIdentityDenseLayer N.width)))
          (Fin.addCases a (N.hiddenState x (N.depth - 1))) i)) =
      Fin.addCases
        (fun i ↦ if i = dst then N.realize x else a i)
        (fun _ : Fin N.width ↦ 0) := by
  classical
  rw [reluApproxPersistentWorkFeatures_exact]
  rw [reluApproxLiftWorkDenseLayer_reluApply]
  · rw [reluApproxIdentityDenseLayer_reluApply]
    · funext i
      simp only [Fin.addCases_left]
      refine Fin.addCases ?_ ?_ i
      · intro k
        by_cases hk : k = dst
        · subst k
          simp only [reluApproxFiniteAffineMap,
            reluApproxPersistentNetworkOutputUpdateMatrix,
            reluApproxPersistentNetworkOutputUpdateBias,
            reluApproxPersistentWorkFeatureSize,
            Fin.addCases_left, if_pos]
          rw [Fin.sum_univ_add]
          simp [FullyConnectedReLUNet.realize]
        · simp only [reluApproxFiniteAffineMap,
            reluApproxPersistentNetworkOutputUpdateMatrix,
            reluApproxPersistentNetworkOutputUpdateBias,
            reluApproxPersistentWorkFeatureSize,
            Fin.addCases_left, hk, if_false]
          rw [Fin.sum_univ_add]
          simp only [
            Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
          rw [Fin.sum_univ_add]
          rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
          · simp only [Fin.addCases_left, Fin.addCases_right, if_pos,
              one_mul, neg_one_mul]
            rw [reluApproxSignedEncode_natAdd]
            simpa using reluApproxSignedEncode_sub (a k)
          · intro j _hj hjk
            rw [Fin.addCases_left, Fin.addCases_left]
            rw [Fin.addCases_right]
            rw [if_neg hjk, zero_mul]
          · simp
          · intro j _hj hjk
            simp [Fin.addCases_left, Fin.addCases_right, hjk]
          · simp
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxPersistentNetworkOutputUpdateMatrix,
          reluApproxPersistentNetworkOutputUpdateBias,
          reluApproxPersistentWorkFeatureSize,
          Fin.addCases_right]
        rw [Fin.sum_univ_add]
        simp
    · exact fullyConnectedReLUNet_hiddenState_nonneg N x (N.depth - 1)

/-- Update matrix which adds an affine network output to one designated
persistent register.  The signed persistent features reconstruct the old
register value, the work features contribute the network output, and every
other persistent register is copied unchanged. -/
private noncomputable def reluApproxPersistentNetworkOutputAddUpdateMatrix {p w : ℕ}
    (dst : Fin p) (outputWeight : Fin w → ℝ) :
    Matrix (Fin (p + w)) (Fin (reluApproxPersistentWorkFeatureSize p w)) ℝ :=
  Fin.addCases
    (fun i ↦ if i = dst then
      Fin.addCases
        (Fin.addCases (fun j ↦ if j = i then 1 else 0)
          (fun j ↦ if j = i then -1 else 0))
        outputWeight
    else
      Fin.addCases
        (Fin.addCases (fun j ↦ if j = i then 1 else 0)
          (fun j ↦ if j = i then -1 else 0))
        (fun _ ↦ 0))
    (fun _ _ ↦ 0)

/-- Bias companion of
`reluApproxPersistentNetworkOutputAddUpdateMatrix`. -/
private noncomputable def reluApproxPersistentNetworkOutputAddUpdateBias {p w : ℕ}
    (dst : Fin p) (outputBias : ℝ) : Fin (p + w) → ℝ :=
  Fin.addCases (fun i ↦ if i = dst then outputBias else 0) (fun _ ↦ 0)

/-- One macro adds the concrete network's scalar output to `dst`, preserves
all other persistent registers, and clears the temporary work suffix. -/
private theorem reluApproxPersistentNetworkOutputAdd_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p) (x : Fin d → ℝ)
    (a : Fin p → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxPersistentNetworkOutputAddUpdateMatrix dst N.outputWeight)
        (reluApproxPersistentNetworkOutputAddUpdateBias dst N.outputBias)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxPersistentWorkFeatureMatrix
            (reluApproxLiftWorkDenseLayer
              (reluApproxIdentityDenseLayer N.width)))
          (reluApproxPersistentWorkFeatureBias
            (reluApproxLiftWorkDenseLayer
              (reluApproxIdentityDenseLayer N.width)))
          (Fin.addCases a (N.hiddenState x (N.depth - 1))) i)) =
      Fin.addCases
        (fun i ↦ if i = dst then a i + N.realize x else a i)
        (fun _ : Fin N.width ↦ 0) := by
  classical
  rw [reluApproxPersistentWorkFeatures_exact]
  rw [reluApproxLiftWorkDenseLayer_reluApply]
  · rw [reluApproxIdentityDenseLayer_reluApply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro k
        by_cases hk : k = dst
        · subst k
          simp only [reluApproxFiniteAffineMap,
            reluApproxPersistentNetworkOutputAddUpdateMatrix,
            reluApproxPersistentNetworkOutputAddUpdateBias,
            reluApproxPersistentWorkFeatureSize,
            Fin.addCases_left, if_pos]
          rw [Fin.sum_univ_add, Fin.sum_univ_add]
          rw [Finset.sum_eq_single dst, Finset.sum_eq_single dst]
          · simp only [Fin.addCases_left, Fin.addCases_right, if_pos,
              one_mul, neg_one_mul]
            rw [reluApproxSignedEncode_castAdd,
              reluApproxSignedEncode_natAdd]
            have hsigned : relu (a dst) + -relu (-a dst) = a dst := by
              simpa [sub_eq_add_neg] using reluApproxSignedEncode_sub (a dst)
            rw [hsigned]
            simp [FullyConnectedReLUNet.realize]
            ring
          · intro j _hj hj
            rw [Fin.addCases_left, Fin.addCases_left]
            rw [Fin.addCases_right]
            rw [if_neg hj, zero_mul]
          · simp
          · intro j _hj hj
            simp [Fin.addCases_left, Fin.addCases_right, hj]
          · simp
        · simp only [reluApproxFiniteAffineMap,
            reluApproxPersistentNetworkOutputAddUpdateMatrix,
            reluApproxPersistentNetworkOutputAddUpdateBias,
            reluApproxPersistentWorkFeatureSize,
            Fin.addCases_left, hk, if_false]
          rw [Fin.sum_univ_add]
          simp only [Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
          rw [Fin.sum_univ_add]
          rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
          · simp only [Fin.addCases_left, Fin.addCases_right, if_pos,
              one_mul, neg_one_mul]
            rw [reluApproxSignedEncode_natAdd]
            simpa using reluApproxSignedEncode_sub (a k)
          · intro j _hj hjk
            rw [Fin.addCases_left, Fin.addCases_left]
            rw [Fin.addCases_right]
            rw [if_neg hjk, zero_mul]
          · simp
          · intro j _hj hjk
            simp [Fin.addCases_left, Fin.addCases_right, hjk]
          · simp
      · intro k
        simp only [reluApproxFiniteAffineMap,
          reluApproxPersistentNetworkOutputAddUpdateMatrix,
          reluApproxPersistentNetworkOutputAddUpdateBias,
          reluApproxPersistentWorkFeatureSize, Fin.addCases_right]
        rw [Fin.sum_univ_add]
        simp
    · exact fullyConnectedReLUNet_hiddenState_nonneg N x (N.depth - 1)

/-! ## Register instruction for a concrete subnetwork -/

/-- Feature schedule which runs `N` on an affine read of the current registers,
then exposes its terminal affine output for writeback. -/
noncomputable def reluApproxPersistentNetworkInstructionFeatureSchedule {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) :
    Fin (((N.depth - 1) + 1) + 1) →
      Matrix (Fin (reluApproxPersistentWorkFeatureSize p N.width +
        reluApproxPersistentWorkFeatureSize p N.width)) (Fin (p + N.width)) ℝ :=
  reluApproxConcatFeatureSchedule
    (fun k ↦ reluApproxPersistentWorkFeatureMatrix
      (reluApproxPersistentDenseScheduleLayer
        (reluApproxNetworkInputOfAffineRead N readMatrix readBias) N.hidden k))
    (fun _ : Fin 1 ↦ reluApproxPersistentWorkFeatureMatrix
      (reluApproxLiftWorkDenseLayer
        (reluApproxIdentityDenseLayer N.width)))

/-- Bias schedule paired with
`reluApproxPersistentNetworkInstructionFeatureSchedule`. -/
noncomputable def reluApproxPersistentNetworkInstructionFeatureBiasSchedule {d p : ℕ}
    (N : FullyConnectedReLUNet d)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) :
    Fin (((N.depth - 1) + 1) + 1) →
      Fin (reluApproxPersistentWorkFeatureSize p N.width +
        reluApproxPersistentWorkFeatureSize p N.width) → ℝ :=
  reluApproxConcatFeatureBiasSchedule
    (fun k ↦ reluApproxPersistentWorkFeatureBias
      (reluApproxPersistentDenseScheduleLayer
        (reluApproxNetworkInputOfAffineRead N readMatrix readBias) N.hidden k))
    (fun _ : Fin 1 ↦ reluApproxPersistentWorkFeatureBias
      (reluApproxLiftWorkDenseLayer
        (reluApproxIdentityDenseLayer N.width)))

/-- Update schedule paired with
`reluApproxPersistentNetworkInstructionFeatureSchedule`. -/
noncomputable def reluApproxPersistentNetworkInstructionUpdateSchedule {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p) :
    Fin (((N.depth - 1) + 1) + 1) →
      Matrix (Fin (p + N.width))
        (Fin (reluApproxPersistentWorkFeatureSize p N.width +
          reluApproxPersistentWorkFeatureSize p N.width)) ℝ :=
  reluApproxConcatUpdateSchedule
    (fun _ : Fin ((N.depth - 1) + 1) ↦
      reluApproxPersistentWorkUpdateMatrix p N.width)
    (fun _ : Fin 1 ↦
      reluApproxPersistentNetworkOutputUpdateMatrix dst N.outputWeight)

/-- Update-bias schedule paired with
`reluApproxPersistentNetworkInstructionFeatureSchedule`. -/
noncomputable def reluApproxPersistentNetworkInstructionUpdateBiasSchedule {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p) :
    Fin (((N.depth - 1) + 1) + 1) → Fin (p + N.width) → ℝ :=
  reluApproxConcatUpdateBiasSchedule
    (fun _ : Fin ((N.depth - 1) + 1) ↦ fun _ ↦ 0)
    (fun _ : Fin 1 ↦
      reluApproxPersistentNetworkOutputUpdateBias dst N.outputBias)

/-- A complete register instruction: evaluate `N` on an affine read of the
current state, write its scalar output to `dst`, preserve every other
persistent register, and clear the work suffix. -/
private theorem reluApproxPersistentNetworkInstruction_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) (u : Fin (p + N.width) → ℝ) :
    reluApproxMacroRecursionFrom
        (reluApproxPersistentNetworkInstructionFeatureSchedule N readMatrix readBias)
        (reluApproxPersistentNetworkInstructionFeatureBiasSchedule N readMatrix readBias)
        (reluApproxPersistentNetworkInstructionUpdateSchedule N dst)
        (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst)
        u (((N.depth - 1) + 1) + 1) =
      Fin.addCases
        (fun i : Fin p ↦ if i = dst then
          N.realize (reluApproxFiniteAffineMap readMatrix readBias u)
        else u (Fin.castAdd N.width i))
        (fun _ : Fin N.width ↦ 0) := by
  unfold reluApproxPersistentNetworkInstructionFeatureSchedule
    reluApproxPersistentNetworkInstructionFeatureBiasSchedule
    reluApproxPersistentNetworkInstructionUpdateSchedule
    reluApproxPersistentNetworkInstructionUpdateBiasSchedule
  rw [reluApproxMacroRecursionFrom_concat]
  rw [reluApproxPersistentNetworkOfAffineRead_exact]
  rw [reluApproxMacroRecursionFrom, dif_pos (by omega)]
  simpa using
    (reluApproxPersistentNetworkOutputWrite_exact N dst
      (reluApproxFiniteAffineMap readMatrix readBias u)
      (fun i : Fin p ↦ u (Fin.castAdd N.width i)))

/-- Update schedule for the additive form of the persistent network
instruction. -/
private noncomputable def reluApproxPersistentNetworkInstructionAddUpdateSchedule
    {d p : ℕ} (N : FullyConnectedReLUNet d) (dst : Fin p) :
    Fin (((N.depth - 1) + 1) + 1) →
      Matrix (Fin (p + N.width))
        (Fin (reluApproxPersistentWorkFeatureSize p N.width +
          reluApproxPersistentWorkFeatureSize p N.width)) ℝ :=
  reluApproxConcatUpdateSchedule
    (fun _ : Fin ((N.depth - 1) + 1) ↦
      reluApproxPersistentWorkUpdateMatrix p N.width)
    (fun _ : Fin 1 ↦
      reluApproxPersistentNetworkOutputAddUpdateMatrix dst N.outputWeight)

/-- Update-bias schedule for the additive persistent network instruction. -/
private noncomputable def reluApproxPersistentNetworkInstructionAddUpdateBiasSchedule
    {d p : ℕ} (N : FullyConnectedReLUNet d) (dst : Fin p) :
    Fin (((N.depth - 1) + 1) + 1) → Fin (p + N.width) → ℝ :=
  reluApproxConcatUpdateBiasSchedule
    (fun _ : Fin ((N.depth - 1) + 1) ↦ fun _ ↦ 0)
    (fun _ : Fin 1 ↦
      reluApproxPersistentNetworkOutputAddUpdateBias dst N.outputBias)

/-- Evaluate `N` on an affine read of the current state and add its scalar
output to `dst`.  All other persistent registers are preserved and the work
suffix is cleared. -/
private theorem reluApproxPersistentNetworkInstructionAdd_exact {d p : ℕ}
    (N : FullyConnectedReLUNet d) (dst : Fin p)
    (readMatrix : Matrix (Fin d) (Fin (p + N.width)) ℝ)
    (readBias : Fin d → ℝ) (u : Fin (p + N.width) → ℝ) :
    reluApproxMacroRecursionFrom
        (reluApproxPersistentNetworkInstructionFeatureSchedule N readMatrix readBias)
        (reluApproxPersistentNetworkInstructionFeatureBiasSchedule N readMatrix readBias)
        (reluApproxPersistentNetworkInstructionAddUpdateSchedule N dst)
        (reluApproxPersistentNetworkInstructionAddUpdateBiasSchedule N dst)
        u (((N.depth - 1) + 1) + 1) =
      Fin.addCases
        (fun i : Fin p ↦ if i = dst then
          u (Fin.castAdd N.width i) +
            N.realize (reluApproxFiniteAffineMap readMatrix readBias u)
        else u (Fin.castAdd N.width i))
        (fun _ : Fin N.width ↦ 0) := by
  unfold reluApproxPersistentNetworkInstructionFeatureSchedule
    reluApproxPersistentNetworkInstructionFeatureBiasSchedule
    reluApproxPersistentNetworkInstructionAddUpdateSchedule
    reluApproxPersistentNetworkInstructionAddUpdateBiasSchedule
  rw [reluApproxMacroRecursionFrom_concat]
  rw [reluApproxPersistentNetworkOfAffineRead_exact]
  rw [reluApproxMacroRecursionFrom, dif_pos (by omega)]
  simpa using
    (reluApproxPersistentNetworkOutputAdd_exact N dst
      (reluApproxFiniteAffineMap readMatrix readBias u)
      (fun i : Fin p ↦ u (Fin.castAdd N.width i)))

/-! ## State-preserving macro embedding

The state machine uses one common register vector, while its coarse selector,
digit decoder, and terminal evaluator naturally act on different suffixes.  The
following construction embeds an arbitrary signed-state macro on a suffix and
copies a persistent prefix exactly.
-/

/-- Feature width for a suffix macro with `p` persistent registers. -/
private def reluApproxPersistentMacroFeatureSize (p h : ℕ) : ℕ :=
  (p + p) + h

/-- Feature matrix which signed-encodes the persistent prefix and applies the
embedded macro's feature matrix to the suffix. -/
private noncomputable def reluApproxPersistentMacroFeatureMatrix {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) :
    Matrix (Fin (reluApproxPersistentMacroFeatureSize p h)) (Fin (p + s)) ℝ :=
  Fin.addCases
    (Fin.addCases
      (fun i j ↦ if j = Fin.castAdd s i then 1 else 0)
      (fun i j ↦ if j = Fin.castAdd s i then -1 else 0))
    (fun i ↦ Fin.addCases (fun _ : Fin p ↦ 0) (B i))

/-- Bias companion of `reluApproxPersistentMacroFeatureMatrix`. -/
private noncomputable def reluApproxPersistentMacroFeatureBias {p h : ℕ}
    (c : Fin h → ℝ) : Fin (reluApproxPersistentMacroFeatureSize p h) → ℝ :=
  Fin.addCases (fun _ : Fin (p + p) ↦ 0) c

@[simp] theorem reluApproxPersistentMacroFeatureMatrix_pos {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (i : Fin p) (j : Fin (p + s)) :
    reluApproxPersistentMacroFeatureMatrix B
        (Fin.castAdd h (Fin.castAdd p i)) j =
      (if j = Fin.castAdd s i then 1 else 0) := by
  unfold reluApproxPersistentMacroFeatureMatrix
  rw [Fin.addCases_left, Fin.addCases_left]

@[simp] theorem reluApproxPersistentMacroFeatureMatrix_neg {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (i : Fin p) (j : Fin (p + s)) :
    reluApproxPersistentMacroFeatureMatrix B
        (Fin.castAdd h (Fin.natAdd p i)) j =
      (if j = Fin.castAdd s i then -1 else 0) := by
  unfold reluApproxPersistentMacroFeatureMatrix
  rw [Fin.addCases_left, Fin.addCases_right]

@[simp] theorem reluApproxPersistentMacroFeatureMatrix_work {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (i : Fin h) (j : Fin (p + s)) :
    reluApproxPersistentMacroFeatureMatrix B
        (Fin.natAdd (p + p) i) j =
      Fin.addCases (fun _ : Fin p ↦ 0) (B i) j := by
  unfold reluApproxPersistentMacroFeatureMatrix
  rw [Fin.addCases_right]

@[simp] theorem reluApproxPersistentMacroFeatureBias_signed {p h : ℕ}
    (c : Fin h → ℝ) (i : Fin (p + p)) :
    reluApproxPersistentMacroFeatureBias c (Fin.castAdd h i) = 0 := by
  exact Fin.addCases_left i

@[simp] theorem reluApproxPersistentMacroFeatureBias_work {p h : ℕ}
    (c : Fin h → ℝ) (i : Fin h) :
    reluApproxPersistentMacroFeatureBias c (Fin.natAdd (p + p) i) = c i := by
  exact Fin.addCases_right i

/-- Update matrix which decodes the persistent signed pairs and applies the
embedded macro's update matrix to the suffix feature block. -/
private noncomputable def reluApproxPersistentMacroUpdateMatrix {p s h : ℕ}
    (A : Matrix (Fin s) (Fin h) ℝ) :
    Matrix (Fin (p + s)) (Fin (reluApproxPersistentMacroFeatureSize p h)) ℝ :=
  Fin.addCases
    (fun i ↦ Fin.addCases
      (Fin.addCases (fun j ↦ if j = i then 1 else 0)
        (fun j ↦ if j = i then -1 else 0))
      (fun _ ↦ 0))
    (fun i ↦ Fin.addCases (fun _ : Fin (p + p) ↦ 0) (A i))

/-- Bias companion of `reluApproxPersistentMacroUpdateMatrix`. -/
private noncomputable def reluApproxPersistentMacroUpdateBias {p s : ℕ}
    (b : Fin s → ℝ) : Fin (p + s) → ℝ :=
  Fin.addCases (fun _ : Fin p ↦ 0) b

/-- The embedded feature layer is the signed persistent prefix followed by
the original macro features evaluated on the suffix. -/
private theorem reluApproxPersistentMacroFeatures_exact {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (u : Fin (p + s) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxPersistentMacroFeatureMatrix B)
      (reluApproxPersistentMacroFeatureBias c) u i)) =
      Fin.addCases
        (reluApproxSignedEncode (fun k : Fin p ↦ u (Fin.castAdd s k)))
        (fun i ↦ relu (reluApproxFiniteAffineMap B c
          (fun j : Fin s ↦ u (Fin.natAdd p j)) i)) := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have hsum :
          (∑ q : Fin (p + s),
            reluApproxPersistentMacroFeatureMatrix B
                (Fin.castAdd h (Fin.castAdd p k)) q * u q) =
            u (Fin.castAdd s k) := by
        rw [Finset.sum_eq_single (Fin.castAdd s k)]
        · rw [reluApproxPersistentMacroFeatureMatrix_pos]
          simp
        · intro q _hq hq
          rw [reluApproxPersistentMacroFeatureMatrix_pos]
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxPersistentMacroFeatureBias, Fin.addCases_left]
      rw [hsum]
      simp [reluApproxSignedEncode]
    · intro k
      have hsum :
          (∑ q : Fin (p + s),
            reluApproxPersistentMacroFeatureMatrix B
                (Fin.castAdd h (Fin.natAdd p k)) q * u q) =
            -u (Fin.castAdd s k) := by
        rw [Finset.sum_eq_single (Fin.castAdd s k)]
        · rw [reluApproxPersistentMacroFeatureMatrix_neg]
          simp
        · intro q _hq hq
          rw [reluApproxPersistentMacroFeatureMatrix_neg]
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxPersistentMacroFeatureBias, Fin.addCases_left]
      rw [hsum]
      rw [reluApproxSignedEncode_natAdd]
      simp
  · intro k
    simp [reluApproxFiniteAffineMap,
      reluApproxPersistentMacroFeatureMatrix,
      reluApproxPersistentMacroFeatureBias, Fin.sum_univ_add]

/-- Exact law for embedding one macro on the suffix of a persistent state. -/
private theorem reluApproxPersistentMacro_exact {p s h : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (A : Matrix (Fin s) (Fin h) ℝ) (b : Fin s → ℝ)
    (u : Fin (p + s) → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxPersistentMacroUpdateMatrix A)
        (reluApproxPersistentMacroUpdateBias b)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxPersistentMacroFeatureMatrix B)
          (reluApproxPersistentMacroFeatureBias c) u i)) =
      Fin.addCases (fun i : Fin p ↦ u (Fin.castAdd s i))
        (reluApproxFiniteAffineMap A b
          (fun i ↦ relu (reluApproxFiniteAffineMap B c
            (fun j : Fin s ↦ u (Fin.natAdd p j)) i))) := by
  classical
  rw [reluApproxPersistentMacroFeatures_exact]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxPersistentMacroUpdateMatrix,
      reluApproxPersistentMacroUpdateBias,
      reluApproxPersistentMacroFeatureSize, Fin.addCases_left,
      Fin.sum_univ_add, Fin.addCases_right, zero_mul,
      Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · rw [reluApproxSignedEncode_natAdd]
      simpa using reluApproxSignedEncode_sub (u (Fin.castAdd s k))
    · intro j _hj hjk
      simp [hjk]
    · simp
    · intro j _hj hjk
      simp [hjk]
    · simp
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxPersistentMacroUpdateMatrix,
      reluApproxPersistentMacroUpdateBias,
      reluApproxPersistentMacroFeatureSize, Fin.addCases_right,
      Fin.sum_univ_add, Fin.addCases_left, zero_mul,
      Finset.sum_const_zero, zero_add]

/-! ## Suffix-preserving macro embedding

The coarse/fine state machine occupies the leading block of the final state.
Its terminal Taylor evaluator uses additional registers after that block.  The
following companion to `reluApproxPersistentMacro_exact` runs a macro on the
leading block and signed-copies an arbitrary persistent suffix. -/

/-- Feature width for a leading-state macro with `p` persistent suffix
registers. -/
def reluApproxMacroWithPersistentSuffixFeatureSize (h p : ℕ) : ℕ :=
  h + (p + p)

/-- Apply the original feature map to the leading state and signed-encode the
persistent suffix. -/
private noncomputable def reluApproxMacroWithPersistentSuffixFeatureMatrix
    {s h p : ℕ} (B : Matrix (Fin h) (Fin s) ℝ) :
    Matrix (Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p))
      (Fin (s + p)) ℝ :=
  Fin.addCases
    (fun i ↦ Fin.addCases (B i) (fun _ : Fin p ↦ 0))
    (Fin.addCases
      (fun i j ↦ if j = Fin.natAdd s i then 1 else 0)
      (fun i j ↦ if j = Fin.natAdd s i then -1 else 0))

/-- Bias companion of
`reluApproxMacroWithPersistentSuffixFeatureMatrix`. -/
private noncomputable def reluApproxMacroWithPersistentSuffixFeatureBias
    {h p : ℕ} (c : Fin h → ℝ) :
    Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p) → ℝ :=
  Fin.addCases c (fun _ : Fin (p + p) ↦ 0)

/-- Decode the original macro output into the leading state and reconstruct
the persistent suffix from its signed feature pairs. -/
private noncomputable def reluApproxMacroWithPersistentSuffixUpdateMatrix
    {s h p : ℕ} (A : Matrix (Fin s) (Fin h) ℝ) :
    Matrix (Fin (s + p))
      (Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p)) ℝ :=
  Fin.addCases
    (fun i ↦ Fin.addCases (A i) (fun _ : Fin (p + p) ↦ 0))
    (fun i ↦ Fin.addCases (fun _ : Fin h ↦ 0)
      (Fin.addCases
        (fun j ↦ if j = i then 1 else 0)
        (fun j ↦ if j = i then -1 else 0)))

/-- Bias companion of
`reluApproxMacroWithPersistentSuffixUpdateMatrix`. -/
private noncomputable def reluApproxMacroWithPersistentSuffixUpdateBias
    {s p : ℕ} (b : Fin s → ℝ) : Fin (s + p) → ℝ :=
  Fin.addCases b (fun _ : Fin p ↦ 0)

/-- The feature layer is the original macro feature vector followed by signed
copies of the persistent suffix. -/
private theorem reluApproxMacroWithPersistentSuffixFeatures_exact {s h p : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (u : Fin (s + p) → ℝ) :
    (fun i ↦ relu (reluApproxFiniteAffineMap
      (reluApproxMacroWithPersistentSuffixFeatureMatrix B)
      (reluApproxMacroWithPersistentSuffixFeatureBias c) u i)) =
      Fin.addCases
        (fun i ↦ relu (reluApproxFiniteAffineMap B c
          (fun j : Fin s ↦ u (Fin.castAdd p j)) i))
        (reluApproxSignedEncode (fun j : Fin p ↦ u (Fin.natAdd s j))) := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp [reluApproxFiniteAffineMap,
      reluApproxMacroWithPersistentSuffixFeatureMatrix,
      reluApproxMacroWithPersistentSuffixFeatureBias,
      Fin.sum_univ_add]
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have hdisjoint (q : Fin s) :
          Fin.castAdd p q ≠ Fin.natAdd s k := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      have hsum :
          (∑ q : Fin (s + p),
            reluApproxMacroWithPersistentSuffixFeatureMatrix B
                (Fin.natAdd h (Fin.castAdd p k)) q * u q) =
            u (Fin.natAdd s k) := by
        rw [Fin.sum_univ_add]
        simp only [reluApproxMacroWithPersistentSuffixFeatureMatrix,
          Fin.addCases_right, Fin.addCases_left]
        simp only [if_neg (hdisjoint _), zero_mul,
          Finset.sum_const_zero, zero_add]
        rw [Finset.sum_eq_single k]
        · simp
        · intro q _hq hq
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxMacroWithPersistentSuffixFeatureBias,
        Fin.addCases_right]
      rw [hsum]
      simp [reluApproxSignedEncode]
    · intro k
      have hdisjoint (q : Fin s) :
          Fin.castAdd p q ≠ Fin.natAdd s k := by
        intro heq
        have hval := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      have hsum :
          (∑ q : Fin (s + p),
            reluApproxMacroWithPersistentSuffixFeatureMatrix B
                (Fin.natAdd h (Fin.natAdd p k)) q * u q) =
            -u (Fin.natAdd s k) := by
        rw [Fin.sum_univ_add]
        simp only [reluApproxMacroWithPersistentSuffixFeatureMatrix,
          Fin.addCases_right, Fin.addCases_left]
        simp only [if_neg (hdisjoint _), zero_mul,
          Finset.sum_const_zero, zero_add]
        rw [Finset.sum_eq_single k]
        · simp
        · intro q _hq hq
          simp [hq]
        · simp
      simp only [reluApproxFiniteAffineMap,
        reluApproxMacroWithPersistentSuffixFeatureBias,
        Fin.addCases_right]
      rw [hsum]
      rw [reluApproxSignedEncode_natAdd]
      simp

/-- Exact law for running one signed-state macro on a leading state block while
preserving a suffix of arbitrary real registers. -/
private theorem reluApproxMacroWithPersistentSuffix_exact {s h p : ℕ}
    (B : Matrix (Fin h) (Fin s) ℝ) (c : Fin h → ℝ)
    (A : Matrix (Fin s) (Fin h) ℝ) (b : Fin s → ℝ)
    (u : Fin (s + p) → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxMacroWithPersistentSuffixUpdateMatrix A)
        (reluApproxMacroWithPersistentSuffixUpdateBias b)
        (fun i ↦ relu (reluApproxFiniteAffineMap
          (reluApproxMacroWithPersistentSuffixFeatureMatrix B)
          (reluApproxMacroWithPersistentSuffixFeatureBias c) u i)) =
      Fin.addCases
        (reluApproxFiniteAffineMap A b
          (fun i ↦ relu (reluApproxFiniteAffineMap B c
            (fun j : Fin s ↦ u (Fin.castAdd p j)) i)))
        (fun i : Fin p ↦ u (Fin.natAdd s i)) := by
  classical
  rw [reluApproxMacroWithPersistentSuffixFeatures_exact]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxMacroWithPersistentSuffixUpdateMatrix,
      reluApproxMacroWithPersistentSuffixUpdateBias,
      reluApproxMacroWithPersistentSuffixFeatureSize,
      Fin.addCases_left, Fin.sum_univ_add, Fin.addCases_right,
      zero_mul, Finset.sum_const_zero, add_zero]
  · intro k
    simp only [reluApproxFiniteAffineMap,
      reluApproxMacroWithPersistentSuffixUpdateMatrix,
      reluApproxMacroWithPersistentSuffixUpdateBias,
      reluApproxMacroWithPersistentSuffixFeatureSize,
      Fin.addCases_right, Fin.sum_univ_add, Fin.addCases_left,
      zero_mul, Finset.sum_const_zero, zero_add, add_zero]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · rw [reluApproxSignedEncode_natAdd]
      simpa using reluApproxSignedEncode_sub (u (Fin.natAdd s k))
    · intro j _hj hjk
      simp [hjk]
    · simp
    · intro j _hj hjk
      simp [hjk]
    · simp

/-- Lift every feature matrix in a macro schedule so the schedule acts on a
leading state block and signed-copies a persistent suffix. -/
noncomputable def reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix
    {s h p T : ℕ} (B : Fin T → Matrix (Fin h) (Fin s) ℝ) :
    Fin T → Matrix
      (Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p))
      (Fin (s + p)) ℝ :=
  fun k ↦ reluApproxMacroWithPersistentSuffixFeatureMatrix (B k)

/-- Bias schedule accompanying
`reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix`. -/
noncomputable def reluApproxMacroScheduleWithPersistentSuffixFeatureBias
    {h p T : ℕ} (c : Fin T → Fin h → ℝ) :
    Fin T → Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p) → ℝ :=
  fun k ↦ reluApproxMacroWithPersistentSuffixFeatureBias (c k)

/-- Lift every update matrix in a macro schedule so the schedule acts on a
leading state block and preserves a suffix. -/
noncomputable def reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix
    {s h p T : ℕ} (A : Fin T → Matrix (Fin s) (Fin h) ℝ) :
    Fin T → Matrix (Fin (s + p))
      (Fin (reluApproxMacroWithPersistentSuffixFeatureSize h p)) ℝ :=
  fun k ↦ reluApproxMacroWithPersistentSuffixUpdateMatrix (A k)

/-- Bias schedule accompanying
`reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix`. -/
noncomputable def reluApproxMacroScheduleWithPersistentSuffixUpdateBias
    {s p T : ℕ} (b : Fin T → Fin s → ℝ) :
    Fin T → Fin (s + p) → ℝ :=
  fun k ↦ reluApproxMacroWithPersistentSuffixUpdateBias (b k)

/-- A lifted macro schedule computes exactly the original recursion in its
leading block and leaves every persistent suffix register unchanged. -/
private theorem reluApproxMacroRecursionFrom_withPersistentSuffix
    {s h p T : ℕ}
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (u : Fin s → ℝ) (work : Fin p → ℝ) (t : ℕ) (ht : t ≤ T) :
    reluApproxMacroRecursionFrom
        (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix B)
        (reluApproxMacroScheduleWithPersistentSuffixFeatureBias c)
        (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix A)
        (reluApproxMacroScheduleWithPersistentSuffixUpdateBias b)
        (Fin.addCases u work) t =
      Fin.addCases (reluApproxMacroRecursionFrom B c A b u t) work := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxMacroRecursionFrom, reluApproxMacroRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      simp only [
        reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix,
        reluApproxMacroScheduleWithPersistentSuffixFeatureBias,
        reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix,
        reluApproxMacroScheduleWithPersistentSuffixUpdateBias]
      rw [reluApproxMacroWithPersistentSuffix_exact]
      simp

/-! ## External-input initialization with persistent work registers -/

/-- Affine read of a prescribed finite family of persistent registers.  The
work suffix is ignored. -/
noncomputable def reluApproxRegisterReadMatrix {n p : ℕ} (work : ℕ)
    (src : Fin n → Fin p) : Matrix (Fin n) (Fin (p + work)) ℝ :=
  fun i j => if j = Fin.castAdd work (src i) then 1 else 0

/-- A register read returns the selected persistent coordinates exactly when
the work suffix is zero. -/
private theorem reluApproxRegisterReadMatrix_exact {n p work : ℕ}
    (src : Fin n → Fin p) (u : Fin p → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxRegisterReadMatrix work src) (fun _ => 0)
        (Fin.addCases u (fun _ : Fin work => 0)) =
      fun i => u (src i) := by
  classical
  funext i
  simp only [reluApproxFiniteAffineMap, add_zero]
  rw [Finset.sum_eq_single (Fin.castAdd work (src i))]
  · simp [reluApproxRegisterReadMatrix]
  · intro j _hj hj
    simp [reluApproxRegisterReadMatrix, hj]
  · simp

/-- Extend the affine input map of a macro program by a zero-initialized work
suffix. -/
noncomputable def reluApproxInputMatrixWithZeroSuffix {d s w : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) : Matrix (Fin (s + w)) (Fin d) ℝ :=
  Fin.addCases A₀ (fun _ _ ↦ 0)

/-- Bias companion of `reluApproxInputMatrixWithZeroSuffix`. -/
noncomputable def reluApproxInputBiasWithZeroSuffix {s w : ℕ}
    (b₀ : Fin s → ℝ) : Fin (s + w) → ℝ :=
  Fin.addCases b₀ (fun _ ↦ 0)

private theorem reluApproxInputWithZeroSuffix_exact {d s w : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) (b₀ : Fin s → ℝ)
    (x : Fin d → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxInputMatrixWithZeroSuffix (w := w) A₀)
        (reluApproxInputBiasWithZeroSuffix (w := w) b₀) x =
      Fin.addCases (reluApproxFiniteAffineMap A₀ b₀ x)
        (fun _ : Fin w ↦ 0) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [reluApproxFiniteAffineMap,
      reluApproxInputMatrixWithZeroSuffix,
      reluApproxInputBiasWithZeroSuffix]
  · intro j
    simp [reluApproxFiniteAffineMap,
      reluApproxInputMatrixWithZeroSuffix,
      reluApproxInputBiasWithZeroSuffix]

/-- Lifting a complete external-input macro program preserves a zero work
suffix at every stage while reproducing the original recursion exactly in the
leading state block. -/
private theorem reluApproxSignedMacroRecursion_withPersistentZeroSuffix
    {d s h w T : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) (b₀ : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ht : t ≤ T) :
    reluApproxSignedMacroRecursion
        (reluApproxInputMatrixWithZeroSuffix (w := w) A₀)
        (reluApproxInputBiasWithZeroSuffix (w := w) b₀)
        (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix (p := w) B)
        (reluApproxMacroScheduleWithPersistentSuffixFeatureBias (p := w) c)
        (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix (p := w) A)
        (reluApproxMacroScheduleWithPersistentSuffixUpdateBias (p := w) b)
        x t =
      Fin.addCases (reluApproxSignedMacroRecursion A₀ b₀ B c A b x t)
        (fun _ : Fin w ↦ 0) := by
  induction t with
  | zero =>
      simpa [reluApproxSignedMacroRecursion] using
        reluApproxInputWithZeroSuffix_exact (w := w) A₀ b₀ x
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxSignedMacroRecursion, reluApproxSignedMacroRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      simp only [
        reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix,
        reluApproxMacroScheduleWithPersistentSuffixFeatureBias,
        reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix,
        reluApproxMacroScheduleWithPersistentSuffixUpdateBias]
      rw [reluApproxMacroWithPersistentSuffix_exact]
      simp

/-- Append a concrete fully connected subnetwork to an arbitrary macro
program.  The first program runs in the leading state block with zero work
registers; the appended instruction reads its terminal state affinely, writes
the subnetwork output to `dst`, and a final linear readout selects that value. -/
private theorem reluApproxSignedMacroRecursion_appendNetworkInstruction_state
    {d n s h T : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) (b₀ : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (N : FullyConnectedReLUNet n) (dst : Fin s)
    (readMatrix : Matrix (Fin n) (Fin (s + N.width)) ℝ)
    (readBias : Fin n → ℝ) (x : Fin d → ℝ) :
    reluApproxSignedMacroRecursion
        (reluApproxInputMatrixWithZeroSuffix (w := N.width) A₀)
        (reluApproxInputBiasWithZeroSuffix (w := N.width) b₀)
        (reluApproxConcatFeatureSchedule
          (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix
            (p := N.width) B)
          (reluApproxPersistentNetworkInstructionFeatureSchedule
            N readMatrix readBias))
        (reluApproxConcatFeatureBiasSchedule
          (reluApproxMacroScheduleWithPersistentSuffixFeatureBias
            (p := N.width) c)
          (reluApproxPersistentNetworkInstructionFeatureBiasSchedule
            N readMatrix readBias))
        (reluApproxConcatUpdateSchedule
          (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix
            (p := N.width) A)
          (reluApproxPersistentNetworkInstructionUpdateSchedule N dst))
        (reluApproxConcatUpdateBiasSchedule
          (reluApproxMacroScheduleWithPersistentSuffixUpdateBias
            (p := N.width) b)
          (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst))
        x (T + (((N.depth - 1) + 1) + 1)) =
      Fin.addCases
        (fun i : Fin s => if i = dst then
          N.realize (reluApproxFiniteAffineMap readMatrix readBias
            (Fin.addCases
              (reluApproxSignedMacroRecursion A₀ b₀ B c A b x T)
              (fun _ : Fin N.width => 0)))
        else reluApproxSignedMacroRecursion A₀ b₀ B c A b x T i)
        (fun _ : Fin N.width => 0) := by
  rw [reluApproxSignedMacroRecursion_concat]
  rw [reluApproxSignedMacroRecursion_withPersistentZeroSuffix
    A₀ b₀ B c A b x T le_rfl]
  simpa using
    (reluApproxPersistentNetworkInstruction_exact N dst readMatrix readBias
      (Fin.addCases
        (reluApproxSignedMacroRecursion A₀ b₀ B c A b x T)
        (fun _ : Fin N.width => 0)))

theorem reluApproxSignedMacroRecursion_appendNetworkInstruction_realize
    {d n s h T : ℕ}
    (A₀ : Matrix (Fin s) (Fin d) ℝ) (b₀ : Fin s → ℝ)
    (B : Fin T → Matrix (Fin h) (Fin s) ℝ) (c : Fin T → Fin h → ℝ)
    (A : Fin T → Matrix (Fin s) (Fin h) ℝ) (b : Fin T → Fin s → ℝ)
    (N : FullyConnectedReLUNet n) (dst : Fin s)
    (readMatrix : Matrix (Fin n) (Fin (s + N.width)) ℝ)
    (readBias : Fin n → ℝ) (x : Fin d → ℝ) :
    (∑ i : Fin (s + N.width),
        (if i = Fin.castAdd N.width dst then 1 else 0) *
          reluApproxSignedMacroRecursion
            (reluApproxInputMatrixWithZeroSuffix (w := N.width) A₀)
            (reluApproxInputBiasWithZeroSuffix (w := N.width) b₀)
            (reluApproxConcatFeatureSchedule
              (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix
                (p := N.width) B)
              (reluApproxPersistentNetworkInstructionFeatureSchedule
                N readMatrix readBias))
            (reluApproxConcatFeatureBiasSchedule
              (reluApproxMacroScheduleWithPersistentSuffixFeatureBias
                (p := N.width) c)
              (reluApproxPersistentNetworkInstructionFeatureBiasSchedule
                N readMatrix readBias))
            (reluApproxConcatUpdateSchedule
              (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix
                (p := N.width) A)
              (reluApproxPersistentNetworkInstructionUpdateSchedule N dst))
            (reluApproxConcatUpdateBiasSchedule
              (reluApproxMacroScheduleWithPersistentSuffixUpdateBias
                (p := N.width) b)
              (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst))
            x (T + (((N.depth - 1) + 1) + 1)) i) =
      N.realize (reluApproxFiniteAffineMap readMatrix readBias
        (Fin.addCases (reluApproxSignedMacroRecursion A₀ b₀ B c A b x T)
          (fun _ : Fin N.width ↦ 0))) := by
  classical
  rw [reluApproxSignedMacroRecursion_concat]
  rw [reluApproxSignedMacroRecursion_withPersistentZeroSuffix
    A₀ b₀ B c A b x T le_rfl]
  rw [reluApproxPersistentNetworkInstruction_exact]
  rw [Finset.sum_eq_single (Fin.castAdd N.width dst)]
  · simp
  · intro j hj hjne
    simp [hj, hjne]
  · simp

/-- A finite fully connected ReLU network realizes a continuous scalar
function. -/
theorem fullyConnectedReLUNet_continuous_realize {d : Nat}
    (N : FullyConnectedReLUNet d) : Continuous N.realize := by
  have hstate : forall n : Nat, Continuous (fun x => N.hiddenState x n) := by
    intro n
    induction n with
    | zero =>
        simp only [FullyConnectedReLUNet.hiddenState]
        unfold DenseLayer.reluApply reluVec DenseLayer.apply relu
        fun_prop
    | succ n ih =>
        by_cases h : n < N.depth - 1
        · rw [show (fun x => N.hiddenState x (n + 1)) =
              fun x => (N.hidden ⟨n, h⟩).reluApply (N.hiddenState x n) by
            funext x
            simp [FullyConnectedReLUNet.hiddenState, h]]
          unfold DenseLayer.reluApply reluVec DenseLayer.apply relu
          fun_prop
        · rw [show (fun x => N.hiddenState x (n + 1)) =
              fun x => N.hiddenState x n by
            funext x
            simp [FullyConnectedReLUNet.hiddenState, h]]
          exact ih
  unfold FullyConnectedReLUNet.realize
  fun_prop (disch := aesop)

/-- The output of a fixed finite ReLU network is uniformly bounded on the
unit cube. -/
theorem fullyConnectedReLUNet_exists_abs_realize_bound_on_unitCube
    {d : Nat} (N : FullyConnectedReLUNet d) :
    exists B : Real, 0 <= B /\ forall x : Fin d -> Real,
      (forall q : Fin d, x q ∈ Set.Icc (0 : Real) 1) ->
        |N.realize x| <= B := by
  let cube : Set (Fin d -> Real) :=
    {x | forall q, x q ∈ Set.Icc (0 : Real) 1}
  have hcube : IsCompact cube := by
    simpa [cube] using
      (isCompact_pi_infinite (s := fun _ : Fin d => Set.Icc (0 : Real) 1)
        (fun _ : Fin d => isCompact_Icc))
  obtain ⟨B0, hB0⟩ := IsCompact.exists_bound_of_continuousOn
    hcube (fullyConnectedReLUNet_continuous_realize N).continuousOn
  refine ⟨max B0 0, le_max_right B0 0, ?_⟩
  intro x hx
  have hxCube : x ∈ cube := by simpa [cube] using hx
  exact le_trans (by simpa using hB0 x hxCube) (le_max_left B0 0)

/-! ## Composable macro programs -/

/-- A complete signed-state macro program, with all finite dimensions carried
by the object.  This packages the matrices used by the paper construction so
that concrete subnetworks can be appended without repeatedly restating the
dependent matrix types. -/
structure ReLUApproxMacroProgram (d : ℕ) where
  stateSize : ℕ
  featureSize : ℕ
  stepCount : ℕ
  inputMatrix : Matrix (Fin stateSize) (Fin d) ℝ
  inputBias : Fin stateSize → ℝ
  featureMatrix : Fin stepCount → Matrix (Fin featureSize) (Fin stateSize) ℝ
  featureBias : Fin stepCount → Fin featureSize → ℝ
  updateMatrix : Fin stepCount → Matrix (Fin stateSize) (Fin featureSize) ℝ
  updateBias : Fin stepCount → Fin stateSize → ℝ

/-- Empty macro program whose persistent prefix stores the external input and
whose remaining registers start at zero.  It is the seed for serially composing
already compiled scalar subnetworks. -/
noncomputable def reluApproxInputRegisterProgram (d extra : Nat) :
    ReLUApproxMacroProgram d where
  stateSize := d + extra
  featureSize := 0
  stepCount := 0
  inputMatrix := reluApproxInputMatrixWithZeroSuffix
    (1 : Matrix (Fin d) (Fin d) Real)
  inputBias := reluApproxInputBiasWithZeroSuffix (fun _ : Fin d => 0)
  featureMatrix := fun t => Fin.elim0 t
  featureBias := fun t => Fin.elim0 t
  updateMatrix := fun t => Fin.elim0 t
  updateBias := fun t => Fin.elim0 t

/-- Terminal register state of a packaged macro program. -/
noncomputable def ReLUApproxMacroProgram.run {d : ℕ}
    (P : ReLUApproxMacroProgram d) (x : Fin d → ℝ) : Fin P.stateSize → ℝ :=
  reluApproxSignedMacroRecursion P.inputMatrix P.inputBias
    P.featureMatrix P.featureBias P.updateMatrix P.updateBias x P.stepCount

theorem reluApproxInputRegisterProgram_run (d extra : Nat)
    (x : Fin d -> Real) :
    (reluApproxInputRegisterProgram d extra).run x =
      Fin.addCases x (fun _ : Fin extra => 0) := by
  unfold ReLUApproxMacroProgram.run reluApproxInputRegisterProgram
  simp only [reluApproxSignedMacroRecursion]
  have hid : reluApproxFiniteAffineMap
      (1 : Matrix (Fin d) (Fin d) Real) (fun _ => 0) x = x := by
    funext i
    simp [reluApproxFiniteAffineMap, Matrix.one_apply]
  rw [reluApproxInputWithZeroSuffix_exact]
  rw [hid]

/-- Append a concrete scalar-output network instruction to a macro program.
The old state is persistent, while a zero work suffix of width `N.width` is
available during the appended instruction. -/
noncomputable def ReLUApproxMacroProgram.appendNetwork {d n : ℕ}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize)
    (readMatrix : Matrix (Fin n) (Fin (P.stateSize + N.width)) ℝ)
    (readBias : Fin n → ℝ) : ReLUApproxMacroProgram d where
  stateSize := P.stateSize + N.width
  featureSize := reluApproxMacroWithPersistentSuffixFeatureSize
      P.featureSize N.width +
    (reluApproxPersistentWorkFeatureSize P.stateSize N.width +
      reluApproxPersistentWorkFeatureSize P.stateSize N.width)
  stepCount := P.stepCount + (((N.depth - 1) + 1) + 1)
  inputMatrix := reluApproxInputMatrixWithZeroSuffix P.inputMatrix
  inputBias := reluApproxInputBiasWithZeroSuffix P.inputBias
  featureMatrix := reluApproxConcatFeatureSchedule
    (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix
      (p := N.width) P.featureMatrix)
    (reluApproxPersistentNetworkInstructionFeatureSchedule
      N readMatrix readBias)
  featureBias := reluApproxConcatFeatureBiasSchedule
    (reluApproxMacroScheduleWithPersistentSuffixFeatureBias
      (p := N.width) P.featureBias)
    (reluApproxPersistentNetworkInstructionFeatureBiasSchedule
      N readMatrix readBias)
  updateMatrix := reluApproxConcatUpdateSchedule
    (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix
      (p := N.width) P.updateMatrix)
    (reluApproxPersistentNetworkInstructionUpdateSchedule N dst)
  updateBias := reluApproxConcatUpdateBiasSchedule
    (reluApproxMacroScheduleWithPersistentSuffixUpdateBias
      (p := N.width) P.updateBias)
    (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst)

/-- Exact terminal-state law for `appendNetwork`. -/
theorem ReLUApproxMacroProgram.run_appendNetwork {d n : ℕ}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize)
    (readMatrix : Matrix (Fin n) (Fin (P.stateSize + N.width)) ℝ)
    (readBias : Fin n → ℝ) (x : Fin d → ℝ) :
    (P.appendNetwork N dst readMatrix readBias).run x =
      Fin.addCases
        (fun i : Fin P.stateSize ↦ if i = dst then
          N.realize (reluApproxFiniteAffineMap readMatrix readBias
            (Fin.addCases (P.run x) (fun _ : Fin N.width ↦ 0)))
        else P.run x i)
        (fun _ : Fin N.width ↦ 0) := by
  exact reluApproxSignedMacroRecursion_appendNetworkInstruction_state
    P.inputMatrix P.inputBias P.featureMatrix P.featureBias
    P.updateMatrix P.updateBias N dst readMatrix readBias x

/-- Append a concrete scalar-output network and add its value to an existing
persistent accumulator. -/
noncomputable def ReLUApproxMacroProgram.appendNetworkAdd {d n : ℕ}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize)
    (readMatrix : Matrix (Fin n) (Fin (P.stateSize + N.width)) ℝ)
    (readBias : Fin n → ℝ) : ReLUApproxMacroProgram d where
  stateSize := P.stateSize + N.width
  featureSize := reluApproxMacroWithPersistentSuffixFeatureSize
      P.featureSize N.width +
    (reluApproxPersistentWorkFeatureSize P.stateSize N.width +
      reluApproxPersistentWorkFeatureSize P.stateSize N.width)
  stepCount := P.stepCount + (((N.depth - 1) + 1) + 1)
  inputMatrix := reluApproxInputMatrixWithZeroSuffix P.inputMatrix
  inputBias := reluApproxInputBiasWithZeroSuffix P.inputBias
  featureMatrix := reluApproxConcatFeatureSchedule
    (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix
      (p := N.width) P.featureMatrix)
    (reluApproxPersistentNetworkInstructionFeatureSchedule
      N readMatrix readBias)
  featureBias := reluApproxConcatFeatureBiasSchedule
    (reluApproxMacroScheduleWithPersistentSuffixFeatureBias
      (p := N.width) P.featureBias)
    (reluApproxPersistentNetworkInstructionFeatureBiasSchedule
      N readMatrix readBias)
  updateMatrix := reluApproxConcatUpdateSchedule
    (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix
      (p := N.width) P.updateMatrix)
    (reluApproxPersistentNetworkInstructionAddUpdateSchedule N dst)
  updateBias := reluApproxConcatUpdateBiasSchedule
    (reluApproxMacroScheduleWithPersistentSuffixUpdateBias
      (p := N.width) P.updateBias)
    (reluApproxPersistentNetworkInstructionAddUpdateBiasSchedule N dst)

/-- Exact terminal-state law for `appendNetworkAdd`. -/
theorem ReLUApproxMacroProgram.run_appendNetworkAdd {d n : ℕ}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize)
    (readMatrix : Matrix (Fin n) (Fin (P.stateSize + N.width)) ℝ)
    (readBias : Fin n → ℝ) (x : Fin d → ℝ) :
    (P.appendNetworkAdd N dst readMatrix readBias).run x =
      Fin.addCases
        (fun i : Fin P.stateSize ↦ if i = dst then
          P.run x i +
            N.realize (reluApproxFiniteAffineMap readMatrix readBias
              (Fin.addCases (P.run x) (fun _ : Fin N.width ↦ 0)))
        else P.run x i)
        (fun _ : Fin N.width ↦ 0) := by
  unfold ReLUApproxMacroProgram.run ReLUApproxMacroProgram.appendNetworkAdd
  rw [reluApproxSignedMacroRecursion_concat]
  rw [reluApproxSignedMacroRecursion_withPersistentZeroSuffix
    P.inputMatrix P.inputBias P.featureMatrix P.featureBias
    P.updateMatrix P.updateBias x P.stepCount le_rfl]
  simpa using
    (reluApproxPersistentNetworkInstructionAdd_exact N dst readMatrix readBias
      (Fin.addCases (P.run x) (fun _ : Fin N.width ↦ 0)))

/-- Linear readout selecting one terminal register. -/
noncomputable def ReLUApproxMacroProgram.outputWeightAt {d : ℕ}
    (P : ReLUApproxMacroProgram d) (dst : Fin P.stateSize) :
    Fin P.stateSize → ℝ :=
  fun i ↦ if i = dst then 1 else 0

theorem ReLUApproxMacroProgram.outputWeightAt_run {d : ℕ}
    (P : ReLUApproxMacroProgram d) (dst : Fin P.stateSize)
    (x : Fin d → ℝ) :
    (∑ i : Fin P.stateSize, P.outputWeightAt dst i * P.run x i) = P.run x dst := by
  classical
  rw [Finset.sum_eq_single dst]
  · simp [ReLUApproxMacroProgram.outputWeightAt]
  · intro i _hi hne
    simp [ReLUApproxMacroProgram.outputWeightAt, hne]
  · simp

/-- Specialized append law for an affine read of persistent registers.  This
is the serial-composition interface used to combine independently compiled
paper subnetworks without exposing their hidden layers. -/
theorem ReLUApproxMacroProgram.run_appendNetwork_registerRead {d n : Nat}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize) (src : Fin n -> Fin P.stateSize)
    (x : Fin d -> Real) :
    (P.appendNetwork N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x =
      Fin.addCases
        (fun i : Fin P.stateSize => if i = dst then
          N.realize (fun j => P.run x (src j)) else P.run x i)
        (fun _ : Fin N.width => 0) := by
  rw [ReLUApproxMacroProgram.run_appendNetwork]
  rw [reluApproxRegisterReadMatrix_exact]

theorem ReLUApproxMacroProgram.run_appendNetwork_registerRead_at_dst
    {d n : Nat} (P : ReLUApproxMacroProgram d)
    (N : FullyConnectedReLUNet n) (dst : Fin P.stateSize)
    (src : Fin n -> Fin P.stateSize) (x : Fin d -> Real) :
    (P.appendNetwork N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x
        (Fin.castAdd N.width dst) =
      N.realize (fun j => P.run x (src j)) := by
  rw [P.run_appendNetwork_registerRead]
  simp

theorem ReLUApproxMacroProgram.run_appendNetwork_registerRead_of_ne
    {d n : Nat} (P : ReLUApproxMacroProgram d)
    (N : FullyConnectedReLUNet n) (dst i : Fin P.stateSize)
    (src : Fin n -> Fin P.stateSize) (x : Fin d -> Real) (hi : i ≠ dst) :
    (P.appendNetwork N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x
        (Fin.castAdd N.width i) = P.run x i := by
  rw [P.run_appendNetwork_registerRead]
  simp [hi]

/-- Register-read specialization of the accumulating append instruction. -/
theorem ReLUApproxMacroProgram.run_appendNetworkAdd_registerRead {d n : Nat}
    (P : ReLUApproxMacroProgram d) (N : FullyConnectedReLUNet n)
    (dst : Fin P.stateSize) (src : Fin n -> Fin P.stateSize)
    (x : Fin d -> Real) :
    (P.appendNetworkAdd N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x =
      Fin.addCases
        (fun i : Fin P.stateSize => if i = dst then
          P.run x i + N.realize (fun j => P.run x (src j)) else P.run x i)
        (fun _ : Fin N.width => 0) := by
  rw [ReLUApproxMacroProgram.run_appendNetworkAdd]
  rw [reluApproxRegisterReadMatrix_exact]

theorem ReLUApproxMacroProgram.run_appendNetworkAdd_registerRead_at_dst
    {d n : Nat} (P : ReLUApproxMacroProgram d)
    (N : FullyConnectedReLUNet n) (dst : Fin P.stateSize)
    (src : Fin n -> Fin P.stateSize) (x : Fin d -> Real) :
    (P.appendNetworkAdd N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x
        (Fin.castAdd N.width dst) =
      P.run x dst + N.realize (fun j => P.run x (src j)) := by
  rw [P.run_appendNetworkAdd_registerRead]
  simp

theorem ReLUApproxMacroProgram.run_appendNetworkAdd_registerRead_of_ne
    {d n : Nat} (P : ReLUApproxMacroProgram d)
    (N : FullyConnectedReLUNet n) (dst i : Fin P.stateSize)
    (src : Fin n -> Fin P.stateSize) (x : Fin d -> Real) (hi : i ≠ dst) :
    (P.appendNetworkAdd N dst
      (reluApproxRegisterReadMatrix N.width src) (fun _ => 0)).run x
        (Fin.castAdd N.width i) = P.run x i := by
  rw [P.run_appendNetworkAdd_registerRead]
  simp [hi]

/-- Compile one terminal register of a macro program into an exact-depth fully
connected ReLU network. -/
theorem exists_fullyConnectedReLUNet_of_macroProgram_register {d D W : Nat}
    (P : ReLUApproxMacroProgram d) (dst : Fin P.stateSize)
    (hdepth : 2 * P.stepCount + 1 <= D)
    (hwidth : (P.stateSize + P.stateSize) + P.featureSize <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
      N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
      forall x, N.realize x = P.run x dst := by
  obtain ⟨N, hD, hW, hP, hrealize⟩ :=
    exists_reluApproxSignedMacroRecursionNet_exactDepth
      P.inputMatrix P.inputBias P.featureMatrix P.featureBias
      P.updateMatrix P.updateBias (P.outputWeightAt dst) 0 hdepth hwidth
  refine ⟨N, hD, hW, hP, ?_⟩
  intro x
  rw [hrealize x, add_zero]
  exact P.outputWeightAt_run dst x

end Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra
