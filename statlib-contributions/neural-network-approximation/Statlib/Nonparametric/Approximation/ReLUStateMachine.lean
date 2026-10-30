import Statlib.Nonparametric.Approximation.ReLUNetworkConstruction

open scoped BigOperators
open Statlib.Nonparametric.Vocabulary

/-! # ReLU State-Machine Approximation

Reusable state-machine constructions for Taylor coefficients, grid scans,
boundary clipping, and fixed-width ReLU evaluation.
-/

namespace Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra

set_option maxHeartbeats 1000000

noncomputable def fixedDirectionalDerivative {d : Nat} :
    (k : Nat) -> ((Fin d -> Real) -> Real) ->
      (Fin k -> Fin d -> Real) -> (Fin d -> Real) -> Real
  | 0, f, _ => f
  | k + 1, f, v =>
      fun x => fderiv Real (fixedDirectionalDerivative k f (Fin.tail v)) x (v 0)

theorem fixedDirectionalDerivative_eq_iteratedFDeriv
    {d k : Nat} (f : (Fin d -> Real) -> Real)
    (hf : ContDiff Real k f)
    (v : Fin k -> Fin d -> Real) (x : Fin d -> Real) :
    fixedDirectionalDerivative k f v x = iteratedFDeriv Real k f x v := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [fixedDirectionalDerivative]
      rw [iteratedFDeriv_succ_apply_left]
      have hfun : fixedDirectionalDerivative k f (Fin.tail v) =
          fun y => iteratedFDeriv Real k f y (Fin.tail v) := by
        funext y
        exact ih (hf.of_le (by norm_num)) (Fin.tail v) y
      rw [hfun]
      change
        (fderiv Real (fun y => iteratedFDeriv Real k f y (Fin.tail v)) x) (v 0) = _
      exact fderiv_continuousMultilinear_apply_const_apply
        ((hf.differentiable_iteratedFDeriv (m := k) (by norm_cast; omega)) x)
        (Fin.tail v) (v 0)

def fixedDirectionAppend {d k : Nat} :
    {j : Nat} -> (Fin j -> Fin d -> Real) ->
      (Fin k -> Fin d -> Real) -> Fin (k + j) -> Fin d -> Real
  | 0, _, v => v
  | _j + 1, w, v => Fin.cons (w 0) (fixedDirectionAppend (Fin.tail w) v)

theorem fixedDirectionalDerivative_comp
    {d j k : Nat} (f : (Fin d -> Real) -> Real)
    (v : Fin k -> Fin d -> Real) (w : Fin j -> Fin d -> Real)
    (x : Fin d -> Real) :
    fixedDirectionalDerivative j (fixedDirectionalDerivative k f v) w x =
      fixedDirectionalDerivative (k + j) f (fixedDirectionAppend w v) x := by
  induction j generalizing x with
  | zero =>
      simp [fixedDirectionalDerivative, fixedDirectionAppend]
  | succ j ih =>
      rw [fixedDirectionalDerivative]
      have hfun :
          fixedDirectionalDerivative j (fixedDirectionalDerivative k f v) (Fin.tail w) =
            fixedDirectionalDerivative (k + j) f (fixedDirectionAppend (Fin.tail w) v) := by
        funext y
        exact ih (Fin.tail w) y
      rw [hfun]
      change
        (fderiv Real
          (fixedDirectionalDerivative (k + j) f
            (fixedDirectionAppend (Fin.tail w) v)) x) (w 0) = _
      simp only [fixedDirectionalDerivative, fixedDirectionAppend]
      rw [Fin.tail_cons, Fin.cons_zero]
      rfl

theorem fixedDirectionalDerivative_contDiff
    {d k n : Nat} (f : (Fin d -> Real) -> Real)
    (hf : ContDiff Real (k + n : Nat) f)
    (v : Fin k -> Fin d -> Real) :
    ContDiff Real n (fixedDirectionalDerivative k f v) := by
  induction k generalizing n with
  | zero =>
      simpa [fixedDirectionalDerivative] using hf
  | succ k ih =>
      rw [fixedDirectionalDerivative]
      have hle : ((k + (n + 1) : Nat) : WithTop ℕ∞) ≤
          ((k + 1 + n : Nat) : WithTop ℕ∞) := by
        exact_mod_cast (show k + (n + 1) ≤ k + 1 + n by omega)
      have hprev : ContDiff Real (n + 1 : Nat)
          (fixedDirectionalDerivative k f (Fin.tail v)) :=
        ih (hf.of_le hle) (Fin.tail v)
      exact (hprev.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_num)).clm_apply
        contDiff_const

theorem fixedDirectionalDerivative_iteratedFDeriv
    {d j k : Nat} (f : (Fin d -> Real) -> Real)
    (hf : ContDiff Real (k + j : Nat) f)
    (v : Fin k -> Fin d -> Real) (w : Fin j -> Fin d -> Real)
    (x : Fin d -> Real) :
    (iteratedFDeriv Real j (fixedDirectionalDerivative k f v) x) w =
      (iteratedFDeriv Real (k + j) f x) (fixedDirectionAppend w v) := by
  rw [<- fixedDirectionalDerivative_eq_iteratedFDeriv
    (fixedDirectionalDerivative k f v)
    (fixedDirectionalDerivative_contDiff f hf v) w x]
  rw [fixedDirectionalDerivative_comp]
  exact fixedDirectionalDerivative_eq_iteratedFDeriv f
    (hf.of_le (by norm_num)) (fixedDirectionAppend w v) x

theorem fixedDirectionAppend_left
    {d j k : Nat} (w : Fin j -> Fin d -> Real)
    (v : Fin k -> Fin d -> Real) (i : Fin j) :
    fixedDirectionAppend w v
        (Fin.cast (Nat.add_comm j k) (Fin.castAdd k i)) = w i := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simpa [fixedDirectionAppend] using ih (Fin.tail w) i

theorem fixedDirectionAppend_right
    {d j k : Nat} (w : Fin j -> Fin d -> Real)
    (v : Fin k -> Fin d -> Real) (i : Fin k) :
    fixedDirectionAppend w v
        (Fin.cast (Nat.add_comm j k) (Fin.natAdd j i)) = v i := by
  induction j with
  | zero => simp [fixedDirectionAppend]
  | succ j ih =>
      simpa [fixedDirectionAppend] using ih (Fin.tail w)

theorem fixedDirectionAppend_prod_norm
    {d j k : Nat} (w : Fin j -> Fin d -> Real)
    (v : Fin k -> Fin d -> Real) :
    (∏ i : Fin (k + j), ‖fixedDirectionAppend w v i‖) =
      (∏ i : Fin j, ‖w i‖) * ∏ i : Fin k, ‖v i‖ := by
  let e : Fin (j + k) ≃ Fin (k + j) := finCongr (Nat.add_comm j k)
  rw [← Fintype.prod_equiv e
    (fun i : Fin (j + k) => ‖fixedDirectionAppend w v (e i)‖)
    (fun i : Fin (k + j) => ‖fixedDirectionAppend w v i‖)]
  · rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simpa [e] using congrArg norm (fixedDirectionAppend_left w v i)
    · apply Finset.prod_congr rfl
      intro i hi
      simpa [e] using congrArg norm (fixedDirectionAppend_right w v i)
  · intro i
    rfl

theorem norm_iteratedFDeriv_fixedDirectionalDerivative_sub_le
    {d j k : Nat} (f : (Fin d -> Real) -> Real)
    (hf : ContDiff Real (k + j : Nat) f)
    (v : Fin k -> Fin d -> Real) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x y : Fin d -> Real) :
    ‖iteratedFDeriv Real j (fixedDirectionalDerivative k f v) x -
        iteratedFDeriv Real j (fixedDirectionalDerivative k f v) y‖ ≤
      ‖iteratedFDeriv Real (k + j) f x -
        iteratedFDeriv Real (k + j) f y‖ := by
  let A := iteratedFDeriv Real (k + j) f x - iteratedFDeriv Real (k + j) f y
  have hvprod : (∏ i : Fin k, ‖v i‖) ≤ 1 := by
    calc
      (∏ i : Fin k, ‖v i‖) ≤ ∏ _i : Fin k, (1 : Real) := by
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hv i)
      _ = 1 := by simp
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro w
  rw [ContinuousMultilinearMap.sub_apply]
  rw [fixedDirectionalDerivative_iteratedFDeriv f hf v w x]
  rw [fixedDirectionalDerivative_iteratedFDeriv f hf v w y]
  rw [← ContinuousMultilinearMap.sub_apply]
  calc
    ‖A (fixedDirectionAppend w v)‖ ≤
        ‖A‖ * ∏ i : Fin (k + j), ‖fixedDirectionAppend w v i‖ :=
      A.le_opNorm (fixedDirectionAppend w v)
    _ = ‖A‖ * ((∏ i : Fin j, ‖w i‖) * ∏ i : Fin k, ‖v i‖) := by
      rw [fixedDirectionAppend_prod_norm]
    _ ≤ ‖A‖ * ((∏ i : Fin j, ‖w i‖) * 1) := by
      gcongr
    _ = ‖A‖ * ∏ i : Fin j, ‖w i‖ := by ring

theorem fixedDirectionalDerivative_isHolderSmooth
    {d j k : Nat} {beta C : Real}
    (f : (Fin d -> Real) -> Real)
    (hf : IsHolderSmoothFunction (k + j) beta C f)
    (v : Fin k -> Fin d -> Real) (hv : ∀ i, ‖v i‖ ≤ 1) :
    IsHolderSmoothFunction j beta C (fixedDirectionalDerivative k f v) := by
  cases j with
  | zero =>
      cases k with
      | zero => simpa [fixedDirectionalDerivative] using hf
      | succ k =>
          have hf' : ContDiff Real (k + 1 : Nat) f ∧
              ∀ x y : Fin d -> Real,
                ‖iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y‖ ≤
                  C * Real.rpow (dist x y) beta := by
            simpa [isHolderSmoothFunction_succ] using hf
          change IsHolderFunction (fixedDirectionalDerivative (k + 1) f v) beta C
          intro x y
          rw [fixedDirectionalDerivative_eq_iteratedFDeriv f hf'.1 v x]
          rw [fixedDirectionalDerivative_eq_iteratedFDeriv f hf'.1 v y]
          have hvprod : (∏ i : Fin (k + 1), ‖v i‖) ≤ 1 := by
            calc
              (∏ i : Fin (k + 1), ‖v i‖) ≤ ∏ _i : Fin (k + 1), (1 : Real) := by
                exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hv i)
              _ = 1 := by simp
          have heval :
              |(iteratedFDeriv Real (k + 1) f x -
                  iteratedFDeriv Real (k + 1) f y) v| ≤
                ‖iteratedFDeriv Real (k + 1) f x -
                  iteratedFDeriv Real (k + 1) f y‖ := by
            calc
              |(iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y) v| =
                  ‖(iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y) v‖ := by
                      rw [Real.norm_eq_abs]
              _ ≤ ‖iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y‖ *
                    ∏ i : Fin (k + 1), ‖v i‖ :=
                ContinuousMultilinearMap.le_opNorm _ v
              _ ≤ ‖iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y‖ * 1 := by
                gcongr
              _ = ‖iteratedFDeriv Real (k + 1) f x -
                    iteratedFDeriv Real (k + 1) f y‖ := by ring
          rw [← ContinuousMultilinearMap.sub_apply]
          exact heval.trans (hf'.2 x y)
  | succ j =>
      have hf' : ContDiff Real (k + (j + 1) : Nat) f ∧
          ∀ x y : Fin d -> Real,
            ‖iteratedFDeriv Real (k + (j + 1)) f x -
                iteratedFDeriv Real (k + (j + 1)) f y‖ ≤
              C * Real.rpow (dist x y) beta := by
        simpa [isHolderSmoothFunction_succ, Nat.add_assoc] using hf
      rw [isHolderSmoothFunction_succ]
      refine ⟨fixedDirectionalDerivative_contDiff f hf'.1 v, ?_⟩
      intro x y
      exact (norm_iteratedFDeriv_fixedDirectionalDerivative_sub_le
        f hf'.1 v hv x y).trans (hf'.2 x y)

theorem fixedDirectionalDerivative_taylor_remainder_bound_on_box
    {d j k : Nat} {beta C rho : Real}
    (hbeta_nonneg : 0 ≤ beta) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (f : (Fin d -> Real) -> Real)
    (hf : IsHolderSmoothFunction (k + j) beta C f)
    (v : Fin k -> Fin d -> Real) (hv : ∀ i, ‖v i‖ ≤ 1)
    (center x : Fin d -> Real) (hbox : ‖x - center‖ ≤ rho) :
    |fixedDirectionalDerivative k f v x -
        ∑ n ∈ Finset.range (j + 1),
          ((Nat.factorial n : Real)⁻¹) *
            (iteratedFDeriv Real n (fixedDirectionalDerivative k f v) center)
              (fun _ : Fin n => x - center)| ≤
      C / (Nat.factorial j : Real) * Real.rpow rho ((j : Real) + beta) := by
  exact isHolderSmoothFunction_taylor_remainder_bound_on_box
    hbeta_nonneg hC hrho (fixedDirectionalDerivative k f v)
    (fixedDirectionalDerivative_isHolderSmooth f hf v hv) center x hbox

/-- Coordinate directions attached to an ordered Taylor multiindex. -/
noncomputable def reluApproxTaylorDirections {r d : Nat}
    (a : TaylorMultiindex r d) : Fin a.1.val -> Fin d -> Real :=
  fun q => Pi.single (a.2 q) 1

@[simp] theorem norm_reluApproxTaylorDirections {r d : Nat}
    (a : TaylorMultiindex r d) (q : Fin a.1.val) :
    ‖reluApproxTaylorDirections a q‖ = 1 := by
  simp [reluApproxTaylorDirections, Pi.norm_single]

/-- Taylor coefficient in the ordered-direction convention used by the paper. -/
private noncomputable def reluApproxNormalizedTaylorCoefficient {r d : Nat}
    (f : (Fin d -> Real) -> Real) (a : TaylorMultiindex r d)
    (x : Fin d -> Real) : Real :=
  (Nat.factorial a.1.val : Real)⁻¹ *
    (iteratedFDeriv Real a.1.val f x) (reluApproxTaylorDirections a)

/-- Taylor prediction of a fixed directional derivative after a center move. -/
private noncomputable def reluApproxDirectionalTaylorPredictor {d j k : Nat}
    (f : (Fin d -> Real) -> Real) (v : Fin k -> Fin d -> Real)
    (center next : Fin d -> Real) : Real :=
  (Nat.factorial k : Real)⁻¹ *
    ∑ n ∈ Finset.range (j + 1),
      (Nat.factorial n : Real)⁻¹ *
        (iteratedFDeriv Real n (fixedDirectionalDerivative k f v) center)
          (fun _ : Fin n => next - center)

/-- Unnormalized Taylor prediction for a directional-derivative register. -/
private noncomputable def reluApproxDirectionalTaylorPredictorRaw {d j k : Nat}
    (f : (Fin d -> Real) -> Real) (v : Fin k -> Fin d -> Real)
    (center next : Fin d -> Real) : Real :=
  ∑ n ∈ Finset.range (j + 1),
    (Nat.factorial n : Real)⁻¹ *
      (iteratedFDeriv Real n (fixedDirectionalDerivative k f v) center)
        (fun _ : Fin n => next - center)

private theorem reluApprox_directional_taylor_remainder_bound_raw
    {d j k : Nat} {beta C rho : Real}
    (hbeta_nonneg : 0 ≤ beta) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (f : (Fin d -> Real) -> Real)
    (hf : IsHolderSmoothFunction (k + j) beta C f)
    (v : Fin k -> Fin d -> Real) (hv : ∀ i, ‖v i‖ ≤ 1)
    (center next : Fin d -> Real) (hbox : ‖next - center‖ ≤ rho) :
    |fixedDirectionalDerivative k f v next -
        reluApproxDirectionalTaylorPredictorRaw (j := j) f v center next| ≤
      C / (Nat.factorial j : Real) * Real.rpow rho ((j : Real) + beta) := by
  simpa [reluApproxDirectionalTaylorPredictorRaw] using
    fixedDirectionalDerivative_taylor_remainder_bound_on_box
      hbeta_nonneg hC hrho f hf v hv center next hbox

private theorem reluApprox_normalized_directional_taylor_remainder_bound
    {d j k : Nat} {beta C rho : Real}
    (hbeta_nonneg : 0 ≤ beta) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (f : (Fin d -> Real) -> Real)
    (hf : IsHolderSmoothFunction (k + j) beta C f)
    (v : Fin k -> Fin d -> Real) (hv : ∀ i, ‖v i‖ ≤ 1)
    (center next : Fin d -> Real) (hbox : ‖next - center‖ ≤ rho) :
    |(Nat.factorial k : Real)⁻¹ * fixedDirectionalDerivative k f v next -
        reluApproxDirectionalTaylorPredictor (j := j) f v center next| ≤
      (Nat.factorial k : Real)⁻¹ *
        (C / (Nat.factorial j : Real) * Real.rpow rho ((j : Real) + beta)) := by
  have hfac_nonneg : 0 ≤ (Nat.factorial k : Real)⁻¹ := by positivity
  have hrem := fixedDirectionalDerivative_taylor_remainder_bound_on_box
    hbeta_nonneg hC hrho f hf v hv center next hbox
  rw [reluApproxDirectionalTaylorPredictor]
  rw [← mul_sub, abs_mul, abs_of_nonneg hfac_nonneg]
  exact mul_le_mul_of_nonneg_left hrem hfac_nonneg

/-- Extend an ordered Taylor multiindex by `n` repetitions of one coordinate. -/
private def reluApproxTaylorExtension {r d : Nat} (a : TaylorMultiindex r d)
    (n : Fin (r - a.1.val + 1)) (q : Fin d) : TaylorMultiindex r d :=
  ⟨⟨a.1.val + n.val, by omega⟩,
    fun i => Fin.addCases (fun _ : Fin n.val => q) a.2
      (Fin.cast (Nat.add_comm a.1.val n.val) i)⟩

@[simp] theorem reluApproxTaylorExtension_degree {r d : Nat}
    (a : TaylorMultiindex r d) (n : Fin (r - a.1.val + 1)) (q : Fin d) :
    (reluApproxTaylorExtension a n q).1.val = a.1.val + n.val := rfl

private theorem reluApproxTaylorExtension_left {r d : Nat}
    (a : TaylorMultiindex r d) (n : Fin (r - a.1.val + 1)) (q : Fin d)
    (u : Fin n.val) :
    (reluApproxTaylorExtension a n q).2
        (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.castAdd a.1.val u)) = q := by
  change Fin.addCases (fun _ : Fin n.val => q) a.2
      (Fin.cast (Nat.add_comm a.1.val n.val)
        (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.castAdd a.1.val u))) = q
  have hi :
      Fin.cast (Nat.add_comm a.1.val n.val)
          (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.castAdd a.1.val u)) =
        Fin.castAdd a.1.val u := by
    apply Fin.ext
    rfl
  rw [hi, Fin.addCases_left]

private theorem reluApproxTaylorExtension_right {r d : Nat}
    (a : TaylorMultiindex r d) (n : Fin (r - a.1.val + 1)) (q : Fin d)
    (u : Fin a.1.val) :
    (reluApproxTaylorExtension a n q).2
        (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.natAdd n.val u)) = a.2 u := by
  change Fin.addCases (fun _ : Fin n.val => q) a.2
      (Fin.cast (Nat.add_comm a.1.val n.val)
        (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.natAdd n.val u))) = a.2 u
  have hi :
      Fin.cast (Nat.add_comm a.1.val n.val)
          (Fin.cast (Nat.add_comm n.val a.1.val) (Fin.natAdd n.val u)) =
        Fin.natAdd n.val u := by
    apply Fin.ext
    rfl
  rw [hi, Fin.addCases_right]

private theorem reluApproxTaylorDirections_extension {r d : Nat}
    (a : TaylorMultiindex r d) (n : Fin (r - a.1.val + 1)) (q : Fin d) :
    reluApproxTaylorDirections (reluApproxTaylorExtension a n q) =
      fixedDirectionAppend (fun _ : Fin n.val => Pi.single q 1)
        (reluApproxTaylorDirections a) := by
  funext i
  let j : Fin (n.val + a.1.val) :=
    Fin.cast (Nat.add_comm a.1.val n.val) i
  have hij : i = Fin.cast (Nat.add_comm n.val a.1.val) j := by
    apply Fin.ext
    rfl
  rw [hij]
  refine Fin.addCases ?_ ?_ j
  · intro u
    rw [fixedDirectionAppend_left]
    simp only [reluApproxTaylorDirections]
    rw [reluApproxTaylorExtension_left]
  · intro u
    rw [fixedDirectionAppend_right]
    simp only [reluApproxTaylorDirections]
    rw [reluApproxTaylorExtension_right]

/-- Sparse Taylor transport matrix for a signed one-coordinate grid move. -/
private noncomputable def reluApproxTaylorTransport {r d : Nat}
    (step : Real) (q : Fin d) (a b : TaylorMultiindex r d) : Real :=
  ∑ n : Fin (r - a.1.val + 1),
    if b = reluApproxTaylorExtension a n q then
      step ^ n.val * (Nat.factorial n.val : Real)⁻¹
    else 0

private theorem reluApproxTaylorTransport_sum {r d : Nat}
    (step : Real) (q : Fin d) (a : TaylorMultiindex r d)
    (theta : TaylorMultiindex r d -> Real) :
    (∑ b : TaylorMultiindex r d,
        reluApproxTaylorTransport step q a b * theta b) =
      ∑ n : Fin (r - a.1.val + 1),
        (step ^ n.val * (Nat.factorial n.val : Real)⁻¹) *
          theta (reluApproxTaylorExtension a n q) := by
  classical
  simp only [reluApproxTaylorTransport, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  simp

/-- Coordinate step used by a signed serpentine transition. -/
noncomputable def reluApproxCoordinateStep {d : Nat}
    (q : Fin d) (step : Real) : Fin d -> Real :=
  Pi.single q step

private theorem reluApproxCoordinateStep_eq_smul {d : Nat}
    (q : Fin d) (step : Real) :
    reluApproxCoordinateStep q step =
      step • (Pi.single q (1 : Real) : Fin d -> Real) := by
  funext u
  by_cases hu : u = q
  · subst u
    simp [reluApproxCoordinateStep]
  · simp [reluApproxCoordinateStep, Pi.single_apply, hu]

@[simp] theorem norm_reluApproxCoordinateStep {d : Nat}
    (q : Fin d) (step : Real) :
    ‖reluApproxCoordinateStep q step‖ = |step| := by
  simp [reluApproxCoordinateStep, Pi.norm_single, Real.norm_eq_abs]

theorem iteratedFDeriv_coordinateStep {d n : Nat}
    (g : (Fin d -> Real) -> Real) (center : Fin d -> Real)
    (q : Fin d) (step : Real) :
    (iteratedFDeriv Real n g center)
        (fun _ : Fin n => reluApproxCoordinateStep q step) =
      step ^ n *
        (iteratedFDeriv Real n g center)
          (fun _ : Fin n => (Pi.single q 1 : Fin d -> Real)) := by
  have hvec :
    (fun _ : Fin n => reluApproxCoordinateStep q step) =
        fun _i : Fin n => step • (Pi.single q (1 : Real) : Fin d -> Real) := by
    funext i
    exact reluApproxCoordinateStep_eq_smul q step
  rw [hvec, ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- Raw derivative register indexed by an ordered Taylor multiindex. -/
noncomputable def reluApproxRawTaylorCoefficient {r d : Nat}
    (f : (Fin d -> Real) -> Real) (a : TaylorMultiindex r d)
    (x : Fin d -> Real) : Real :=
  (iteratedFDeriv Real a.1.val f x) (reluApproxTaylorDirections a)

private theorem reluApprox_rawTaylorPredictor_eq_transport {r d : Nat}
    (f : (Fin d -> Real) -> Real) (hf : ContDiff Real r f)
    (a : TaylorMultiindex r d) (q : Fin d) (step : Real)
    (center next : Fin d -> Real)
    (hmove : next - center = reluApproxCoordinateStep q step) :
    reluApproxDirectionalTaylorPredictorRaw (j := r - a.1.val)
        f (reluApproxTaylorDirections a) center next =
      ∑ b : TaylorMultiindex r d,
        reluApproxTaylorTransport step q a b *
          reluApproxRawTaylorCoefficient f b center := by
  have hdeg : a.1.val ≤ r := Nat.le_of_lt_succ a.1.isLt
  rw [reluApproxTaylorTransport_sum]
  let term : Nat -> Real := fun n =>
    (Nat.factorial n : Real)⁻¹ *
      (iteratedFDeriv Real n
        (fixedDirectionalDerivative a.1.val f (reluApproxTaylorDirections a)) center)
        (fun _ : Fin n => next - center)
  change (∑ n ∈ Finset.range (r - a.1.val + 1), term n) = _
  rw [← Fin.sum_univ_eq_sum_range term]
  apply Finset.sum_congr rfl
  intro n _hn
  have hnle : n.val ≤ r - a.1.val := by omega
  have hsumle : a.1.val + n.val ≤ r := by omega
  have hfkn : ContDiff Real (a.1.val + n.val : Nat) f :=
    hf.of_le (by exact_mod_cast hsumle)
  have hunit :
      (iteratedFDeriv Real n.val
          (fixedDirectionalDerivative a.1.val f (reluApproxTaylorDirections a)) center)
          (fun _ : Fin n.val => (Pi.single q 1 : Fin d -> Real)) =
        reluApproxRawTaylorCoefficient f
          (reluApproxTaylorExtension a n q) center := by
    rw [fixedDirectionalDerivative_iteratedFDeriv f hfkn]
    rw [← reluApproxTaylorDirections_extension]
    rfl
  have hstep := iteratedFDeriv_coordinateStep (n := n.val)
      (fixedDirectionalDerivative a.1.val f (reluApproxTaylorDirections a))
      center q step
  dsimp [term]
  rw [hmove, hstep, hunit]
  ring

private theorem reluApprox_rawTaylorTransport_residual_bound {r d : Nat}
    {beta C rho : Real} (hbeta_nonneg : 0 ≤ beta) (hC : 0 ≤ C)
    (hrho : 0 ≤ rho) (f : (Fin d -> Real) -> Real)
    (hf : IsHolderSmoothFunction r beta C f) (hfcont : ContDiff Real r f)
    (a : TaylorMultiindex r d) (q : Fin d) (step : Real)
    (center next : Fin d -> Real)
    (hmove : next - center = reluApproxCoordinateStep q step)
    (hstep : |step| ≤ rho) :
    |reluApproxRawTaylorCoefficient f a next -
        ∑ b : TaylorMultiindex r d,
          reluApproxTaylorTransport step q a b *
            reluApproxRawTaylorCoefficient f b center| ≤
      C / (Nat.factorial (r - a.1.val) : Real) *
        Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) := by
  have hdeg : a.1.val ≤ r := Nat.le_of_lt_succ a.1.isLt
  have hfdeg : ContDiff Real a.1.val f :=
    hfcont.of_le (by exact_mod_cast hdeg)
  have hsmooth : IsHolderSmoothFunction
      (a.1.val + (r - a.1.val)) beta C f := by
    simpa [Nat.add_sub_of_le hdeg] using hf
  have hbox : ‖next - center‖ ≤ rho := by
    rw [hmove, norm_reluApproxCoordinateStep]
    exact hstep
  have hrem := reluApprox_directional_taylor_remainder_bound_raw
    hbeta_nonneg hC hrho f hsmooth (reluApproxTaylorDirections a)
    (fun i => by simp) center next hbox
  rw [reluApprox_rawTaylorPredictor_eq_transport f hfcont a q step center next hmove]
    at hrem
  rw [fixedDirectionalDerivative_eq_iteratedFDeriv f hfdeg]
    at hrem
  exact hrem

/-- Degree-dependent correction scale for one Taylor register. -/
noncomputable def reluApproxTaylorResidualScale {r d : Nat}
    (beta C rho : Real) (a : TaylorMultiindex r d) : Real :=
  (C + 1) * Real.rpow rho (((r - a.1.val : Nat) : Real) + beta)

theorem reluApproxTaylorResidualScale_pos {r d : Nat}
    {beta C rho : Real} (hbeta_pos : 0 < beta) (hC : 0 ≤ C)
    (hrho : 0 < rho) (a : TaylorMultiindex r d) :
    0 < reluApproxTaylorResidualScale beta C rho a := by
  unfold reluApproxTaylorResidualScale
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos hrho _)

/-- A Taylor transport term preserves the degree-dependent residual scale:
the coordinate step contributes exactly the power lost when the derivative
degree is increased. -/
private theorem reluApproxTaylorResidualScale_transport_term {r d : Nat}
    {beta C rho step : Real} (hC : 0 <= C) (hrho : 0 < rho)
    (hstep : |step| <= rho) (q : Fin d) (a : TaylorMultiindex r d)
    (n : Fin (r - a.1.val + 1)) :
    |step| ^ n.val *
        reluApproxTaylorResidualScale beta C rho
          (reluApproxTaylorExtension a n q) <=
      reluApproxTaylorResidualScale beta C rho a := by
  unfold reluApproxTaylorResidualScale
  have hn : n.val <= r - a.1.val := by omega
  have hpow : |step| ^ n.val <= rho ^ n.val :=
    pow_le_pow_left₀ (abs_nonneg step) hstep n.val
  have hC1 : 0 <= C + 1 := by linarith
  have hscale_nonneg :
      0 <= (C + 1) *
        rho ^ (((r - (a.1.val + n.val) : Nat) : Real) + beta) :=
    mul_nonneg hC1 (Real.rpow_nonneg hrho.le _)
  calc
    |step| ^ n.val *
          ((C + 1) * rho ^
            (((r - (reluApproxTaylorExtension a n q).1.val : Nat) : Real) + beta))
        <= rho ^ n.val *
          ((C + 1) * rho ^
            (((r - (reluApproxTaylorExtension a n q).1.val : Nat) : Real) + beta)) := by
              exact mul_le_mul_of_nonneg_right hpow hscale_nonneg
    _ = (C + 1) * (rho ^ n.val *
          rho ^ (((r - (a.1.val + n.val) : Nat) : Real) + beta)) := by
          rw [reluApproxTaylorExtension_degree]
          ring
    _ = (C + 1) * rho ^ (((r - a.1.val : Nat) : Real) + beta) := by
          rw [← Real.rpow_natCast rho n.val]
          rw [← Real.rpow_add hrho]
          congr 2
          have hnat : n.val + (r - (a.1.val + n.val)) = r - a.1.val := by
            omega
          have hcast : (n.val : Real) + (r - (a.1.val + n.val) : Nat) =
              (r - a.1.val : Nat) := by
            exact_mod_cast hnat
          linarith

/-- Taylor transport is stable for the degree-dependent correction profile.
The exponential factor is independent of the resolution and of the function;
it is the finite Taylor-series envelope for one coordinate move. -/
private theorem reluApproxTaylorTransport_error_le_exp {r d : Nat}
    {beta C rho step : Real} (hbeta : 0 < beta) (hC : 0 <= C)
    (hrho : 0 < rho) (hstep : |step| <= rho)
    (q : Fin d) (a : TaylorMultiindex r d)
    (theta thetaHat : TaylorMultiindex r d -> Real)
    (herr : forall b, |thetaHat b - theta b| <=
      reluApproxTaylorResidualScale beta C rho b) :
    |(Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * thetaHat b)) -
      (Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * theta b))| <=
      Real.exp 1 * reluApproxTaylorResidualScale beta C rho a := by
  have hrewrite :
      (Finset.univ.sum (fun b =>
          reluApproxTaylorTransport step q a b * thetaHat b)) -
        (Finset.univ.sum (fun b =>
          reluApproxTaylorTransport step q a b * theta b)) =
      Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
        (step ^ n.val * (Nat.factorial n.val : Real)⁻¹) *
          (thetaHat (reluApproxTaylorExtension a n q) -
            theta (reluApproxTaylorExtension a n q))) := by
    rw [reluApproxTaylorTransport_sum, reluApproxTaylorTransport_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hrewrite]
  calc
    |Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
        (step ^ n.val * (Nat.factorial n.val : Real)⁻¹) *
          (thetaHat (reluApproxTaylorExtension a n q) -
            theta (reluApproxTaylorExtension a n q)))| <=
      Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
        |(step ^ n.val * (Nat.factorial n.val : Real)⁻¹) *
          (thetaHat (reluApproxTaylorExtension a n q) -
            theta (reluApproxTaylorExtension a n q))|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
          (Nat.factorial n.val : Real)⁻¹ *
            reluApproxTaylorResidualScale beta C rho a) := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity :
        0 <= (Nat.factorial n.val : Real)⁻¹)]
      calc
        |step| ^ n.val * (Nat.factorial n.val : Real)⁻¹ *
              |thetaHat (reluApproxTaylorExtension a n q) -
                theta (reluApproxTaylorExtension a n q)|
            <= |step| ^ n.val * (Nat.factorial n.val : Real)⁻¹ *
              reluApproxTaylorResidualScale beta C rho
                (reluApproxTaylorExtension a n q) := by
                  exact mul_le_mul_of_nonneg_left (herr _) (by positivity)
        _ = (Nat.factorial n.val : Real)⁻¹ *
              (|step| ^ n.val *
                reluApproxTaylorResidualScale beta C rho
                  (reluApproxTaylorExtension a n q)) := by ring
        _ <= (Nat.factorial n.val : Real)⁻¹ *
              reluApproxTaylorResidualScale beta C rho a := by
                exact mul_le_mul_of_nonneg_left
                  (reluApproxTaylorResidualScale_transport_term
                    hC hrho hstep q a n) (by positivity)
    _ = (Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
          (Nat.factorial n.val : Real)⁻¹)) *
            reluApproxTaylorResidualScale beta C rho a := by
      rw [Finset.sum_mul]
    _ <= Real.exp 1 * reluApproxTaylorResidualScale beta C rho a := by
      have hsum : Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
          (Nat.factorial n.val : Real)⁻¹) <= Real.exp 1 := by
        calc
          Finset.univ.sum (fun n : Fin (r - a.1.val + 1) =>
              (Nat.factorial n.val : Real)⁻¹) =
              Finset.sum (Finset.range (r - a.1.val + 1)) (fun n =>
                (Nat.factorial n : Real)⁻¹) := by
                  exact Fin.sum_univ_eq_sum_range
                    (fun n => (Nat.factorial n : Real)⁻¹) _
          _ <= Real.exp 1 := by
            simpa [one_pow, div_eq_mul_inv] using
              Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) <= 1)
                (r - a.1.val + 1)
      exact mul_le_mul_of_nonneg_right hsum
        (le_of_lt (reluApproxTaylorResidualScale_pos
          hbeta hC hrho a))

/-- The residual formed from the current approximate registers remains in the
bounded correction alphabet.  It is the sum of the genuine Taylor remainder
and the stable transport error. -/
private theorem reluApprox_approximateTaylorTransport_residual_bound {r d : Nat}
    {beta C rho step nextValue : Real}
    (hd : 0 < d) (hbeta : 0 < beta) (hC : 0 <= C)
    (hrho : 0 < rho) (hstep : |step| <= rho)
    (q : Fin d) (a : TaylorMultiindex r d)
    (theta thetaHat : TaylorMultiindex r d -> Real)
    (herr : forall b, |thetaHat b - theta b| <=
      reluApproxTaylorResidualScale beta C rho b)
    (htrue : |nextValue - Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * theta b)| <=
      C / (Nat.factorial (r - a.1.val) : Real) *
        Real.rpow rho (((r - a.1.val : Nat) : Real) + beta)) :
    |nextValue - Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * thetaHat b)| <=
      (Real.exp (d : Real) + 1) *
        reluApproxTaylorResidualScale beta C rho a := by
  let pred := Finset.univ.sum (fun b =>
    reluApproxTaylorTransport step q a b * theta b)
  let predHat := Finset.univ.sum (fun b =>
    reluApproxTaylorTransport step q a b * thetaHat b)
  have hscale_pos := reluApproxTaylorResidualScale_pos hbeta hC hrho a
  have hfac : (1 : Real) <= Nat.factorial (r - a.1.val) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hcoeff : C / (Nat.factorial (r - a.1.val) : Real) <= C + 1 := by
    have hdiv : C / (Nat.factorial (r - a.1.val) : Real) <= C :=
      div_le_self hC hfac
    linarith
  have hrpow0 : 0 <= Real.rpow rho
      (((r - a.1.val : Nat) : Real) + beta) :=
    Real.rpow_nonneg hrho.le _
  have htrueScale : |nextValue - pred| <=
      reluApproxTaylorResidualScale beta C rho a := by
    exact htrue.trans (mul_le_mul_of_nonneg_right hcoeff hrpow0)
  have htrans : |predHat - pred| <=
      Real.exp 1 * reluApproxTaylorResidualScale beta C rho a := by
    exact reluApproxTaylorTransport_error_le_exp
      hbeta hC hrho hstep q a theta thetaHat herr
  have htri : |nextValue - predHat| <=
      |nextValue - pred| + |predHat - pred| := by
    calc
      |nextValue - predHat| = |(nextValue - pred) + -(predHat - pred)| := by
        congr 1
        ring
      _ <= |nextValue - pred| + |-(predHat - pred)| := abs_add_le _ _
      _ = |nextValue - pred| + |predHat - pred| := by rw [abs_neg]
  have hexp : Real.exp 1 <= Real.exp (d : Real) := by
    apply Real.exp_le_exp.mpr
    exact_mod_cast hd
  dsimp only [pred, predHat] at htrueScale htrans htri ⊢
  calc
    |nextValue - Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * thetaHat b)| <=
      |nextValue - Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * theta b)| +
      |Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * thetaHat b) -
       Finset.univ.sum (fun b =>
        reluApproxTaylorTransport step q a b * theta b)| := htri
    _ <= reluApproxTaylorResidualScale beta C rho a +
        Real.exp 1 * reluApproxTaylorResidualScale beta C rho a :=
      add_le_add htrueScale htrans
    _ <= reluApproxTaylorResidualScale beta C rho a +
        Real.exp (d : Real) * reluApproxTaylorResidualScale beta C rho a := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hexp hscale_pos.le)
    _ = (Real.exp (d : Real) + 1) *
        reluApproxTaylorResidualScale beta C rho a := by ring

private theorem reluApprox_normalized_rawTaylor_residual_bound {r d : Nat}
    {beta C rho residual : Real}
    (hbeta_pos : 0 < beta) (hC : 0 ≤ C) (hrho : 0 < rho)
    (a : TaylorMultiindex r d)
    (hresidual : |residual| ≤
      C / (Nat.factorial (r - a.1.val) : Real) *
        Real.rpow rho (((r - a.1.val : Nat) : Real) + beta)) :
    |residual / reluApproxTaylorResidualScale beta C rho a| ≤
      Real.exp (d : Real) + 1 := by
  have hfac : (1 : Real) ≤ Nat.factorial (r - a.1.val) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hfac_pos : (0 : Real) < Nat.factorial (r - a.1.val) := lt_of_lt_of_le zero_lt_one hfac
  have hcoeff : C / (Nat.factorial (r - a.1.val) : Real) ≤ C + 1 := by
    have hdiv_le : C / (Nat.factorial (r - a.1.val) : Real) ≤ C :=
      div_le_self hC hfac
    linarith
  have hrpow_nonneg :
      0 ≤ Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) :=
    Real.rpow_nonneg (le_of_lt hrho) _
  have hscale_pos := reluApproxTaylorResidualScale_pos hbeta_pos hC hrho a
  have hres_scale : |residual| ≤ reluApproxTaylorResidualScale beta C rho a := by
    exact le_trans hresidual
      (mul_le_mul_of_nonneg_right hcoeff hrpow_nonneg)
  have hone : |residual / reluApproxTaylorResidualScale beta C rho a| ≤ 1 := by
    rw [abs_div, abs_of_pos hscale_pos]
    exact (div_le_one hscale_pos).2 hres_scale
  have hexp : (1 : Real) ≤ Real.exp (d : Real) + 1 := by
    linarith [Real.exp_pos (d : Real)]
  exact le_trans hone hexp

/-- Contract exported by the simultaneous correction-code construction. -/
private def ReLUApproxTaylorCorrectionCodeSpec {d r M : Nat}
    (residual : Fin (M ^ d) -> Fin (M ^ d) -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real)
    (correction : Fin (M ^ d) -> Fin (M ^ d) -> TaylorMultiindex r d -> Int)
    (digit : Fin (M ^ d) -> Fin (M ^ d) -> TaylorMultiindex r d -> Nat)
    (code : Fin (M ^ d) -> TaylorMultiindex r d -> Real) : Prop :=
  let cDigit : Nat := Nat.ceil (Real.exp (d : Real))
  let base : Nat := 4 + 2 * cDigit
  (forall i k a,
      -(cDigit : Int) - 1 <= correction i k a /\
        correction i k a <= (cDigit : Int) + 1) /\
    (forall i k a,
      (digit i k a : Int) = correction i k a + ((cDigit : Int) + 2) /\
        1 <= digit i k a /\ digit i k a <= 2 * cDigit + 3) /\
    (forall i a,
      code i a = Finset.univ.sum (fun k : Fin (M ^ d) =>
        (digit i k a : Real) / (base : Real) ^ (k.val + 1))) /\
    (forall i k a,
      0 <= residual i k a - (correction i k a : Real) * scale a /\
        residual i k a - (correction i k a : Real) * scale a < scale a) /\
    forall i a, 0 <= code i a /\ code i a < 1

private theorem exists_reluApprox_degreeProfiled_correction_code {d r M : Nat}
    (hM : 0 < M) {beta C rho : Real}
    (hbeta_pos : 0 < beta) (hC : 0 ≤ C) (hrho : 0 < rho)
    (residual : Fin (M ^ d) -> Fin (M ^ d) -> TaylorMultiindex r d -> Real)
    (hresidual : forall i k a,
      |residual i k a| ≤
        C / (Nat.factorial (r - a.1.val) : Real) *
          Real.rpow rho (((r - a.1.val : Nat) : Real) + beta)) :
    exists correction digit code,
      ReLUApproxTaylorCorrectionCodeSpec residual
        (reluApproxTaylorResidualScale beta C rho) correction digit code := by
  have hscale : forall a : TaylorMultiindex r d,
      0 < reluApproxTaylorResidualScale beta C rho a :=
    reluApproxTaylorResidualScale_pos hbeta_pos hC hrho
  have hnormalized : forall i k a,
      |residual i k a / reluApproxTaylorResidualScale beta C rho a| <=
        Real.exp (d : Real) + 1 := by
    intro i k a
    exact reluApprox_normalized_rawTaylor_residual_bound
      hbeta_pos hC hrho a (hresidual i k a)
  simpa [ReLUApproxTaylorCorrectionCodeSpec] using
    (exists_reluApprox_bounded_correction_code
      (d := d) (r := r) hM residual
      (reluApproxTaylorResidualScale beta C rho) hscale hnormalized)

/-- If each decoded correction rounds the residual from the *current
approximate* Taylor predictor, the next register is reset to within one
degree-dependent scale of the true coefficient.  Thus errors do not accumulate
through the identity term of the Taylor transport. -/
private theorem reluApprox_correctedAffineRecursion_tracks_target
    {Aidx : Type} [Fintype Aidx] {T : Nat}
    (scale : Aidx -> Real) (hscale : forall a, 0 < scale a)
    (theta thetaHat : Nat -> Aidx -> Real)
    (trans : Nat -> Aidx -> Aidx -> Real)
    (correction : Nat -> Aidx -> Int)
    (hinit : forall a, thetaHat 0 a = theta 0 a)
    (hupdate : forall k, k < T -> forall a,
      thetaHat (k + 1) a =
        Finset.univ.sum (fun b => trans k a b * thetaHat k b) +
          (correction k a : Real) * scale a)
    (hround : forall k, k < T -> forall a,
      let predictor :=
        Finset.univ.sum (fun b => trans k a b * thetaHat k b)
      0 <= theta (k + 1) a - predictor -
          (correction k a : Real) * scale a /\
        theta (k + 1) a - predictor -
          (correction k a : Real) * scale a < scale a) :
    forall k, k <= T -> forall a,
      |thetaHat k a - theta k a| < scale a := by
  intro k hk
  cases k with
  | zero =>
      intro a
      rw [hinit]
      simpa using hscale a
  | succ k =>
      have hklt : k < T := Nat.lt_of_succ_le hk
      intro a
      let predictor :=
        Finset.univ.sum (fun b => trans k a b * thetaHat k b)
      have hu := hupdate k hklt a
      have hr := hround k hklt a
      dsimp only [predictor] at hu hr
      have heq : thetaHat (k + 1) a - theta (k + 1) a =
          -(theta (k + 1) a - predictor -
            (correction k a : Real) * scale a) := by
        rw [hu]
        dsimp [predictor]
        ring
      rw [heq, abs_neg, abs_of_nonneg hr.1]
      exact hr.2

/-- Canonical Taylor-register recursion: predict affinely from the preceding
approximate state and round the residual in units of the prescribed scale. -/
noncomputable def reluApproxCorrectedAffineRecursion
    {Aidx : Type} [Fintype Aidx]
    (scale : Aidx -> Real) (theta : Nat -> Aidx -> Real)
    (trans : Nat -> Aidx -> Aidx -> Real) : Nat -> Aidx -> Real
  | 0 => theta 0
  | k + 1 => fun a =>
      let predictor := Finset.univ.sum (fun b =>
        trans k a b * reluApproxCorrectedAffineRecursion scale theta trans k b)
      predictor +
        (Int.floor ((theta (k + 1) a - predictor) / scale a) : Real) * scale a

/-- Signed correction digit used by the canonical corrected recursion. -/
private noncomputable def reluApproxCorrectedAffineCorrection
    {Aidx : Type} [Fintype Aidx]
    (scale : Aidx -> Real) (theta : Nat -> Aidx -> Real)
    (trans : Nat -> Aidx -> Aidx -> Real) (k : Nat) (a : Aidx) : Int :=
  let predictor := Finset.univ.sum (fun b =>
    trans k a b * reluApproxCorrectedAffineRecursion scale theta trans k b)
  Int.floor ((theta (k + 1) a - predictor) / scale a)

private theorem reluApproxCorrectedAffineRecursion_succ
    {Aidx : Type} [Fintype Aidx]
    (scale : Aidx -> Real) (theta : Nat -> Aidx -> Real)
    (trans : Nat -> Aidx -> Aidx -> Real) (k : Nat) (a : Aidx) :
    reluApproxCorrectedAffineRecursion scale theta trans (k + 1) a =
      Finset.univ.sum (fun b => trans k a b *
        reluApproxCorrectedAffineRecursion scale theta trans k b) +
      (reluApproxCorrectedAffineCorrection scale theta trans k a : Real) *
        scale a := by
  rfl

private theorem reluApproxCorrectedAffineCorrection_rounds
    {Aidx : Type} [Fintype Aidx]
    (scale : Aidx -> Real) (hscale : forall a, 0 < scale a)
    (theta : Nat -> Aidx -> Real) (trans : Nat -> Aidx -> Aidx -> Real)
    (k : Nat) (a : Aidx) :
    let predictor := Finset.univ.sum (fun b =>
      trans k a b * reluApproxCorrectedAffineRecursion scale theta trans k b)
    0 <= theta (k + 1) a - predictor -
        (reluApproxCorrectedAffineCorrection scale theta trans k a : Real) * scale a /\
      theta (k + 1) a - predictor -
        (reluApproxCorrectedAffineCorrection scale theta trans k a : Real) * scale a <
          scale a := by
  let predictor := Finset.univ.sum (fun b =>
    trans k a b * reluApproxCorrectedAffineRecursion scale theta trans k b)
  let z := (theta (k + 1) a - predictor) / scale a
  have hs := hscale a
  have hsne : scale a ≠ 0 := ne_of_gt hs
  have hlo : (Int.floor z : Real) <= z := Int.floor_le z
  have hhi : z < (Int.floor z : Real) + 1 := Int.lt_floor_add_one z
  have hmullo := mul_le_mul_of_nonneg_right hlo hs.le
  have hmulhi := mul_lt_mul_of_pos_right hhi hs
  have hz : z * scale a = theta (k + 1) a - predictor := by
    dsimp [z]
    field_simp
  dsimp only
  change 0 <= theta (k + 1) a - predictor -
      (Int.floor z : Real) * scale a /\
    theta (k + 1) a - predictor -
      (Int.floor z : Real) * scale a < scale a
  rw [← hz]
  constructor <;> nlinarith

/-- Every register of the canonical corrected recursion tracks its target
coefficient to within its own degree-dependent scale at every finite time. -/
theorem reluApproxCorrectedAffineRecursion_tracks_target
    {Aidx : Type} [Fintype Aidx] {T : Nat}
    (scale : Aidx -> Real) (hscale : forall a, 0 < scale a)
    (theta : Nat -> Aidx -> Real) (trans : Nat -> Aidx -> Aidx -> Real) :
    forall k, k <= T -> forall a,
      |reluApproxCorrectedAffineRecursion scale theta trans k a - theta k a| <
        scale a := by
  exact reluApprox_correctedAffineRecursion_tracks_target
    scale hscale theta (reluApproxCorrectedAffineRecursion scale theta trans)
      trans (reluApproxCorrectedAffineCorrection scale theta trans)
      (fun _ => rfl)
      (fun k _hk a =>
        reluApproxCorrectedAffineRecursion_succ scale theta trans k a)
      (fun k _hk a =>
        reluApproxCorrectedAffineCorrection_rounds scale hscale theta trans k a)

/-- Holder smoothness includes the differentiability needed by the Taylor
transport formulas, including the vacuous order-zero case. -/
theorem isHolderSmoothFunction_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] {r : Nat} {beta C : Real}
    {f : E -> Real} (hbeta : 0 < beta) (hC : 0 <= C)
    (hf : IsHolderSmoothFunction r beta C f) :
    ContDiff Real r f := by
  cases r with
  | zero =>
      have hholder : HolderWith ⟨C, hC⟩ ⟨beta, hbeta.le⟩ f := by
        intro x y
        rw [edist_dist, edist_dist]
        simp only [NNReal.coe_mk, ENNReal.coe_nnreal_eq]
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hbeta.le]
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (by
          simpa [Real.dist_eq] using hf x y)
      simpa using
        ((contDiff_zero (𝕜 := Real) (E := E) (F := Real) (f := f)).2
          (hholder.continuous (by exact_mod_cast hbeta)))
  | succ r => exact hf.1

/-- Exact raw Taylor coefficient table along a finite-state path. -/
noncomputable def reluApproxExactTaylorState {r d : Nat}
    (f : (Fin d -> Real) -> Real) (center : Nat -> Fin d -> Real) :
    Nat -> TaylorMultiindex r d -> Real :=
  fun k a => reluApproxRawTaylorCoefficient f a (center k)

/-- Taylor transport table attached to the signed coordinate steps of a path. -/
noncomputable def reluApproxTaylorPathTransport {r d : Nat}
    (coordinate : Nat -> Fin d) (step : Nat -> Real) :
    Nat -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real :=
  fun k => reluApproxTaylorTransport (step k) (coordinate k)

/-- Degree-profiled corrected Taylor state used by the state machine. -/
noncomputable def reluApproxCanonicalTaylorState {r d : Nat}
    (beta C rho : Real) (f : (Fin d -> Real) -> Real)
    (center : Nat -> Fin d -> Real) (coordinate : Nat -> Fin d)
    (step : Nat -> Real) : Nat -> TaylorMultiindex r d -> Real :=
  reluApproxCorrectedAffineRecursion
    (reluApproxTaylorResidualScale beta C rho)
    (reluApproxExactTaylorState f center)
    (reluApproxTaylorPathTransport coordinate step)

/-- Residual that is rounded at one transition of the canonical Taylor state. -/
private noncomputable def reluApproxCanonicalTaylorResidual {r d : Nat}
    (beta C rho : Real) (f : (Fin d -> Real) -> Real)
    (center : Nat -> Fin d -> Real) (coordinate : Nat -> Fin d)
    (step : Nat -> Real) (k : Nat) (a : TaylorMultiindex r d) : Real :=
  reluApproxExactTaylorState f center (k + 1) a -
    Finset.univ.sum (fun b =>
      reluApproxTaylorPathTransport coordinate step k a b *
        reluApproxCanonicalTaylorState beta C rho f center coordinate step k b)

/-- The correction residual of the canonical Taylor state lies in the bounded
alphabet used by the existing simultaneous base-tail encoder.  This is the
analytic bridge between the old Taylor estimates and the concrete decoder. -/
private theorem reluApproxCanonicalTaylorResidual_normalized_bound
    {r d : Nat} {beta C B rho : Real}
    (hd : 0 < d) (hbeta : 0 < beta) (hC : 0 <= C) (hrho : 0 < rho)
    (f : (Fin d -> Real) -> Real) (hf : f ∈ holderSmoothBall r beta C B)
    (center : Nat -> Fin d -> Real) (coordinate : Nat -> Fin d)
    (step : Nat -> Real)
    (hmove : forall k, center (k + 1) - center k =
      reluApproxCoordinateStep (coordinate k) (step k))
    (hstep : forall k, |step k| <= rho) (k : Nat)
    (a : TaylorMultiindex r d) :
    |reluApproxCanonicalTaylorResidual beta C rho f center coordinate step k a /
        reluApproxTaylorResidualScale beta C rho a| <=
      Real.exp (d : Real) + 1 := by
  let scale : TaylorMultiindex r d -> Real :=
    reluApproxTaylorResidualScale beta C rho
  let theta : Nat -> TaylorMultiindex r d -> Real :=
    reluApproxExactTaylorState f center
  let trans := reluApproxTaylorPathTransport (r := r) coordinate step
  let thetaHat : Nat -> TaylorMultiindex r d -> Real :=
    reluApproxCanonicalTaylorState beta C rho f center coordinate step
  have hscale : forall b : TaylorMultiindex r d, 0 < scale b := by
    intro b
    exact reluApproxTaylorResidualScale_pos hbeta hC hrho b
  have htrack : forall b : TaylorMultiindex r d,
      |thetaHat k b - theta k b| <= scale b := by
    intro b
    exact le_of_lt (reluApproxCorrectedAffineRecursion_tracks_target
      (T := k) scale hscale theta trans k le_rfl b)
  have htrue :
      |theta (k + 1) a - Finset.univ.sum (fun b =>
          trans k a b * theta k b)| <=
        C / (Nat.factorial (r - a.1.val) : Real) *
          Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) := by
    exact reluApprox_rawTaylorTransport_residual_bound
      hbeta.le hC hrho.le f hf.1
      (isHolderSmoothFunction_contDiff hbeta hC hf.1) a (coordinate k) (step k)
      (center k) (center (k + 1)) (hmove k) (hstep k)
  have hres :
      |theta (k + 1) a - Finset.univ.sum (fun b =>
          trans k a b * thetaHat k b)| <=
        (Real.exp (d : Real) + 1) * scale a := by
    exact reluApprox_approximateTaylorTransport_residual_bound
      hd hbeta hC hrho (hstep k) (coordinate k) a
      (theta k) (thetaHat k) htrack htrue
  have hscalea : 0 < scale a := hscale a
  rw [abs_div, abs_of_pos hscalea, div_le_iff₀ hscalea]
  simpa [reluApproxCanonicalTaylorResidual, theta, thetaHat, trans, scale,
    reluApproxExactTaylorState, reluApproxTaylorPathTransport,
    reluApproxCanonicalTaylorState] using hres

/-- A signed integer is uniquely determined by the half-open rounding interval
of a residual at positive scale. -/
private theorem reluApprox_integerCorrection_unique {residual scale : Real}
    (hscale : 0 < scale) {m n : Int}
    (hm : 0 <= residual - (m : Real) * scale /\
      residual - (m : Real) * scale < scale)
    (hn : 0 <= residual - (n : Real) * scale /\
      residual - (n : Real) * scale < scale) :
    m = n := by
  have hmlo : (m : Real) <= residual / scale := by
    rw [le_div_iff₀ hscale]
    linarith [hm.1]
  have hmhi : residual / scale < (m : Real) + 1 := by
    rw [div_lt_iff₀ hscale]
    linarith [hm.2]
  have hnlo : (n : Real) <= residual / scale := by
    rw [le_div_iff₀ hscale]
    linarith [hn.1]
  have hnhi : residual / scale < (n : Real) + 1 := by
    rw [div_lt_iff₀ hscale]
    linarith [hn.2]
  have hmfloor : Int.floor (residual / scale) = m :=
    Int.floor_eq_iff.mpr ⟨hmlo, hmhi⟩
  have hnfloor : Int.floor (residual / scale) = n :=
    Int.floor_eq_iff.mpr ⟨hnlo, hnhi⟩
  exact hmfloor.symm.trans hnfloor

/-- Extend a nonempty finite center path by retaining its current value after
the final center. -/
private noncomputable def reluApproxFrozenCenterPath
    {d T : Nat} (hT : 0 < T) (center : Fin T -> Fin d -> Real) :
    Nat -> Fin d -> Real
  | 0 => center ⟨0, hT⟩
  | k + 1 => if hk : k + 1 < T then center ⟨k + 1, hk⟩
      else reluApproxFrozenCenterPath hT center k

/-- Extend a finite signed-coordinate path by freezing its last point.  The
result supplies exactly the path, coordinate and signed-step data consumed by
the canonical Taylor-correction encoder. -/
theorem exists_reluApproxFrozenCenterPathData
    {d T : Nat} (hd : 0 < d) (hT : 0 < T)
    (center : Fin T -> Fin d -> Real) (rho : Real) (hrho : 0 <= rho)
    (hadj : forall k : Nat, forall hk : k + 1 < T,
      exists q : Fin d,
        (center ⟨k + 1, hk⟩ q =
            center ⟨k, Nat.lt_of_succ_lt hk⟩ q + rho \/
          center ⟨k + 1, hk⟩ q =
            center ⟨k, Nat.lt_of_succ_lt hk⟩ q - rho) /\
        forall u : Fin d, u ≠ q ->
          center ⟨k + 1, hk⟩ u =
            center ⟨k, Nat.lt_of_succ_lt hk⟩ u) :
    exists path : Nat -> Fin d -> Real,
    exists coordinate : Nat -> Fin d,
    exists step : Nat -> Real,
      (forall k : Nat, forall hk : k < T, path k = center ⟨k, hk⟩) /\
      (forall k : Nat, path (k + 1) - path k =
        reluApproxCoordinateStep (coordinate k) (step k)) /\
      forall k : Nat, |step k| <= rho := by
  let path : Nat -> Fin d -> Real := reluApproxFrozenCenterPath hT center
  let coordinate : Nat -> Fin d := fun k =>
    if hk : k + 1 < T then Classical.choose (hadj k hk) else ⟨0, hd⟩
  let step : Nat -> Real := fun k =>
    if hk : k + 1 < T then
      if center ⟨k + 1, hk⟩ (Classical.choose (hadj k hk)) =
          center ⟨k, Nat.lt_of_succ_lt hk⟩ (Classical.choose (hadj k hk)) + rho
      then rho else -rho
    else 0
  have hpath_center : forall k : Nat, forall hk : k < T,
      path k = center ⟨k, hk⟩ := by
    intro k hk
    cases k with
    | zero => rfl
    | succ k => simp [path, reluApproxFrozenCenterPath, hk]
  refine ⟨path, coordinate, step, ?_, ?_, ?_⟩
  · exact hpath_center
  · intro k
    funext u
    by_cases hk : k + 1 < T
    · have hk0 : k < T := Nat.lt_of_succ_lt hk
      let q : Fin d := Classical.choose (hadj k hk)
      have hq := (Classical.choose_spec (hadj k hk)).1
      have hfixed := (Classical.choose_spec (hadj k hk)).2
      change
        center ⟨k + 1, hk⟩ q = center ⟨k, hk0⟩ q + rho \/
          center ⟨k + 1, hk⟩ q = center ⟨k, hk0⟩ q - rho at hq
      change forall v : Fin d, v ≠ q ->
        center ⟨k + 1, hk⟩ v = center ⟨k, hk0⟩ v at hfixed
      have hcoord : coordinate k = q := by simp [coordinate, hk, q]
      by_cases hplus : center ⟨k + 1, hk⟩ q = center ⟨k, hk0⟩ q + rho
      · have hstep : step k = rho := by
          simp only [step, dif_pos hk]
          rw [if_pos]
          simpa [q] using hplus
        rw [hstep, hcoord]
        change path (k + 1) u - path k u = _
        rw [congrFun (hpath_center k hk0) u]
        by_cases hu : u = q
        · subst u
          simp [path, reluApproxFrozenCenterPath, hk, hk0,
            reluApproxCoordinateStep, hplus]
        · have hsame := hfixed u hu
          simp [path, reluApproxFrozenCenterPath, hk, hk0,
            reluApproxCoordinateStep, hu, hsame]
      · have hminus :
            center ⟨k + 1, hk⟩ q = center ⟨k, hk0⟩ q - rho :=
          hq.resolve_left hplus
        have hstep : step k = -rho := by
          simp only [step, dif_pos hk]
          rw [if_neg]
          simpa [q] using hplus
        rw [hstep, hcoord]
        change path (k + 1) u - path k u = _
        rw [congrFun (hpath_center k hk0) u]
        by_cases hu : u = q
        · subst u
          simp [path, reluApproxFrozenCenterPath, hk, hk0,
            reluApproxCoordinateStep, hminus]
        · have hsame := hfixed u hu
          simp [path, reluApproxFrozenCenterPath, hk, hk0,
            reluApproxCoordinateStep, hu, hsame]
    · have hk_ge : T <= k + 1 := Nat.le_of_not_gt hk
      have hstep : step k = 0 := by simp [step, hk]
      rw [hstep]
      simp [path, reluApproxFrozenCenterPath, hk,
        reluApproxCoordinateStep]
  · intro k
    by_cases hk : k + 1 < T
    · by_cases hplus :
          center ⟨k + 1, hk⟩ (Classical.choose (hadj k hk)) =
          center ⟨k, Nat.lt_of_succ_lt hk⟩
              (Classical.choose (hadj k hk)) + rho
      · simp [step, hk, hplus, abs_of_nonneg hrho]
      · simp [step, hk, hplus, abs_of_nonneg hrho]
    · simp [step, hk, hrho]

/-- A canonical two-scale layout admits one fine-path transition schedule shared
by every coarse block.  Only the coarse offset changes with the block; the
coordinate and signed fine step are common. -/
private theorem exists_reluApproxCanonicalCommonFinePathData
    {d M : Nat} (hd : 0 < d) (hM : 2 <= M)
    (orderC orderF : Fin (M ^ d) ≃ (Fin d -> Fin M))
    (center scale : Fin (M ^ d) -> Fin (M ^ d) -> Fin d -> Real)
    (hcanonical :
      IsCanonicalTwoScaleLayout d M orderC orderF center scale) :
    let rho : Real := ((M ^ 2 - 1 : Nat) : Real)⁻¹
    exists path : Fin (M ^ d) -> Nat -> Fin d -> Real,
    exists coordinate : Nat -> Fin d,
    exists signedStep : Nat -> Real,
      (forall b k, forall hk : k < M ^ d,
        path b k = center b ⟨k, hk⟩) /\
      (forall b k, path b (k + 1) - path b k =
        reluApproxCoordinateStep (coordinate k) (signedStep k)) /\
      forall k, |signedStep k| <= rho := by
  classical
  dsimp only
  have hMpos : 0 < M := by omega
  have hTpos : 0 < M ^ d := pow_pos hMpos d
  let b0 : Fin (M ^ d) := ⟨0, hTpos⟩
  let t0 : Fin (M ^ d) := ⟨0, hTpos⟩
  let rho : Real := ((M ^ 2 - 1 : Nat) : Real)⁻¹
  have hrho : 0 <= rho := by
    dsimp [rho]
    positivity
  obtain ⟨path0, coordinate, signedStep, hpath0, hmove0, hstep⟩ :=
    exists_reluApproxFrozenCenterPathData hd hTpos (center b0) rho hrho
      (by
        intro k hk
        obtain ⟨q, hq, hfixed⟩ := hcanonical.2.2.2.2.2.2.2 b0 k hk
        exact ⟨q, hq, fun u hu => hfixed u (bne_iff_ne.mpr hu)⟩)
  let path : Fin (M ^ d) -> Nat -> Fin d -> Real := fun b k q =>
    path0 k q + (center b t0 q - center b0 t0 q)
  refine ⟨path, coordinate, signedStep, ?_, ?_, hstep⟩
  · intro b k hk
    funext q
    have hp0 := congrFun (hpath0 k hk) q
    have hformula := hcanonical.2.2.1
    have horderF0 := congrFun (hcanonical.2.1.1 hMpos) q
    have horderF0val : (orderF t0 q).val = 0 := by
      simpa [t0] using congrArg Fin.val horderF0
    dsimp [path]
    rw [hp0, hformula b0 ⟨k, hk⟩ q, hformula b t0 q,
      hformula b0 t0 q, hformula b ⟨k, hk⟩ q, horderF0val]
    norm_num
    ring
  · intro b k
    funext q
    have hm0 := congrFun (hmove0 k) q
    dsimp [path]
    calc
      path0 (k + 1) q + (center b t0 q - center b0 t0 q) -
          (path0 k q + (center b t0 q - center b0 t0 q)) =
        path0 (k + 1) q - path0 k q := by ring
      _ = reluApproxCoordinateStep (coordinate k) (signedStep k) q := hm0

/-- Simultaneous existing base-tail codes can be chosen to encode exactly the
canonical Taylor-state corrections on every coarse-cell path. -/
theorem exists_reluApproxCanonicalTaylorCorrectionCode
    {r d M : Nat} (hd : 0 < d) (hM : 0 < M)
    {beta C B rho : Real} (hbeta : 0 < beta) (hC : 0 <= C)
    (hrho : 0 < rho) (f : (Fin d -> Real) -> Real)
    (hf : f ∈ holderSmoothBall r beta C B)
    (center : Fin (M ^ d) -> Nat -> Fin d -> Real)
    (coordinate : Fin (M ^ d) -> Nat -> Fin d)
    (step : Fin (M ^ d) -> Nat -> Real)
    (hmove : forall i k, center i (k + 1) - center i k =
      reluApproxCoordinateStep (coordinate i k) (step i k))
    (hstep : forall i k, |step i k| <= rho) :
    let residual := fun i : Fin (M ^ d) => fun k : Fin (M ^ d) =>
      reluApproxCanonicalTaylorResidual beta C rho f (center i)
        (coordinate i) (step i) k.val
    exists correction digit code,
      ReLUApproxTaylorCorrectionCodeSpec residual
        (reluApproxTaylorResidualScale beta C rho) correction digit code /\
      forall i k a,
        correction i k a =
          reluApproxCorrectedAffineCorrection
            (reluApproxTaylorResidualScale (r := r) (d := d) beta C rho)
            (reluApproxExactTaylorState (r := r) f (center i))
            (reluApproxTaylorPathTransport (r := r) (coordinate i) (step i))
            k.val a := by
  let residual : Fin (M ^ d) -> Fin (M ^ d) -> TaylorMultiindex r d -> Real :=
    fun i : Fin (M ^ d) => fun k : Fin (M ^ d) =>
    reluApproxCanonicalTaylorResidual beta C rho f (center i)
      (coordinate i) (step i) k.val
  have hnormalized : forall i k a,
      |residual i k a / reluApproxTaylorResidualScale beta C rho a| <=
        Real.exp (d : Real) + 1 := by
    intro i k a
    exact reluApproxCanonicalTaylorResidual_normalized_bound
      hd hbeta hC hrho f hf (center i) (coordinate i) (step i)
      (hmove i) (hstep i) k.val a
  obtain ⟨correction, digit, code, hspec⟩ :=
    exists_reluApprox_bounded_correction_code hM residual
      (reluApproxTaylorResidualScale beta C rho)
      (reluApproxTaylorResidualScale_pos hbeta hC hrho) hnormalized
  refine ⟨correction, digit, code, hspec, ?_⟩
  intro i k a
  have hscale := reluApproxTaylorResidualScale_pos hbeta hC hrho a
  have hreturned := hspec.2.2.2.1 i k a
  have hcanonical := reluApproxCorrectedAffineCorrection_rounds
    (reluApproxTaylorResidualScale beta C rho)
    (reluApproxTaylorResidualScale_pos hbeta hC hrho)
    (reluApproxExactTaylorState f (center i))
    (reluApproxTaylorPathTransport (coordinate i) (step i)) k.val a
  apply reluApprox_integerCorrection_unique hscale hreturned
  simpa [residual, reluApproxCanonicalTaylorResidual,
    reluApproxExactTaylorState, reluApproxTaylorPathTransport,
    reluApproxCanonicalTaylorState] using hcanonical

/-! ## Two-pass schedule composition -/

/-- A finite base expansion beginning at `start`, written with its first digit
in the `base⁻¹` place.  Taking one floor digit shifts this tail by one. -/
noncomputable def reluApproxFiniteBaseTail (base : Real)
    (digit : Nat -> Nat) (start length : Nat) : Real :=
  Finset.sum (Finset.range length) (fun j =>
    (digit (start + j) : Real) / base ^ (j + 1))

private theorem reluApproxFiniteBaseTail_succ {base : Real} (hbase : base ≠ 0)
    (digit : Nat -> Nat) (start length : Nat) :
    base * reluApproxFiniteBaseTail base digit start (length + 1) =
      (digit start : Real) +
        reluApproxFiniteBaseTail base digit (start + 1) length := by
  rw [reluApproxFiniteBaseTail, Finset.sum_range_succ']
  rw [mul_add]
  simp only [Nat.zero_add, Nat.add_zero, pow_one]
  have hhead : base * ((digit start : Real) / base) = (digit start : Real) := by
    field_simp
  rw [hhead, add_comm]
  congr 1
  rw [reluApproxFiniteBaseTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hpow : base ^ (j + 1 + 1) = base * base ^ (j + 1) := by
    rw [pow_succ']
  rw [hpow]
  field_simp
  congr 2
  omega

/-- A floor-augmented affine schedule started from an already computed state. -/
private noncomputable def reluApproxFloorAffineRecursionFrom {s T : Nat}
    (R : Real) (B : Nat) (base : Real)
    (tail : Fin T -> Fin s)
    (P : Fin T -> Matrix (Fin s) (Fin s) Real)
    (bias digitCoeff : Fin T -> Fin s -> Real)
    (u0 : Fin s -> Real) : Nat -> Fin s -> Real
  | 0 => u0
  | t + 1 =>
      if ht : t < T then
        reluApproxFloorAffineState R B base (tail ⟨t, ht⟩)
          (P ⟨t, ht⟩) (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩)
          (reluApproxFloorAffineRecursionFrom R B base tail P bias digitCoeff u0 t)
      else
        reluApproxFloorAffineRecursionFrom R B base tail P bias digitCoeff u0 t

/-- The affine recursion driven by a prescribed digit sequence, with an
arbitrary initial register state. -/
private noncomputable def reluApproxFloorAffineDigitRecursionFrom {s T : Nat}
    (P : Fin T -> Matrix (Fin s) (Fin s) Real)
    (bias digitCoeff : Fin T -> Fin s -> Real)
    (digit : Fin T -> Nat) (u0 : Fin s -> Real) : Nat -> Fin s -> Real
  | 0 => u0
  | t + 1 =>
      if ht : t < T then
        reluApproxFloorAffineDigitState (P ⟨t, ht⟩)
          (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩) (digit ⟨t, ht⟩)
          (reluApproxFloorAffineDigitRecursionFrom
            P bias digitCoeff digit u0 t)
      else
        reluApproxFloorAffineDigitRecursionFrom
          P bias digitCoeff digit u0 t

/-- A positive base-tail certificate at every step identifies the concrete
floor recursion from an arbitrary state with its prescribed digit recursion. -/
private theorem reluApproxFloorAffineRecursionFrom_eq_digit_of_bounded_baseTail
    {s T : Nat}
    (dExp : Real) (c : Nat) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (tailLength : Fin T -> Nat)
    (hTailLength : forall k : Fin T, 1 <= tailLength k)
    (hRsep : forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-(tailLength k : Int)))
    (stateTail : Fin T -> Fin s)
    (P : Fin T -> Matrix (Fin s) (Fin s) Real)
    (bias digitCoeff : Fin T -> Fin s -> Real)
    (digit : Fin T -> Nat)
    (tailDigit : forall k : Fin T, Fin (tailLength k) -> Nat)
    (hDigitLower : forall k : Fin T, 1 <= digit k)
    (hDigitUpper : forall k : Fin T, digit k <= 2 * c + 3)
    (hTailLower : forall k : Fin T, forall j : Fin (tailLength k),
      1 <= tailDigit k j)
    (hTailUpper : forall k : Fin T, forall j : Fin (tailLength k),
      tailDigit k j <= 2 * c + 3)
    (u0 : Fin s -> Real)
    (hcode : forall k : Fin T,
      (baseNat : Real) *
          reluApproxFloorAffineRecursionFrom R floorBound
            (baseNat : Real) stateTail P bias digitCoeff u0 k.val
              (stateTail k) =
        (digit k : Real) + Finset.univ.sum (fun j : Fin (tailLength k) =>
          (tailDigit k j : Real) / (baseNat : Real) ^ (j.val + 1)))
    (t : Nat) (ht : t <= T) :
    reluApproxFloorAffineRecursionFrom R floorBound
        (baseNat : Real) stateTail P bias digitCoeff u0 t =
      reluApproxFloorAffineDigitRecursionFrom
        P bias digitCoeff digit u0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      let k : Fin T := ⟨t, htlt⟩
      let signedDigit : Int := (digit k : Int) - (c + 2 : Int)
      have hshift : (digit k : Int) = signedDigit + (c + 2 : Int) := by
        dsimp [signedDigit]
        ring
      rcases reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
          dExp c hc baseNat hbase (digit k) signedDigit hshift
          (hDigitLower k) (hDigitUpper k) (tailLength k) (hTailLength k)
          (tailDigit k) (hTailLower k) (hTailUpper k)
          ((baseNat : Real) *
            reluApproxFloorAffineRecursionFrom R floorBound
              (baseNat : Real) stateTail P bias digitCoeff u0 t (stateTail k))
          (hcode k) floorBound hFloorBound R hR (hRsep k) with
        ⟨_hgap, _hclass, htruncated, hfloor, _hsigned⟩
      rw [ih (Nat.le_of_succ_le ht)] at htruncated hfloor
      rw [reluApproxFloorAffineRecursionFrom,
        reluApproxFloorAffineDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      funext i
      simp only [reluApproxFloorAffineState,
        reluApproxFloorAffineDigitState]
      rw [htruncated, hfloor]

/-- Non-circular form of the floor-decoder invariant: it is enough to prove the
base-tail equation for the prescribed digit recursion.  The theorem then
transfers that invariant to the concrete ReLU floor recursion inductively. -/
private theorem reluApproxFloorAffineRecursionFrom_eq_digit_of_digitBaseTail
    {s T : Nat}
    (dExp : Real) (c : Nat) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (tailLength : Fin T -> Nat)
    (hTailLength : forall k : Fin T, 1 <= tailLength k)
    (hRsep : forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-(tailLength k : Int)))
    (stateTail : Fin T -> Fin s)
    (P : Fin T -> Matrix (Fin s) (Fin s) Real)
    (bias digitCoeff : Fin T -> Fin s -> Real)
    (digit : Fin T -> Nat)
    (tailDigit : forall k : Fin T, Fin (tailLength k) -> Nat)
    (hDigitLower : forall k : Fin T, 1 <= digit k)
    (hDigitUpper : forall k : Fin T, digit k <= 2 * c + 3)
    (hTailLower : forall k : Fin T, forall j : Fin (tailLength k),
      1 <= tailDigit k j)
    (hTailUpper : forall k : Fin T, forall j : Fin (tailLength k),
      tailDigit k j <= 2 * c + 3)
    (u0 : Fin s -> Real)
    (hcode : forall k : Fin T,
      (baseNat : Real) *
          reluApproxFloorAffineDigitRecursionFrom
            P bias digitCoeff digit u0 k.val (stateTail k) =
        (digit k : Real) + Finset.univ.sum (fun j : Fin (tailLength k) =>
          (tailDigit k j : Real) / (baseNat : Real) ^ (j.val + 1)))
    (t : Nat) (ht : t <= T) :
    reluApproxFloorAffineRecursionFrom R floorBound
        (baseNat : Real) stateTail P bias digitCoeff u0 t =
      reluApproxFloorAffineDigitRecursionFrom
        P bias digitCoeff digit u0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      let k : Fin T := ⟨t, htlt⟩
      let signedDigit : Int := (digit k : Int) - (c + 2 : Int)
      have hshift : (digit k : Int) = signedDigit + (c + 2 : Int) := by
        dsimp [signedDigit]
        ring
      have hcodeConcrete :
          (baseNat : Real) *
              reluApproxFloorAffineRecursionFrom R floorBound
                (baseNat : Real) stateTail P bias digitCoeff u0 t
                  (stateTail k) =
            (digit k : Real) + Finset.univ.sum (fun j : Fin (tailLength k) =>
              (tailDigit k j : Real) / (baseNat : Real) ^ (j.val + 1)) := by
        rw [ih (Nat.le_of_succ_le ht)]
        exact hcode k
      rcases reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
          dExp c hc baseNat hbase (digit k) signedDigit hshift
          (hDigitLower k) (hDigitUpper k) (tailLength k) (hTailLength k)
          (tailDigit k) (hTailLower k) (hTailUpper k)
          ((baseNat : Real) *
            reluApproxFloorAffineRecursionFrom R floorBound
              (baseNat : Real) stateTail P bias digitCoeff u0 t (stateTail k))
          hcodeConcrete floorBound hFloorBound R hR (hRsep k) with
        ⟨_hgap, _hclass, htruncated, hfloor, _hsigned⟩
      rw [ih (Nat.le_of_succ_le ht)] at htruncated hfloor
      rw [reluApproxFloorAffineRecursionFrom,
        reluApproxFloorAffineDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      funext i
      simp only [reluApproxFloorAffineState,
        reluApproxFloorAffineDigitState]
      rw [htruncated, hfloor]

/-- The generic signed-macro recursion implements the floor-affine recursion
from an arbitrary initial state. -/
private theorem reluApproxMacroRecursionFrom_floorAffine {s T : Nat}
    (R : Real) (B : Nat) (base : Real)
    (tail : Fin T -> Fin s)
    (P : Fin T -> Matrix (Fin s) (Fin s) Real)
    (bias digitCoeff : Fin T -> Fin s -> Real)
    (u0 : Fin s -> Real) (t : Nat) (ht : t <= T) :
    reluApproxMacroRecursionFrom
        (fun k : Fin T => reluApproxFloorAffineFeatureMatrix base B (tail k))
        (fun _ : Fin T => reluApproxFloorAffineFeatureBias R B)
        (fun k : Fin T =>
          reluApproxFloorAffineUpdateMatrix R B (P k) (digitCoeff k))
        bias u0 t =
      reluApproxFloorAffineRecursionFrom R B base tail P bias digitCoeff u0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxMacroRecursionFrom,
        reluApproxFloorAffineRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxFloorAffineMacro_exact R B base (tail ⟨t, htlt⟩)
        (P ⟨t, htlt⟩) (bias ⟨t, htlt⟩) (digitCoeff ⟨t, htlt⟩)
        (reluApproxFloorAffineRecursionFrom R B base tail P bias digitCoeff u0 t)

/-- A concrete vector-valued coarse scan followed by a floor-affine schedule
is one common-workspace signed-macro program. -/
private theorem reluApproxVectorBoxScan_then_floorAffine {d m T U : Nat}
    (Rscan : Real) (lower upper : Fin T -> Fin d -> Real)
    (payload : Fin T -> Fin m -> Real)
    (Rfloor : Real) (floorBound : Nat) (base : Real)
    (tail : Fin U -> Fin (reluApproxVectorBoxScanStateSize d m))
    (P : Fin U -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) Real)
    (bias digitCoeff : Fin U ->
      Fin (reluApproxVectorBoxScanStateSize d m) -> Real)
    (x : Fin d -> Real) :
    reluApproxSignedMacroRecursion
        (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
        (reluApproxConcatFeatureSchedule
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (fun k : Fin U =>
            reluApproxFloorAffineFeatureMatrix base floorBound (tail k)))
        (reluApproxConcatFeatureBiasSchedule
          (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper payload)
          (fun _ : Fin U => reluApproxFloorAffineFeatureBias Rfloor floorBound))
        (reluApproxConcatUpdateSchedule
          (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T))
          (fun k : Fin U =>
            reluApproxFloorAffineUpdateMatrix Rfloor floorBound
              (P k) (digitCoeff k)))
        (reluApproxConcatUpdateBiasSchedule
          (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T))
          bias)
        x (T * 2 + U) =
      reluApproxFloorAffineRecursionFrom Rfloor floorBound base tail P bias
        digitCoeff
        (reluApproxVectorBoxScanState x
          (reluApproxVectorBoxScanAccumulator Rscan lower upper payload x T)) U := by
  rw [reluApproxSignedMacroRecursion_concat]
  have hscan := reluApproxVectorBoxScanRecursion_even
    Rscan lower upper payload x T le_rfl
  have hscan' :
      reluApproxSignedMacroRecursion
          (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper payload)
          reluApproxVectorBoxScanUpdateSchedule
          reluApproxVectorBoxScanUpdateBiasSchedule x (T * 2) =
        reluApproxVectorBoxScanState x
          (reluApproxVectorBoxScanAccumulator Rscan lower upper payload x T) := by
    simpa [Nat.mul_comm] using hscan
  rw [hscan']
  exact reluApproxMacroRecursionFrom_floorAffine
    Rfloor floorBound base tail P bias digitCoeff _ U le_rfl

/-- On a safe coarse cell, the first pass of the concatenated program may be
replaced by the selected payload before reasoning about the fine recursion. -/
private theorem reluApproxVectorBoxScan_then_floorAffine_of_unique
    {d m T U : Nat} {Rscan : Real} (hRscan : 0 < Rscan)
    (lower upper : Fin T -> Fin d -> Real)
    (payload : Fin T -> Fin m -> Real)
    (Rfloor : Real) (floorBound : Nat) (base : Real)
    (tail : Fin U -> Fin (reluApproxVectorBoxScanStateSize d m))
    (P : Fin U -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) Real)
    (bias digitCoeff : Fin U ->
      Fin (reluApproxVectorBoxScanStateSize d m) -> Real)
    (x : Fin d -> Real) (active : Fin T)
    (hpayload : forall i : Fin T, forall k : Fin m, |payload i k| <= Rscan)
    (hactive : forall q : Fin d,
      lower active q + Rscan⁻¹ <= x q /\ x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i : Fin T, i ≠ active -> exists q : Fin d,
      x q <= lower i q \/ upper i q <= x q) :
    reluApproxSignedMacroRecursion
        (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
        (reluApproxConcatFeatureSchedule
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (fun k : Fin U =>
            reluApproxFloorAffineFeatureMatrix base floorBound (tail k)))
        (reluApproxConcatFeatureBiasSchedule
          (reluApproxVectorBoxScanFeatureBiasSchedule
            Rscan lower upper payload)
          (fun _ : Fin U =>
            reluApproxFloorAffineFeatureBias Rfloor floorBound))
        (reluApproxConcatUpdateSchedule
          (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T))
          (fun k : Fin U =>
            reluApproxFloorAffineUpdateMatrix Rfloor floorBound
              (P k) (digitCoeff k)))
        (reluApproxConcatUpdateBiasSchedule
          (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T))
          bias)
        x (T * 2 + U) =
      reluApproxFloorAffineRecursionFrom Rfloor floorBound base tail P bias
        digitCoeff (reluApproxVectorBoxScanState x (payload active)) U := by
  rw [reluApproxSignedMacroRecursion_concat]
  have hscan := reluApproxVectorBoxScanRecursion_eq_payload_of_unique
    hRscan lower upper payload x active hpayload hactive hinactive
  have hscan' :
      reluApproxSignedMacroRecursion
          (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (reluApproxVectorBoxScanFeatureBiasSchedule
            Rscan lower upper payload)
          reluApproxVectorBoxScanUpdateSchedule
          reluApproxVectorBoxScanUpdateBiasSchedule x (T * 2) =
        reluApproxVectorBoxScanState x (payload active) := by
    simpa [Nat.mul_comm] using hscan
  rw [hscan']
  exact reluApproxMacroRecursionFrom_floorAffine
    Rfloor floorBound base tail P bias digitCoeff _ U le_rfl

/-- Compile a vector-valued coarse scan followed by a floor-affine state
schedule into one concrete fully connected ReLU network.  The theorem exposes
the terminal mathematical state rather than the concatenated matrix program,
so later paper-machine proofs only have to establish their register invariant. -/
private theorem exists_reluApproxVectorBoxScan_then_floorAffineNet
    {d m T U D W : Nat}
    (Rscan : Real) (lower upper : Fin T -> Fin d -> Real)
    (payload : Fin T -> Fin m -> Real)
    (Rfloor : Real) (floorBound : Nat) (base : Real)
    (tail : Fin U -> Fin (reluApproxVectorBoxScanStateSize d m))
    (P : Fin U -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d m))
      (Fin (reluApproxVectorBoxScanStateSize d m)) Real)
    (bias digitCoeff : Fin U ->
      Fin (reluApproxVectorBoxScanStateSize d m) -> Real)
    (outputWeight : Fin (reluApproxVectorBoxScanStateSize d m) -> Real)
    (outputBias : Real)
    (hdepth : 2 * (T * 2 + U) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d m
      let hscan := reluApproxVectorBoxScanFeatureSize d m
      let hfloor := (s + s) + 2 * floorBound
      (s + s) + (hscan + hfloor) <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall x : Fin d -> Real,
          N.realize x =
            (Finset.univ.sum (fun i => outputWeight i *
              reluApproxFloorAffineRecursionFrom Rfloor floorBound base
                tail P bias digitCoeff
                (reluApproxVectorBoxScanState x
                  (reluApproxVectorBoxScanAccumulator
                    Rscan lower upper payload x T)) U i)) + outputBias := by
  let s := reluApproxVectorBoxScanStateSize d m
  let hscan := reluApproxVectorBoxScanFeatureSize d m
  let hfloor := (s + s) + 2 * floorBound
  let featureMatrix : Fin (T * 2 + U) ->
      Matrix (Fin (hscan + hfloor)) (Fin s) Real :=
    reluApproxConcatFeatureSchedule
      (reluApproxVectorBoxScanFeatureSchedule Rscan)
      (fun k : Fin U =>
        reluApproxFloorAffineFeatureMatrix base floorBound (tail k))
  let featureBias : Fin (T * 2 + U) -> Fin (hscan + hfloor) -> Real :=
    reluApproxConcatFeatureBiasSchedule
      (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper payload)
      (fun _ : Fin U => reluApproxFloorAffineFeatureBias Rfloor floorBound)
  let updateMatrix : Fin (T * 2 + U) ->
      Matrix (Fin s) (Fin (hscan + hfloor)) Real :=
    reluApproxConcatUpdateSchedule
      (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T))
      (fun k : Fin U =>
        reluApproxFloorAffineUpdateMatrix Rfloor floorBound
          (P k) (digitCoeff k))
  let updateBias : Fin (T * 2 + U) -> Fin s -> Real :=
    reluApproxConcatUpdateBiasSchedule
      (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T))
      bias
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxSignedMacroRecursionNet_exactDepth
      (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
      featureMatrix featureBias updateMatrix updateBias outputWeight outputBias
      hdepth hwidth
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x
  rw [hNrealize]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  exact congrFun
    (reluApproxVectorBoxScan_then_floorAffine
      Rscan lower upper payload Rfloor floorBound base tail P bias digitCoeff x) i

/-! ## Structured finite-state programs

The state machine has several semantically different register families.  The
following interface lets those registers be indexed by an arbitrary finite
type, then reindexes the complete program to `Fin` for the signed-macro
compiler.  This keeps the mathematical state invariant independent of manual
numeric register offsets.
-/

/-- Affine map between arbitrary finite real register families. -/
private noncomputable def reluApproxTypedAffineMap {I J : Type*}
    [Fintype I] [Fintype J]
    (A : J -> I -> Real) (b : J -> Real) (u : I -> Real) : J -> Real :=
  fun j => (Finset.univ.sum fun i => A j i * u i) + b j

/-- Mathematical recursion for a typed two-layer ReLU macro program. -/
private noncomputable def reluApproxTypedMacroRecursion {d T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (input : S -> Fin d -> Real) (inputBias : S -> Real)
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (x : Fin d -> Real) : Nat -> S -> Real
  | 0 => reluApproxTypedAffineMap input inputBias x
  | t + 1 =>
      if ht : t < T then
        reluApproxTypedAffineMap (update ⟨t, ht⟩) (updateBias ⟨t, ht⟩)
          (fun j => relu (reluApproxTypedAffineMap (feature ⟨t, ht⟩)
            (featureBias ⟨t, ht⟩)
            (reluApproxTypedMacroRecursion input inputBias feature
              featureBias update updateBias x t) j))
      else
        reluApproxTypedMacroRecursion input inputBias feature featureBias
          update updateBias x t

/-- Typed macro recursion from an arbitrary already-loaded state. -/
private noncomputable def reluApproxTypedMacroRecursionFrom {T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (u0 : S -> Real) : Nat -> S -> Real
  | 0 => u0
  | t + 1 =>
      if ht : t < T then
        reluApproxTypedAffineMap (update ⟨t, ht⟩) (updateBias ⟨t, ht⟩)
          (fun j => relu (reluApproxTypedAffineMap (feature ⟨t, ht⟩)
            (featureBias ⟨t, ht⟩)
            (reluApproxTypedMacroRecursionFrom feature featureBias update
              updateBias u0 t) j))
      else
        reluApproxTypedMacroRecursionFrom feature featureBias update
          updateBias u0 t

/-- Reindex a typed input matrix by the canonical finite equivalence. -/
private noncomputable def reluApproxTypedInputMatrix {d : Nat}
    {S : Type*} [Fintype S] (input : S -> Fin d -> Real) :
    Matrix (Fin (Fintype.card S)) (Fin d) Real :=
  fun i q => input ((Fintype.equivFin S).symm i) q

/-- Reindex a typed input bias by the canonical finite equivalence. -/
private noncomputable def reluApproxTypedInputBias {S : Type*} [Fintype S]
    (b : S -> Real) : Fin (Fintype.card S) -> Real :=
  fun i => b ((Fintype.equivFin S).symm i)

/-- Reindex the feature matrix of a typed macro schedule. -/
private noncomputable def reluApproxTypedFeatureMatrix {T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (feature : Fin T -> H -> S -> Real) :
    Fin T -> Matrix (Fin (Fintype.card H)) (Fin (Fintype.card S)) Real :=
  fun t i j => feature t ((Fintype.equivFin H).symm i)
    ((Fintype.equivFin S).symm j)

/-- Reindex the feature bias of a typed macro schedule. -/
private noncomputable def reluApproxTypedFeatureBias {T : Nat}
    {H : Type*} [Fintype H] (b : Fin T -> H -> Real) :
    Fin T -> Fin (Fintype.card H) -> Real :=
  fun t i => b t ((Fintype.equivFin H).symm i)

/-- Reindex the update matrix of a typed macro schedule. -/
private noncomputable def reluApproxTypedUpdateMatrix {T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (update : Fin T -> S -> H -> Real) :
    Fin T -> Matrix (Fin (Fintype.card S)) (Fin (Fintype.card H)) Real :=
  fun t i j => update t ((Fintype.equivFin S).symm i)
    ((Fintype.equivFin H).symm j)

/-- Reindex the update bias of a typed macro schedule. -/
private noncomputable def reluApproxTypedUpdateBias {T : Nat}
    {S : Type*} [Fintype S] (b : Fin T -> S -> Real) :
    Fin T -> Fin (Fintype.card S) -> Real :=
  fun t i => b t ((Fintype.equivFin S).symm i)

/-- Reindexing preserves every state of a typed macro recursion exactly. -/
private theorem reluApproxTypedMacroRecursion_reindex {d T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (input : S -> Fin d -> Real) (inputBias : S -> Real)
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (x : Fin d -> Real) (t : Nat) (ht : t <= T) :
    (fun i => reluApproxSignedMacroRecursion
      (reluApproxTypedInputMatrix input) (reluApproxTypedInputBias inputBias)
      (reluApproxTypedFeatureMatrix feature)
      (reluApproxTypedFeatureBias featureBias)
      (reluApproxTypedUpdateMatrix update)
      (reluApproxTypedUpdateBias updateBias) x t (Fintype.equivFin S i)) =
      reluApproxTypedMacroRecursion input inputBias feature featureBias update
        updateBias x t := by
  induction t with
  | zero =>
      funext i
      simp [reluApproxSignedMacroRecursion, reluApproxFiniteAffineMap,
        reluApproxTypedMacroRecursion, reluApproxTypedAffineMap,
        reluApproxTypedInputMatrix, reluApproxTypedInputBias]
  | succ t ih =>
      funext i
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxSignedMacroRecursion, reluApproxTypedMacroRecursion]
      simp only [dif_pos htlt]
      simp only [reluApproxFiniteAffineMap, reluApproxTypedAffineMap,
        reluApproxTypedUpdateMatrix, reluApproxTypedUpdateBias,
        reluApproxTypedFeatureMatrix, reluApproxTypedFeatureBias,
        Equiv.symm_apply_apply]
      rw [← Equiv.sum_comp (Fintype.equivFin H)]
      apply congrArg (fun z : Real => z + updateBias ⟨t, htlt⟩ i)
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [Equiv.symm_apply_apply]
      congr 1
      congr 1
      rw [← Equiv.sum_comp (Fintype.equivFin S)]
      apply congrArg (fun z : Real => z + featureBias ⟨t, htlt⟩ j)
      apply Finset.sum_congr rfl
      intro k _hk
      rw [congrFun (ih (Nat.le_of_succ_le ht)) k]
      simp

/-- Reindexing also preserves typed macro recursion from an arbitrary state. -/
private theorem reluApproxTypedMacroRecursionFrom_reindex {T : Nat}
    {S H : Type*} [Fintype S] [Fintype H]
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (u0 : S -> Real) (t : Nat) (ht : t <= T) :
    (fun i => reluApproxMacroRecursionFrom
      (reluApproxTypedFeatureMatrix feature)
      (reluApproxTypedFeatureBias featureBias)
      (reluApproxTypedUpdateMatrix update)
      (reluApproxTypedUpdateBias updateBias)
      (fun j => u0 ((Fintype.equivFin S).symm j)) t
      (Fintype.equivFin S i)) =
      reluApproxTypedMacroRecursionFrom feature featureBias update updateBias
        u0 t := by
  induction t with
  | zero =>
      funext i
      simp [reluApproxMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom]
  | succ t ih =>
      funext i
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom]
      simp only [dif_pos htlt, reluApproxFiniteAffineMap,
        reluApproxTypedAffineMap, reluApproxTypedUpdateMatrix,
        reluApproxTypedUpdateBias, reluApproxTypedFeatureMatrix,
        reluApproxTypedFeatureBias, Equiv.symm_apply_apply]
      rw [← Equiv.sum_comp (Fintype.equivFin H)]
      apply congrArg (fun z : Real => z + updateBias ⟨t, htlt⟩ i)
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [Equiv.symm_apply_apply]
      congr 1
      congr 1
      rw [← Equiv.sum_comp (Fintype.equivFin S)]
      apply congrArg (fun z : Real => z + featureBias ⟨t, htlt⟩ j)
      apply Finset.sum_congr rfl
      intro k _hk
      rw [congrFun (ih (Nat.le_of_succ_le ht)) k]
      simp

/-- Compile a typed finite-state macro program and pad it to exact requested
depth and width. -/
private theorem exists_reluApproxTypedMacroRecursionNet_exactDepth
    {d T D W : Nat} {S H : Type*} [Fintype S] [Fintype H]
    (input : S -> Fin d -> Real) (inputBias : S -> Real)
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (outputWeight : S -> Real) (outputBias : Real)
    (hdepth : 2 * T + 1 <= D)
    (hwidth : (Fintype.card S + Fintype.card S) + Fintype.card H <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
      N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
      forall x : Fin d -> Real,
        N.realize x =
          (Finset.univ.sum fun i : S => outputWeight i *
            reluApproxTypedMacroRecursion input inputBias feature featureBias
              update updateBias x T i) + outputBias := by
  let outputWeightFin : Fin (Fintype.card S) -> Real :=
    fun i => outputWeight ((Fintype.equivFin S).symm i)
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxSignedMacroRecursionNet_exactDepth
      (reluApproxTypedInputMatrix input) (reluApproxTypedInputBias inputBias)
      (reluApproxTypedFeatureMatrix feature)
      (reluApproxTypedFeatureBias featureBias)
      (reluApproxTypedUpdateMatrix update)
      (reluApproxTypedUpdateBias updateBias)
      outputWeightFin outputBias hdepth hwidth
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x
  rw [hNrealize]
  apply congrArg (fun z : Real => z + outputBias)
  rw [← Equiv.sum_comp (Fintype.equivFin S)]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [outputWeightFin, Equiv.symm_apply_apply]
  rw [congrFun (reluApproxTypedMacroRecursion_reindex input inputBias feature
    featureBias update updateBias x T le_rfl) i]

/-! ## Typed floor-decoder schedules -/

/-- One typed affine transition driven by a prescribed natural digit. -/
private noncomputable def reluApproxTypedFloorAffineDigitState {S : Type*}
    [Fintype S] (P : S -> S -> Real) (bias digitCoeff : S -> Real)
    (digit : Nat) (u : S -> Real) : S -> Real :=
  fun i => reluApproxTypedAffineMap P bias u i + digitCoeff i * (digit : Real)

/-- Typed prescribed-digit recursion, saturated after its finite schedule. -/
private noncomputable def reluApproxTypedFloorAffineDigitRecursionFrom
    {S : Type*} [Fintype S] {T : Nat}
    (P : Fin T -> S -> S -> Real)
    (bias digitCoeff : Fin T -> S -> Real)
    (digit : Fin T -> Nat) (u0 : S -> Real) : Nat -> S -> Real
  | 0 => u0
  | t + 1 =>
      if ht : t < T then
        reluApproxTypedFloorAffineDigitState (P ⟨t, ht⟩)
          (bias ⟨t, ht⟩) (digitCoeff ⟨t, ht⟩) (digit ⟨t, ht⟩)
          (reluApproxTypedFloorAffineDigitRecursionFrom
            P bias digitCoeff digit u0 t)
      else
        reluApproxTypedFloorAffineDigitRecursionFrom
          P bias digitCoeff digit u0 t

/-- Reindexing a prescribed-digit affine recursion to `Fin` preserves every
typed register exactly. -/
private theorem reluApproxTypedFloorAffineDigitRecursionFrom_reindex
    {S : Type*} [Fintype S] {T : Nat}
    (P : Fin T -> S -> S -> Real)
    (bias digitCoeff : Fin T -> S -> Real)
    (digit : Fin T -> Nat) (u0 : S -> Real)
    (t : Nat) (ht : t <= T) :
    (fun i => reluApproxFloorAffineDigitRecursionFrom
      (reluApproxTypedUpdateMatrix P)
      (reluApproxTypedUpdateBias bias)
      (reluApproxTypedUpdateBias digitCoeff) digit
      (fun j => u0 ((Fintype.equivFin S).symm j)) t
      (Fintype.equivFin S i)) =
      reluApproxTypedFloorAffineDigitRecursionFrom
        P bias digitCoeff digit u0 t := by
  induction t with
  | zero =>
      funext i
      simp [reluApproxFloorAffineDigitRecursionFrom,
        reluApproxTypedFloorAffineDigitRecursionFrom]
  | succ t ih =>
      funext i
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxFloorAffineDigitRecursionFrom,
        reluApproxTypedFloorAffineDigitRecursionFrom]
      simp only [dif_pos htlt, reluApproxFloorAffineDigitState,
        reluApproxTypedFloorAffineDigitState, reluApproxFiniteAffineMap,
        reluApproxTypedAffineMap, reluApproxTypedUpdateMatrix,
        reluApproxTypedUpdateBias, Equiv.symm_apply_apply]
      rw [← Equiv.sum_comp (Fintype.equivFin S)]
      apply congrArg (fun z : Real =>
        z + bias ⟨t, htlt⟩ i + digitCoeff ⟨t, htlt⟩ i * (digit ⟨t, htlt⟩ : Real))
      apply Finset.sum_congr rfl
      intro j _hj
      rw [congrFun (ih (Nat.le_of_succ_le ht)) j]
      simp

/-- A positive typed base-tail certificate identifies the concrete floor-macro
recursion with its prescribed-digit recursion. -/
private theorem reluApproxTypedFloorAffineRecursion_eq_digit_of_digitBaseTail
    {S : Type*} [Fintype S] {T : Nat}
    (dExp : Real) (c : Nat) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (tailLength : Fin T -> Nat)
    (hTailLength : forall k : Fin T, 1 <= tailLength k)
    (hRsep : forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-(tailLength k : Int)))
    (stateTail : Fin T -> S)
    (P : Fin T -> S -> S -> Real)
    (bias digitCoeff : Fin T -> S -> Real)
    (digit : Fin T -> Nat)
    (tailDigit : forall k : Fin T, Fin (tailLength k) -> Nat)
    (hDigitLower : forall k : Fin T, 1 <= digit k)
    (hDigitUpper : forall k : Fin T, digit k <= 2 * c + 3)
    (hTailLower : forall k : Fin T, forall j : Fin (tailLength k),
      1 <= tailDigit k j)
    (hTailUpper : forall k : Fin T, forall j : Fin (tailLength k),
      tailDigit k j <= 2 * c + 3)
    (u0 : S -> Real)
    (hcode : forall k : Fin T,
      (baseNat : Real) *
          reluApproxTypedFloorAffineDigitRecursionFrom
            P bias digitCoeff digit u0 k.val (stateTail k) =
        (digit k : Real) + Finset.univ.sum (fun j : Fin (tailLength k) =>
          (tailDigit k j : Real) / (baseNat : Real) ^ (j.val + 1)))
    (t : Nat) (ht : t <= T) :
    (fun i => reluApproxFloorAffineRecursionFrom R floorBound
      (baseNat : Real) (fun k => Fintype.equivFin S (stateTail k))
      (reluApproxTypedUpdateMatrix P)
      (reluApproxTypedUpdateBias bias)
      (reluApproxTypedUpdateBias digitCoeff)
      (fun j => u0 ((Fintype.equivFin S).symm j)) t
      (Fintype.equivFin S i)) =
      reluApproxTypedFloorAffineDigitRecursionFrom
        P bias digitCoeff digit u0 t := by
  have hcodeFin : forall k : Fin T,
      (baseNat : Real) *
          reluApproxFloorAffineDigitRecursionFrom
            (reluApproxTypedUpdateMatrix P)
            (reluApproxTypedUpdateBias bias)
            (reluApproxTypedUpdateBias digitCoeff) digit
            (fun j => u0 ((Fintype.equivFin S).symm j)) k.val
            (Fintype.equivFin S (stateTail k)) =
        (digit k : Real) + Finset.univ.sum (fun j : Fin (tailLength k) =>
          (tailDigit k j : Real) / (baseNat : Real) ^ (j.val + 1)) := by
    intro k
    rw [congrFun
      (reluApproxTypedFloorAffineDigitRecursionFrom_reindex
        P bias digitCoeff digit u0 k.val k.isLt.le) (stateTail k)]
    exact hcode k
  have hfin := reluApproxFloorAffineRecursionFrom_eq_digit_of_digitBaseTail
    dExp c hc baseNat hbase floorBound hFloorBound R hR
    tailLength hTailLength hRsep
    (fun k => Fintype.equivFin S (stateTail k))
    (reluApproxTypedUpdateMatrix P)
    (reluApproxTypedUpdateBias bias)
    (reluApproxTypedUpdateBias digitCoeff) digit tailDigit
    hDigitLower hDigitUpper hTailLower hTailUpper
    (fun j => u0 ((Fintype.equivFin S).symm j)) hcodeFin t ht
  funext i
  rw [congrFun hfin (Fintype.equivFin S i)]
  exact congrFun
    (reluApproxTypedFloorAffineDigitRecursionFrom_reindex
      P bias digitCoeff digit u0 t ht) i

/-! ## Parallel Taylor-tail decoder

There are finitely many Taylor multiindices, depending only on `d` and `r`.
Consequently all their correction tails can be decoded in parallel at fixed
width.  One macro step below preserves the signed state channels, runs one
copy of the truncated-floor feature bank for every tail, and applies an
arbitrary affine transition driven by all decoded digits.
-/

/-- Feature indices for a parallel floor bank: positive and negative copies
of every state register, followed by one floor network per code tail. -/
private abbrev ReLUApproxParallelFloorFeature (S A : Type*) (B : Nat) :=
  (S ⊕ S) ⊕ (A × Fin (2 * B))

/-- Typed feature matrix for a parallel family of truncated-floor decoders. -/
private noncomputable def reluApproxParallelFloorFeatureMatrix {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (base : Real) (B : Nat) (tail : A -> S) :
    ReLUApproxParallelFloorFeature S A B -> S -> Real
  | Sum.inl (Sum.inl j), i => if i = j then 1 else 0
  | Sum.inl (Sum.inr j), i => if i = j then -1 else 0
  | Sum.inr (a, _k), i => if i = tail a then base else 0

/-- Biases for the signed-state channels and every parallel floor bank. -/
private noncomputable def reluApproxParallelFloorFeatureBias {S A : Type*}
    [Fintype S] [Fintype A] (R : Real) (B : Nat) :
    ReLUApproxParallelFloorFeature S A B -> Real
  | Sum.inl _ => 0
  | Sum.inr (_a, k) =>
      (reluApproxTruncatedFloorNet R B).input.bias k

/-- Update matrix combining an affine state map with all decoded digits. -/
private noncomputable def reluApproxParallelFloorUpdateMatrix {S A : Type*}
    [Fintype S] [Fintype A]
    (R : Real) (B : Nat) (P : S -> S -> Real)
    (digitCoeff : S -> A -> Real) :
    S -> ReLUApproxParallelFloorFeature S A B -> Real
  | i, Sum.inl (Sum.inl j) => P i j
  | i, Sum.inl (Sum.inr j) => -P i j
  | i, Sum.inr (a, k) =>
      digitCoeff i a * (reluApproxTruncatedFloorNet R B).outputWeight k

private theorem reluApproxParallelFloorFeature_pos {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (base R : Real) (B : Nat) (tail : A -> S) (u : S -> Real) (j : S) :
    reluApproxTypedAffineMap
      (reluApproxParallelFloorFeatureMatrix base B tail)
      (reluApproxParallelFloorFeatureBias (S := S) (A := A) R B) u
      (Sum.inl (Sum.inl j)) = u j := by
  simp [reluApproxTypedAffineMap, reluApproxParallelFloorFeatureMatrix,
    reluApproxParallelFloorFeatureBias]

private theorem reluApproxParallelFloorFeature_neg {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (base R : Real) (B : Nat) (tail : A -> S) (u : S -> Real) (j : S) :
    reluApproxTypedAffineMap
      (reluApproxParallelFloorFeatureMatrix base B tail)
      (reluApproxParallelFloorFeatureBias (S := S) (A := A) R B) u
      (Sum.inl (Sum.inr j)) = -u j := by
  simp [reluApproxTypedAffineMap, reluApproxParallelFloorFeatureMatrix,
    reluApproxParallelFloorFeatureBias]

private theorem reluApproxParallelFloorFeature_decoder {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (base R : Real) (B : Nat) (tail : A -> S) (u : S -> Real)
    (a : A) (k : Fin (2 * B)) :
    reluApproxTypedAffineMap
      (reluApproxParallelFloorFeatureMatrix base B tail)
      (reluApproxParallelFloorFeatureBias (S := S) (A := A) R B) u
      (Sum.inr (a, k)) =
      base * u (tail a) +
        (reluApproxTruncatedFloorNet R B).input.bias k := by
  simp [reluApproxTypedAffineMap, reluApproxParallelFloorFeatureMatrix,
    reluApproxParallelFloorFeatureBias]

/-- Mathematical state update produced by all concrete floor decoders. -/
private noncomputable def reluApproxParallelFloorState {S A : Type*}
    [Fintype S] [Fintype A]
    (R : Real) (B : Nat) (base : Real) (tail : A -> S)
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (u : S -> Real) : S -> Real :=
  fun i => reluApproxTypedAffineMap P bias u i +
    Finset.univ.sum (fun a : A => digitCoeff i a *
      truncatedFloorReLUFunction R B (base * u (tail a)))

/-- One parallel floor bank is represented exactly by one typed ReLU macro. -/
private theorem reluApproxParallelFloorMacro_exact {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (R : Real) (B : Nat) (base : Real) (tail : A -> S)
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (u : S -> Real) :
    reluApproxTypedAffineMap
      (reluApproxParallelFloorUpdateMatrix R B P digitCoeff) bias
      (fun z => relu (reluApproxTypedAffineMap
        (reluApproxParallelFloorFeatureMatrix base B tail)
        (reluApproxParallelFloorFeatureBias (S := S) (A := A) R B) u z)) =
      reluApproxParallelFloorState R B base tail P bias digitCoeff u := by
  have hdecode : forall a : A,
      (Finset.univ.sum fun k : Fin (2 * B) =>
        (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu (base * u (tail a) +
            (reluApproxTruncatedFloorNet R B).input.bias k)) =
        truncatedFloorReLUFunction R B (base * u (tail a)) := by
    intro a
    have hfloor := reluApproxTruncatedFloorNet_realize R B
      (fun _ : Fin 1 => base * u (tail a))
    simpa [reluApproxTruncatedFloorNet, FullyConnectedReLUNet.realize,
      FullyConnectedReLUNet.hiddenState, DenseLayer.reluApply, reluVec,
      DenseLayer.apply] using hfloor
  funext i
  change ((Finset.univ.sum fun z : ReLUApproxParallelFloorFeature S A B =>
      reluApproxParallelFloorUpdateMatrix R B P digitCoeff i z *
        relu (reluApproxTypedAffineMap
          (reluApproxParallelFloorFeatureMatrix base B tail)
          (reluApproxParallelFloorFeatureBias (S := S) (A := A) R B) u z)) +
        bias i) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [reluApproxParallelFloorUpdateMatrix]
  simp_rw [reluApproxParallelFloorFeature_pos,
    reluApproxParallelFloorFeature_neg,
    reluApproxParallelFloorFeature_decoder]
  simp only [reluApproxParallelFloorState, reluApproxTypedAffineMap]
  have hstate :
      (Finset.univ.sum fun j : S => P i j * relu (u j)) +
          (Finset.univ.sum fun j : S => -P i j * relu (-u j)) =
        Finset.univ.sum fun j : S => P i j * u j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    calc
      P i j * relu (u j) + -P i j * relu (-u j) =
          P i j * (relu (u j) - relu (-u j)) := by ring
      _ = P i j * u j := by rw [reluApproxSignedEncode_sub]
  rw [hstate]
  have hdecoderSum :
      (Finset.univ.sum fun a : A => Finset.univ.sum fun k : Fin (2 * B) =>
        digitCoeff i a * (reluApproxTruncatedFloorNet R B).outputWeight k *
          relu (base * u (tail a) +
            (reluApproxTruncatedFloorNet R B).input.bias k)) =
        Finset.univ.sum (fun a : A => digitCoeff i a *
          truncatedFloorReLUFunction R B (base * u (tail a))) := by
    apply Finset.sum_congr rfl
    intro a _ha
    calc
      (Finset.univ.sum fun k : Fin (2 * B) =>
          digitCoeff i a * (reluApproxTruncatedFloorNet R B).outputWeight k *
            relu (base * u (tail a) +
              (reluApproxTruncatedFloorNet R B).input.bias k)) =
          digitCoeff i a * (Finset.univ.sum fun k : Fin (2 * B) =>
            (reluApproxTruncatedFloorNet R B).outputWeight k *
              relu (base * u (tail a) +
                (reluApproxTruncatedFloorNet R B).input.bias k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = digitCoeff i a *
          truncatedFloorReLUFunction R B (base * u (tail a)) := by
        rw [hdecode a]
  rw [hdecoderSum]
  ring

/-- Parallel affine state transition driven by a prescribed digit vector. -/
private noncomputable def reluApproxParallelFloorDigitState {S A : Type*}
    [Fintype S] [Fintype A]
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (digit : A -> Nat)
    (u : S -> Real) : S -> Real :=
  fun i => reluApproxTypedAffineMap P bias u i +
    Finset.univ.sum (fun a : A => digitCoeff i a * (digit a : Real))

/-- Prescribed-vector-digit recursion for a parallel floor schedule. -/
private noncomputable def reluApproxParallelFloorDigitRecursionFrom
    {S A : Type*} [Fintype S] [Fintype A] {T : Nat}
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real)
    (digit : Fin T -> A -> Nat) (u0 : S -> Real) : Nat -> S -> Real
  | 0 => u0
  | t + 1 =>
      if ht : t < T then
        reluApproxParallelFloorDigitState (P ⟨t, ht⟩) (bias ⟨t, ht⟩)
          (digitCoeff ⟨t, ht⟩) (digit ⟨t, ht⟩)
          (reluApproxParallelFloorDigitRecursionFrom
            P bias digitCoeff digit u0 t)
      else
        reluApproxParallelFloorDigitRecursionFrom
          P bias digitCoeff digit u0 t

/-- Concrete typed macro recursion for a parallel floor schedule. -/
private noncomputable def reluApproxParallelFloorMacroRecursionFrom
    {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {T : Nat}
    (R : Real) (B : Nat) (base : Real) (tail : Fin T -> A -> S)
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real) (u0 : S -> Real) :
    Nat -> S -> Real :=
  reluApproxTypedMacroRecursionFrom
    (fun t => reluApproxParallelFloorFeatureMatrix base B (tail t))
    (fun _ => reluApproxParallelFloorFeatureBias (S := S) (A := A) R B)
    (fun t => reluApproxParallelFloorUpdateMatrix R B (P t) (digitCoeff t))
    bias u0

/-- Under a positive base-tail certificate for every Taylor register, the
concrete parallel floor recursion equals its prescribed-vector-digit recursion
at every scheduled time. -/
private theorem reluApproxParallelFloorMacroRecursionFrom_eq_digit_of_baseTail
    {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    {T : Nat}
    (dExp : Real) (c : Nat) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (tailLength : Fin T -> A -> Nat)
    (hTailLength : forall k a, 1 <= tailLength k a)
    (hRsep : forall k a,
      1 / R < (baseNat : Real) ^ (-(tailLength k a : Int)))
    (stateTail : Fin T -> A -> S)
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real)
    (digit : Fin T -> A -> Nat)
    (tailDigit : forall k a, Fin (tailLength k a) -> Nat)
    (hDigitLower : forall k a, 1 <= digit k a)
    (hDigitUpper : forall k a, digit k a <= 2 * c + 3)
    (hTailLower : forall k a j, 1 <= tailDigit k a j)
    (hTailUpper : forall k a j, tailDigit k a j <= 2 * c + 3)
    (u0 : S -> Real)
    (hcode : forall k a,
      (baseNat : Real) *
          reluApproxParallelFloorDigitRecursionFrom
            P bias digitCoeff digit u0 k.val (stateTail k a) =
        (digit k a : Real) + Finset.univ.sum
          (fun j : Fin (tailLength k a) =>
            (tailDigit k a j : Real) / (baseNat : Real) ^ (j.val + 1)))
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorMacroRecursionFrom R floorBound
        (baseNat : Real) stateTail P bias digitCoeff u0 t =
      reluApproxParallelFloorDigitRecursionFrom
        P bias digitCoeff digit u0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      let k : Fin T := ⟨t, htlt⟩
      have hfloor : forall a : A,
          truncatedFloorReLUFunction R floorBound
              ((baseNat : Real) *
                reluApproxParallelFloorDigitRecursionFrom
                  P bias digitCoeff digit u0 t (stateTail k a)) =
            (digit k a : Real) := by
        intro a
        let signedDigit : Int := (digit k a : Int) - (c + 2 : Int)
        have hshift :
            (digit k a : Int) = signedDigit + (c + 2 : Int) := by
          dsimp [signedDigit]
          ring
        rcases reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
            dExp c hc baseNat hbase (digit k a) signedDigit hshift
            (hDigitLower k a) (hDigitUpper k a)
            (tailLength k a) (hTailLength k a)
            (tailDigit k a) (hTailLower k a) (hTailUpper k a)
            ((baseNat : Real) *
              reluApproxParallelFloorDigitRecursionFrom
                P bias digitCoeff digit u0 t (stateTail k a))
            (hcode k a) floorBound hFloorBound R hR (hRsep k a) with
          ⟨_hgap, _hclass, htruncated, hfloorNat, _hsigned⟩
        rw [htruncated, hfloorNat]
      have iht :
          reluApproxTypedMacroRecursionFrom
              (fun t => reluApproxParallelFloorFeatureMatrix
                (baseNat : Real) floorBound (stateTail t))
              (fun _ => reluApproxParallelFloorFeatureBias
                (S := S) (A := A) R floorBound)
              (fun t => reluApproxParallelFloorUpdateMatrix
                R floorBound (P t) (digitCoeff t))
              bias u0 t =
            reluApproxParallelFloorDigitRecursionFrom
              P bias digitCoeff digit u0 t := by
        simpa [reluApproxParallelFloorMacroRecursionFrom] using
          ih (Nat.le_of_succ_le ht)
      rw [reluApproxParallelFloorMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom,
        reluApproxParallelFloorDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [iht]
      rw [reluApproxParallelFloorMacro_exact]
      funext i
      simp only [reluApproxParallelFloorState,
        reluApproxParallelFloorDigitState]
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [hfloor a]

/-- Registers used by the fine-grid Taylor recursion. The four summands store
the input, the current center, the Taylor coefficients, and their code tails. -/
private abbrev ReLUApproxTaylorMachineRegister (d r : Nat) :=
  (Fin d ⊕ Fin d) ⊕ (TaylorMultiindex r d ⊕ TaylorMultiindex r d)

private noncomputable def reluApproxTaylorMachineState {d r : Nat}
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorMachineRegister d r -> Real
  | .inl (.inl q) => x q
  | .inl (.inr q) => center q
  | .inr (.inl a) => coefficient a
  | .inr (.inr a) => tail a

private noncomputable def reluApproxTaylorMachineMatrix {d r : Nat}
    (base : Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorMachineRegister d r ->
      ReLUApproxTaylorMachineRegister d r -> Real
  | .inl (.inl q), .inl (.inl u) => if u = q then 1 else 0
  | .inl (.inr q), .inl (.inr u) => if u = q then 1 else 0
  | .inr (.inl a), .inr (.inl b) => trans a b
  | .inr (.inr a), .inr (.inr b) => if b = a then base else 0
  | _, _ => 0

private noncomputable def reluApproxTaylorMachineBias {d r : Nat}
    (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorMachineRegister d r -> Real
  | .inl (.inr q) => step q
  | .inr (.inl a) => -(shift : Real) * scale a
  | _ => 0

private noncomputable def reluApproxTaylorMachineDigitCoeff {d r : Nat}
    (scale : TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorMachineRegister d r -> TaylorMultiindex r d -> Real
  | .inr (.inl a), b => if b = a then scale a else 0
  | .inr (.inr a), b => if b = a then -1 else 0
  | _, _ => 0

set_option maxHeartbeats 1000000 in
/-- One parallel decoded digit step performs exactly the intended Taylor-state
update. This is the algebraic interface between the code decoder and the
analytic Taylor recursion. -/
private theorem reluApproxTaylorMachineDigitState_exact {d r : Nat}
    (base : Real) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : TaylorMultiindex r d -> Nat)
    (correction : TaylorMultiindex r d -> Int)
    (hdigit : forall a, (digit a : Int) = correction a + (shift : Int))
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    reluApproxParallelFloorDigitState
      (reluApproxTaylorMachineMatrix base trans)
      (reluApproxTaylorMachineBias step shift scale)
      (reluApproxTaylorMachineDigitCoeff scale) digit
      (reluApproxTaylorMachineState x center coefficient tail) =
    reluApproxTaylorMachineState x (fun q => center q + step q)
      (fun a => Finset.univ.sum (fun b => trans a b * coefficient b) +
        (correction a : Real) * scale a)
      (fun a => base * tail a - (digit a : Real)) := by
  funext z
  rcases z with (⟨q | q⟩ | ⟨a | a⟩)
  · simp [reluApproxParallelFloorDigitState, reluApproxTypedAffineMap,
      reluApproxTaylorMachineMatrix, reluApproxTaylorMachineBias,
      reluApproxTaylorMachineDigitCoeff, reluApproxTaylorMachineState,
      Fintype.sum_sum_type]
  · simp [reluApproxParallelFloorDigitState, reluApproxTypedAffineMap,
      reluApproxTaylorMachineMatrix, reluApproxTaylorMachineBias,
      reluApproxTaylorMachineDigitCoeff, reluApproxTaylorMachineState,
      Fintype.sum_sum_type]
  · have hcast : (digit a : Real) =
        (correction a : Real) + (shift : Real) := by
      exact_mod_cast hdigit a
    simp [reluApproxParallelFloorDigitState, reluApproxTypedAffineMap,
      reluApproxTaylorMachineMatrix, reluApproxTaylorMachineBias,
      reluApproxTaylorMachineDigitCoeff, reluApproxTaylorMachineState,
      Fintype.sum_sum_type, hcast]
    ring
  · simp [reluApproxParallelFloorDigitState, reluApproxTypedAffineMap,
      reluApproxTaylorMachineMatrix, reluApproxTaylorMachineBias,
      reluApproxTaylorMachineDigitCoeff, reluApproxTaylorMachineState,
      Fintype.sum_sum_type]
    ring

/-- Centers generated by the prescribed fine-grid step schedule. -/
noncomputable def reluApproxTaylorCenterRecursion {d T : Nat}
    (step : Fin T -> Fin d -> Real) (center0 : Fin d -> Real) :
    Nat -> Fin d -> Real
  | 0 => center0
  | k + 1 => if hk : k < T then
      fun q => reluApproxTaylorCenterRecursion step center0 k q + step ⟨k, hk⟩ q
    else reluApproxTaylorCenterRecursion step center0 k

/-- Taylor coefficients generated by affine transport and prescribed signed
corrections. -/
noncomputable def reluApproxTaylorCoefficientRecursion
    {r d T : Nat}
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (coefficient0 : TaylorMultiindex r d -> Real) :
    Nat -> TaylorMultiindex r d -> Real
  | 0 => coefficient0
  | k + 1 => if hk : k < T then fun a =>
      Finset.univ.sum (fun b => trans ⟨k, hk⟩ a b *
        reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 k b) +
      (correction ⟨k, hk⟩ a : Real) * scale a
    else reluApproxTaylorCoefficientRecursion
      scale trans correction coefficient0 k

/-- With identity transport, zero correction and zero correction scale, the
constant-one Taylor state is preserved at every time.  This is the zero-code
instance used by the hierarchical boundary checker. -/
private theorem reluApproxTaylorCoefficientRecursion_identity_one
    {r d T : Nat} (n : Nat) :
    reluApproxTaylorCoefficientRecursion (r := r) (d := d) (T := T)
        (fun _ => 0) (fun _ a b => if b = a then 1 else 0)
        (fun _ _ => 0) (fun _ => 1) n = fun _ => 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reluApproxTaylorCoefficientRecursion]
      split_ifs
      · funext a
        simp [ih]
      · exact ih

/-- The finite Taylor-center machine follows any path whose consecutive
differences are the scheduled steps. -/
theorem reluApproxTaylorCenterRecursion_eq_path
    {d T : Nat}
    (step : Fin T -> Fin d -> Real) (center0 : Fin d -> Real)
    (path : Nat -> Fin d -> Real)
    (hcenter0 : center0 = path 0)
    (hmove : forall k : Nat, forall hk : k < T,
      path (k + 1) - path k = step ⟨k, hk⟩) :
    forall t : Nat, t <= T ->
      reluApproxTaylorCenterRecursion step center0 t = path t := by
  intro t ht
  induction t with
  | zero =>
      simpa [reluApproxTaylorCenterRecursion] using hcenter0
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxTaylorCenterRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      funext q
      have hq := congrFun (hmove t htlt) q
      change path (t + 1) q - path t q = step ⟨t, htlt⟩ q at hq
      linarith

/-- The prescribed finite correction recursion is the canonical corrected
affine recursion whenever it uses the canonical correction digits. -/
theorem reluApproxTaylorCoefficientRecursion_eq_canonical
    {r d T : Nat}
    (scale : TaylorMultiindex r d -> Real)
    (theta : Nat -> TaylorMultiindex r d -> Real)
    (trans : Nat -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (coefficient0 : TaylorMultiindex r d -> Real)
    (hcoefficient0 :
      coefficient0 = reluApproxCorrectedAffineRecursion scale theta trans 0)
    (hcorrection : forall k : Fin T, forall a,
      correction k a =
        reluApproxCorrectedAffineCorrection scale theta trans k.val a) :
    forall t : Nat, t <= T ->
      reluApproxTaylorCoefficientRecursion scale
          (fun k : Fin T => trans k.val) correction coefficient0 t =
        reluApproxCorrectedAffineRecursion scale theta trans t := by
  intro t ht
  induction t with
  | zero =>
      simpa [reluApproxTaylorCoefficientRecursion] using hcoefficient0
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxTaylorCoefficientRecursion]
      simp only [dif_pos htlt]
      funext a
      rw [ih (Nat.le_of_succ_le ht), hcorrection ⟨t, htlt⟩ a]
      exact (reluApproxCorrectedAffineRecursion_succ
        scale theta trans t a).symm

/-- Fractional tails generated by the exact base shift and prescribed digits. -/
noncomputable def reluApproxTaylorTailRecursion {A : Type*} {T : Nat}
    (base : Real) (digit : Fin T -> A -> Nat) (tail0 : A -> Real) :
    Nat -> A -> Real
  | 0 => tail0
  | k + 1 => if hk : k < T then fun a =>
      base * reluApproxTaylorTailRecursion base digit tail0 k a -
        (digit ⟨k, hk⟩ a : Real)
    else reluApproxTaylorTailRecursion base digit tail0 k

/-- A zero digit stream started from a zero tail stays zero. -/
private theorem reluApproxTaylorTailRecursion_zero
    {A : Type*} {T : Nat} (base : Real) (n : Nat) :
    reluApproxTaylorTailRecursion (A := A) (T := T) base
        (fun _ _ => 0) (fun _ => 0) n = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reluApproxTaylorTailRecursion]
      split_ifs
      · funext a
        simp [ih]
      · exact ih

/-- The prescribed parallel digit recursion maintains the complete Taylor
machine invariant for every scheduled time. -/
private theorem reluApproxTaylorMachineDigitRecursionFrom_exact
    {d r T : Nat}
    (base : Real) (shift : Nat) (step : Fin T -> Fin d -> Real)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (x center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorDigitRecursionFrom
        (fun k => reluApproxTaylorMachineMatrix base (trans k))
        (fun k => reluApproxTaylorMachineBias (step k)
          shift scale)
        (fun _ => reluApproxTaylorMachineDigitCoeff scale)
        digit
        (reluApproxTaylorMachineState x center0 coefficient0 tail0) t =
      reluApproxTaylorMachineState x
        (reluApproxTaylorCenterRecursion step center0 t)
        (reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 t)
        (reluApproxTaylorTailRecursion base digit tail0 t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxParallelFloorDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      rw [reluApproxTaylorMachineDigitState_exact
        (correction := correction ⟨t, htlt⟩)
        (hdigit := hdigit ⟨t, htlt⟩)]
      rw [reluApproxTaylorCenterRecursion,
        reluApproxTaylorCoefficientRecursion,
        reluApproxTaylorTailRecursion]
      simp only [dif_pos htlt]

/-- Extend a finite correction schedule by the positive sentinel digit used to
keep the final decoded tail away from an integer boundary. -/
def reluApproxSentinelDigit {A : Type*} {T : Nat}
    (digit : Fin T -> A -> Nat) (a : A) (k : Nat) : Nat :=
  if hk : k < T then digit ⟨k, hk⟩ a else 1

/-- Repeated exact base shifts of a correction code with one terminal sentinel
leave precisely the unconsumed finite base tail. -/
private theorem reluApproxTaylorTailRecursion_eq_finiteBaseTail
    {A : Type*} {T : Nat} {base : Real} (hbase : base ≠ 0)
    (digit : Fin T -> A -> Nat) (a : A) (t : Nat) (ht : t <= T) :
    reluApproxTaylorTailRecursion base digit
        (fun b => reluApproxFiniteBaseTail base
          (reluApproxSentinelDigit digit b) 0 (T + 1)) t a =
      reluApproxFiniteBaseTail base
        (reluApproxSentinelDigit digit a) t (T - t + 1) := by
  induction t with
  | zero => simp [reluApproxTaylorTailRecursion]
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxTaylorTailRecursion]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      have hlength : T - t + 1 = (T - (t + 1) + 1) + 1 := by omega
      rw [hlength, reluApproxFiniteBaseTail_succ hbase]
      simp [reluApproxSentinelDigit, htlt]

/-- A finite correction code with its terminal sentinel is the old code plus
one final positive base digit. -/
private theorem reluApproxFiniteBaseTail_sentinel_zero
    {A : Type*} {T : Nat} (base : Real)
    (digit : Fin T -> A -> Nat) (a : A) :
    reluApproxFiniteBaseTail base
        (reluApproxSentinelDigit digit a) 0 (T + 1) =
      Finset.univ.sum (fun k : Fin T =>
        (digit k a : Real) / base ^ (k.val + 1)) +
        1 / base ^ (T + 1) := by
  rw [reluApproxFiniteBaseTail, Finset.sum_range_succ]
  congr 1
  · rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _hk
    have hklt : k < T := Finset.mem_range.mp _hk
    simp [reluApproxSentinelDigit, hklt]
  · simp [reluApproxSentinelDigit]

/-- At every scheduled time, multiplying the sentinel-extended remaining tail
by the base exposes the current digit and another positive finite tail. -/
private theorem reluApproxTaylorTailRecursion_base_eq_digit_add_tail
    {A : Type*} {T : Nat} {base : Real} (hbase : base ≠ 0)
    (digit : Fin T -> A -> Nat) (a : A) (k : Fin T) :
    base * reluApproxTaylorTailRecursion base digit
        (fun b => reluApproxFiniteBaseTail base
          (reluApproxSentinelDigit digit b) 0 (T + 1)) k.val a =
      (digit k a : Real) + Finset.univ.sum
        (fun j : Fin (T - k.val) =>
          (reluApproxSentinelDigit digit a (k.val + 1 + j.val) : Real) /
            base ^ (j.val + 1)) := by
  rw [reluApproxTaylorTailRecursion_eq_finiteBaseTail
    hbase digit a k.val k.isLt.le]
  have hlength : T - k.val + 1 = (T - (k.val + 1)) + 1 + 1 := by omega
  rw [hlength, reluApproxFiniteBaseTail_succ hbase]
  simp only [reluApproxSentinelDigit, dif_pos k.isLt]
  have hrem : T - (k.val + 1) + 1 = T - k.val := by omega
  rw [hrem, reluApproxFiniteBaseTail, Finset.sum_fin_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < T - k.val := Finset.mem_range.mp hj
  simp only [dif_pos hjlt]
  unfold reluApproxSentinelDigit
  rfl

/-- A sentinel-extended Taylor correction tail is read exactly by the
truncated-floor bank at every scheduled fine-grid step. -/
theorem reluApproxTaylorTailRecursion_floor_exact
    {A : Type*} {T : Nat}
    (dExp : Real) (c : Nat) (hc : c = Nat.ceil (Real.exp dExp))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (hRsep : forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-((T - k.val : Nat) : Int)))
    (digit : Fin T -> A -> Nat)
    (hDigitLower : forall k a, 1 <= digit k a)
    (hDigitUpper : forall k a, digit k a <= 2 * c + 3)
    (k : Fin T) (a : A) :
    truncatedFloorReLUFunction R floorBound
        ((baseNat : Real) * reluApproxTaylorTailRecursion (baseNat : Real)
          digit
          (fun b => reluApproxFiniteBaseTail (baseNat : Real)
            (reluApproxSentinelDigit digit b) 0 (T + 1)) k.val a) =
      (digit k a : Real) := by
  have hbasePos : 0 < baseNat := by omega
  have hbaseNe : (baseNat : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt hbasePos)
  have hTailLength : 1 <= T - k.val := by omega
  let tailDigit : Fin (T - k.val) -> Nat := fun j =>
    reluApproxSentinelDigit digit a (k.val + 1 + j.val)
  have hTailLower : forall j : Fin (T - k.val), 1 <= tailDigit j := by
    intro j
    by_cases hj : k.val + 1 + j.val < T
    · simp [tailDigit, reluApproxSentinelDigit, hj, hDigitLower]
    · simp [tailDigit, reluApproxSentinelDigit, hj]
  have hTailUpper : forall j : Fin (T - k.val), tailDigit j <= 2 * c + 3 := by
    intro j
    by_cases hj : k.val + 1 + j.val < T
    · simp [tailDigit, reluApproxSentinelDigit, hj, hDigitUpper]
    · simp [tailDigit, reluApproxSentinelDigit, hj]
  let z : Real := (baseNat : Real) *
    reluApproxTaylorTailRecursion (baseNat : Real) digit
      (fun b => reluApproxFiniteBaseTail (baseNat : Real)
        (reluApproxSentinelDigit digit b) 0 (T + 1)) k.val a
  have hz : z = (digit k a : Real) + Finset.univ.sum
      (fun j : Fin (T - k.val) =>
        (tailDigit j : Real) / (baseNat : Real) ^ (j.val + 1)) := by
    dsimp [z, tailDigit]
    exact reluApproxTaylorTailRecursion_base_eq_digit_add_tail
      hbaseNe digit a k
  let signedDigit : Int := (digit k a : Int) - (c + 2 : Int)
  have hshift : (digit k a : Int) = signedDigit + (c + 2 : Int) := by
    dsimp [signedDigit]
    ring
  obtain ⟨_hgap, _hclass, htruncated, hfloor, _hsigned⟩ :=
    reluApprox_recursiveBaseTail_floorDigit_exact_on_gap
      dExp c hc baseNat hbase (digit k a) signedDigit hshift
        (hDigitLower k a) (hDigitUpper k a) (T - k.val) hTailLength
        tailDigit hTailLower hTailUpper z hz floorBound hFloorBound R hR
        (hRsep k)
  rw [show (baseNat : Real) *
      reluApproxTaylorTailRecursion (baseNat : Real) digit
        (fun b => reluApproxFiniteBaseTail (baseNat : Real)
          (reluApproxSentinelDigit digit b) 0 (T + 1)) k.val a = z by rfl]
  rw [htruncated, hfloor]

/-- The concrete parallel floor-bank macros execute the full prescribed
Taylor-machine recursion when initialized by sentinel-extended code tails. -/
private theorem reluApproxTaylorMachineMacroRecursionFrom_exact
    {d r T : Nat}
    (c : Nat) (hc : c = Nat.ceil (Real.exp (d : Real)))
    (baseNat : Nat) (hbase : 4 + 2 * c <= baseNat)
    (floorBound : Nat) (hFloorBound : floorBound + 1 = baseNat)
    (R : Real) (hR : 0 < R)
    (hRsep : forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-((T - k.val : Nat) : Int)))
    (step : Fin T -> Fin d -> Real)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (c + 2 : Nat))
    (hDigitLower : forall k a, 1 <= digit k a)
    (hDigitUpper : forall k a, digit k a <= 2 * c + 3)
    (x center0 : Fin d -> Real)
    (coefficient0 : TaylorMultiindex r d -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorMacroRecursionFrom R floorBound
        (baseNat : Real)
        (fun _ a =>
          (Sum.inr (Sum.inr a) : ReLUApproxTaylorMachineRegister d r))
        (fun k => reluApproxTaylorMachineMatrix (baseNat : Real) (trans k))
        (fun k => reluApproxTaylorMachineBias (step k) (c + 2) scale)
        (fun _ => reluApproxTaylorMachineDigitCoeff scale)
        (reluApproxTaylorMachineState x center0 coefficient0
          (fun a => reluApproxFiniteBaseTail (baseNat : Real)
            (reluApproxSentinelDigit digit a) 0 (T + 1))) t =
      reluApproxTaylorMachineState x
        (reluApproxTaylorCenterRecursion step center0 t)
        (reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 t)
        (reluApproxTaylorTailRecursion (baseNat : Real) digit
          (fun a => reluApproxFiniteBaseTail (baseNat : Real)
            (reluApproxSentinelDigit digit a) 0 (T + 1)) t) := by
  have hbase_pos : 0 < baseNat := by omega
  have hbase_ne : (baseNat : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hbase_pos)
  let u0 : ReLUApproxTaylorMachineRegister d r -> Real :=
    reluApproxTaylorMachineState x center0 coefficient0
      (fun a => reluApproxFiniteBaseTail (baseNat : Real)
        (reluApproxSentinelDigit digit a) 0 (T + 1))
  have hDigitState : forall n, n <= T ->
      reluApproxParallelFloorDigitRecursionFrom
          (fun k => reluApproxTaylorMachineMatrix (baseNat : Real) (trans k))
          (fun k => reluApproxTaylorMachineBias (step k) (c + 2) scale)
          (fun _ => reluApproxTaylorMachineDigitCoeff scale)
          digit u0 n =
        reluApproxTaylorMachineState x
          (reluApproxTaylorCenterRecursion step center0 n)
          (reluApproxTaylorCoefficientRecursion
            scale trans correction coefficient0 n)
          (reluApproxTaylorTailRecursion (baseNat : Real) digit
            (fun a => reluApproxFiniteBaseTail (baseNat : Real)
              (reluApproxSentinelDigit digit a) 0 (T + 1)) n) := by
    intro n hn
    exact reluApproxTaylorMachineDigitRecursionFrom_exact
      (baseNat : Real) (c + 2) step scale trans digit correction hdigit
      x center0 coefficient0
      (fun a => reluApproxFiniteBaseTail (baseNat : Real)
        (reluApproxSentinelDigit digit a) 0 (T + 1)) n hn
  have hTailLength : forall k : Fin T,
      1 <= T - k.val := by
    intro k
    omega
  have hTailLower : forall k : Fin T, forall a,
      forall j : Fin (T - k.val),
        1 <= reluApproxSentinelDigit digit a (k.val + 1 + j.val) := by
    intro k a j
    by_cases hj : k.val + 1 + j.val < T
    · simp [reluApproxSentinelDigit, hj, hDigitLower]
    · simp [reluApproxSentinelDigit, hj]
  have hTailUpper : forall k : Fin T, forall a,
      forall j : Fin (T - k.val),
        reluApproxSentinelDigit digit a (k.val + 1 + j.val) <= 2 * c + 3 := by
    intro k a j
    by_cases hj : k.val + 1 + j.val < T
    · simp [reluApproxSentinelDigit, hj, hDigitUpper]
    · simp [reluApproxSentinelDigit, hj]
  have hcode : forall k : Fin T, forall a : TaylorMultiindex r d,
      (baseNat : Real) *
          reluApproxParallelFloorDigitRecursionFrom
            (fun k => reluApproxTaylorMachineMatrix (baseNat : Real) (trans k))
            (fun k => reluApproxTaylorMachineBias (step k) (c + 2) scale)
            (fun _ => reluApproxTaylorMachineDigitCoeff scale)
            digit u0 k.val
            (Sum.inr (Sum.inr a) : ReLUApproxTaylorMachineRegister d r) =
        (digit k a : Real) + Finset.univ.sum
          (fun j : Fin (T - k.val) =>
            (reluApproxSentinelDigit digit a (k.val + 1 + j.val) : Real) /
              (baseNat : Real) ^ (j.val + 1)) := by
    intro k a
    rw [congrFun (hDigitState k.val k.isLt.le)
      (Sum.inr (Sum.inr a) : ReLUApproxTaylorMachineRegister d r)]
    exact reluApproxTaylorTailRecursion_base_eq_digit_add_tail
      hbase_ne digit a k
  have hMacro :=
    reluApproxParallelFloorMacroRecursionFrom_eq_digit_of_baseTail
      (d : Real) c hc baseNat hbase floorBound hFloorBound R hR
      (fun k _ => T - k.val) (fun k _ => hTailLength k)
      (fun k _ => hRsep k)
      (fun _ a =>
        (Sum.inr (Sum.inr a) : ReLUApproxTaylorMachineRegister d r))
      (fun k => reluApproxTaylorMachineMatrix (baseNat : Real) (trans k))
      (fun k => reluApproxTaylorMachineBias (step k) (c + 2) scale)
      (fun _ => reluApproxTaylorMachineDigitCoeff scale)
      digit
      (fun k a j => reluApproxSentinelDigit digit a (k.val + 1 + j.val))
      hDigitLower hDigitUpper hTailLower hTailUpper u0 hcode t ht
  exact hMacro.trans (hDigitState t ht)

/-- A decoder scale can be chosen uniformly for all suffix lengths of a finite
base-tail schedule. Its magnitude affects weights but not network width. -/
theorem exists_reluApproxDecoderScale_for_finiteTail
    (baseNat T : Nat) (hbase : 2 <= baseNat) :
    exists R : Real, 0 < R /\ forall k : Fin T,
      1 / R < (baseNat : Real) ^ (-((T - k.val : Nat) : Int)) := by
  let b : Real := baseNat
  let R : Real := 2 * b ^ T
  have hbpos : 0 < b := by
    dsimp [b]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hbase)
  have hb1 : 1 <= b := by
    dsimp [b]
    exact_mod_cast (le_trans (by omega : 1 <= 2) hbase)
  have hbpow : 0 < b ^ T := pow_pos hbpos T
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro k
  have hden : b ^ T < 2 * b ^ T := by nlinarith
  have hsmall : 1 / R < 1 / (b ^ T) := by
    dsimp [R]
    exact one_div_lt_one_div_of_lt hbpow hden
  have hnegT : 1 / (b ^ T) = b ^ (-(T : Int)) := by
    rw [zpow_neg, zpow_natCast]
    rw [one_div]
  have hexp : -(T : Int) <= -((T - k.val : Nat) : Int) := by
    omega
  calc
    1 / R < 1 / (b ^ T) := hsmall
    _ = b ^ (-(T : Int)) := hnegT
    _ <= b ^ (-((T - k.val : Nat) : Int)) :=
      zpow_le_zpow_right₀ hb1 hexp

/-- Reindex a typed feature matrix along chosen state and feature
equivalences. Unlike `Fintype.equivFin`, the chosen state equivalence can be
aligned with a preceding concrete scan layout. -/
private noncomputable def reluApproxEquivFeatureMatrix
    {S H : Type*} {s h : Nat} (eS : S ≃ Fin s) (eH : H ≃ Fin h)
    (feature : H -> S -> Real) : Matrix (Fin h) (Fin s) Real :=
  fun j i => feature (eH.symm j) (eS.symm i)

private noncomputable def reluApproxEquivFeatureBias
    {H : Type*} {h : Nat} (eH : H ≃ Fin h)
    (bias : H -> Real) : Fin h -> Real :=
  fun j => bias (eH.symm j)

private noncomputable def reluApproxEquivUpdateMatrix
    {S H : Type*} {s h : Nat} (eS : S ≃ Fin s) (eH : H ≃ Fin h)
    (update : S -> H -> Real) : Matrix (Fin s) (Fin h) Real :=
  fun i j => update (eS.symm i) (eH.symm j)

private noncomputable def reluApproxEquivUpdateBias
    {S : Type*} {s : Nat} (eS : S ≃ Fin s)
    (bias : S -> Real) : Fin s -> Real :=
  fun i => bias (eS.symm i)

/-- A chosen pair of finite equivalences preserves every step of a typed macro
recursion, including an arbitrary initial state. -/
private theorem reluApproxTypedMacroRecursionFrom_equiv
    {S H : Type*} [Fintype S] [Fintype H]
    {s h T : Nat} (eS : S ≃ Fin s) (eH : H ≃ Fin h)
    (feature : Fin T -> H -> S -> Real)
    (featureBias : Fin T -> H -> Real)
    (update : Fin T -> S -> H -> Real)
    (updateBias : Fin T -> S -> Real)
    (u0 : S -> Real) (t : Nat) (ht : t <= T) :
    (fun i => reluApproxMacroRecursionFrom
      (fun k => reluApproxEquivFeatureMatrix eS eH (feature k))
      (fun k => reluApproxEquivFeatureBias eH (featureBias k))
      (fun k => reluApproxEquivUpdateMatrix eS eH (update k))
      (fun k => reluApproxEquivUpdateBias eS (updateBias k))
      (fun j => u0 (eS.symm j)) t (eS i)) =
      reluApproxTypedMacroRecursionFrom
        feature featureBias update updateBias u0 t := by
  induction t with
  | zero =>
      funext i
      simp [reluApproxMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom]
  | succ t ih =>
      funext i
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom]
      simp only [dif_pos htlt, reluApproxFiniteAffineMap,
        reluApproxTypedAffineMap, reluApproxEquivUpdateMatrix,
        reluApproxEquivUpdateBias, reluApproxEquivFeatureMatrix,
        reluApproxEquivFeatureBias, Equiv.symm_apply_apply]
      rw [← Equiv.sum_comp eH]
      apply congrArg (fun z : Real => z + updateBias ⟨t, htlt⟩ i)
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [Equiv.symm_apply_apply]
      congr 1
      congr 1
      rw [← Equiv.sum_comp eS]
      apply congrArg (fun z : Real => z + featureBias ⟨t, htlt⟩ j)
      apply Finset.sum_congr rfl
      intro k _hk
      rw [congrFun (ih (Nat.le_of_succ_le ht)) k]
      simp

/-- Compile a vector-valued coarse box scan followed by a parallel floor-bank
state recursion into one exact-depth fully connected ReLU network. -/
private theorem exists_reluApproxVectorBoxScan_then_parallelFloorNet
    {d m T U D W B : Nat} {S A : Type*}
    [Fintype S] [Fintype A] [DecidableEq S]
    (eS : S ≃ Fin (reluApproxVectorBoxScanStateSize d m))
    (Rscan : Real) (lower upper : Fin T -> Fin d -> Real)
    (payload : Fin T -> Fin m -> Real)
    (Rfloor base : Real)
    (tail : Fin U -> A -> S)
    (P : Fin U -> S -> S -> Real)
    (bias : Fin U -> S -> Real)
    (digitCoeff : Fin U -> S -> A -> Real)
    (outputWeight : S -> Real) (outputBias : Real)
    (hdepth : 2 * (T * 2 + U) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d m
      let hscan := reluApproxVectorBoxScanFeatureSize d m
      let hfloor := Fintype.card (ReLUApproxParallelFloorFeature S A B)
      (s + s) + (hscan + hfloor) <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
      N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
      forall x : Fin d -> Real,
        N.realize x =
          (Finset.univ.sum fun i : S => outputWeight i *
            reluApproxParallelFloorMacroRecursionFrom Rfloor B base tail
              P bias digitCoeff
              (fun j => reluApproxVectorBoxScanState x
                (reluApproxVectorBoxScanAccumulator
                  Rscan lower upper payload x T) (eS j)) U i) + outputBias := by
  let s := reluApproxVectorBoxScanStateSize d m
  let hscan := reluApproxVectorBoxScanFeatureSize d m
  let H := ReLUApproxParallelFloorFeature S A B
  let hfloor := Fintype.card H
  let eH : H ≃ Fin hfloor := Fintype.equivFin H
  let feature : Fin U -> H -> S -> Real := fun k =>
    reluApproxParallelFloorFeatureMatrix base B (tail k)
  let featureBias : Fin U -> H -> Real := fun _ =>
    reluApproxParallelFloorFeatureBias Rfloor B
  let update : Fin U -> S -> H -> Real := fun k =>
    reluApproxParallelFloorUpdateMatrix Rfloor B (P k) (digitCoeff k)
  let B2 : Fin U -> Matrix (Fin hfloor) (Fin s) Real := fun k =>
    reluApproxEquivFeatureMatrix eS eH (feature k)
  let c2 : Fin U -> Fin hfloor -> Real := fun k =>
    reluApproxEquivFeatureBias eH (featureBias k)
  let A2 : Fin U -> Matrix (Fin s) (Fin hfloor) Real := fun k =>
    reluApproxEquivUpdateMatrix eS eH (update k)
  let b2 : Fin U -> Fin s -> Real := fun k =>
    reluApproxEquivUpdateBias eS (bias k)
  let featureMatrix : Fin (T * 2 + U) ->
      Matrix (Fin (hscan + hfloor)) (Fin s) Real :=
    reluApproxConcatFeatureSchedule
      (reluApproxVectorBoxScanFeatureSchedule Rscan) B2
  let featureBiasAll : Fin (T * 2 + U) -> Fin (hscan + hfloor) -> Real :=
    reluApproxConcatFeatureBiasSchedule
      (reluApproxVectorBoxScanFeatureBiasSchedule
        Rscan lower upper payload) c2
  let updateMatrix : Fin (T * 2 + U) ->
      Matrix (Fin s) (Fin (hscan + hfloor)) Real :=
    reluApproxConcatUpdateSchedule
      (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T)) A2
  let updateBiasAll : Fin (T * 2 + U) -> Fin s -> Real :=
    reluApproxConcatUpdateBiasSchedule
      (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T)) b2
  let outputWeightFin : Fin s -> Real := fun i => outputWeight (eS.symm i)
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxSignedMacroRecursionNet_exactDepth
      (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
      featureMatrix featureBiasAll updateMatrix updateBiasAll
      outputWeightFin outputBias hdepth hwidth
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x
  rw [hNrealize]
  apply congrArg (fun z : Real => z + outputBias)
  rw [← Equiv.sum_comp eS]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [outputWeightFin, Equiv.symm_apply_apply]
  congr 1
  have hconcat := reluApproxSignedMacroRecursion_concat
    (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
    (reluApproxVectorBoxScanFeatureSchedule Rscan)
    (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper payload)
    (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T))
    (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T))
    B2 c2 A2 b2 x
  rw [show featureMatrix = reluApproxConcatFeatureSchedule
      (reluApproxVectorBoxScanFeatureSchedule Rscan) B2 by rfl,
    show featureBiasAll = reluApproxConcatFeatureBiasSchedule
      (reluApproxVectorBoxScanFeatureBiasSchedule
        Rscan lower upper payload) c2 by rfl,
    show updateMatrix = reluApproxConcatUpdateSchedule
      (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T)) A2 by rfl,
    show updateBiasAll = reluApproxConcatUpdateBiasSchedule
      (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T)) b2 by rfl,
    congrFun hconcat (eS i)]
  have hscanEq :
      reluApproxSignedMacroRecursion
          (reluApproxVectorBoxScanInputMatrix d m) (fun _ => 0)
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (reluApproxVectorBoxScanFeatureBiasSchedule
            Rscan lower upper payload)
          (reluApproxVectorBoxScanUpdateSchedule (d := d) (m := m) (T := T))
          (reluApproxVectorBoxScanUpdateBiasSchedule (d := d) (m := m) (T := T))
          x (T * 2) =
        reluApproxVectorBoxScanState x
          (reluApproxVectorBoxScanAccumulator
            Rscan lower upper payload x T) := by
    simpa [Nat.mul_comm] using
      (reluApproxVectorBoxScanRecursion_even
        Rscan lower upper payload x T le_rfl)
  rw [hscanEq]
  have hreindex := reluApproxTypedMacroRecursionFrom_equiv
    eS eH feature featureBias update bias
    (fun j => reluApproxVectorBoxScanState x
      (reluApproxVectorBoxScanAccumulator Rscan lower upper payload x T)
      (eS j)) U le_rfl
  simpa [B2, c2, A2, b2, feature, featureBias, update,
    reluApproxParallelFloorMacroRecursionFrom] using congrFun hreindex i

/-- Payload registers selected in the coarse pass: center, Taylor jet, and one
sentinel-extended correction tail for each Taylor coefficient. -/
private abbrev ReLUApproxTaylorPayload (d r : Nat) :=
  (Fin d ⊕ TaylorMultiindex r d) ⊕ TaylorMultiindex r d

/-- Semantic form of the vector box-scan workspace. The final three summands
are the violation register and temporary signed payload copies. -/
private abbrev ReLUApproxTaylorScanState (d r : Nat) :=
  Fin d ⊕ (ReLUApproxTaylorPayload d r ⊕
    (Fin 1 ⊕ (ReLUApproxTaylorPayload d r ⊕
      ReLUApproxTaylorPayload d r)))

private noncomputable def reluApproxTaylorPayloadEquivFin (d r : Nat) :
    ReLUApproxTaylorPayload d r ≃
      Fin (Fintype.card (ReLUApproxTaylorPayload d r)) :=
  Fintype.equivFin _

private noncomputable def reluApproxTaylorPayloadPairEquivFin (d r : Nat) :
    (ReLUApproxTaylorPayload d r ⊕ ReLUApproxTaylorPayload d r) ≃
      Fin (Fintype.card (ReLUApproxTaylorPayload d r) +
        Fintype.card (ReLUApproxTaylorPayload d r)) :=
  (Equiv.sumCongr (reluApproxTaylorPayloadEquivFin d r)
    (reluApproxTaylorPayloadEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxTaylorWorkEquivFin (d r : Nat) :
    (Fin 1 ⊕ (ReLUApproxTaylorPayload d r ⊕
      ReLUApproxTaylorPayload d r)) ≃
      Fin (1 + (Fintype.card (ReLUApproxTaylorPayload d r) +
        Fintype.card (ReLUApproxTaylorPayload d r))) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
    (reluApproxTaylorPayloadPairEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxTaylorAccumulatorWorkEquivFin (d r : Nat) :
    (ReLUApproxTaylorPayload d r ⊕
      (Fin 1 ⊕ (ReLUApproxTaylorPayload d r ⊕
        ReLUApproxTaylorPayload d r))) ≃
      Fin (Fintype.card (ReLUApproxTaylorPayload d r) +
        (1 + (Fintype.card (ReLUApproxTaylorPayload d r) +
          Fintype.card (ReLUApproxTaylorPayload d r)))) :=
  (Equiv.sumCongr (reluApproxTaylorPayloadEquivFin d r)
    (reluApproxTaylorWorkEquivFin d r)).trans finSumFinEquiv

/-- The semantic Taylor scan state is canonically aligned with the concrete
`Fin` indexing used by the vector box-scan network. -/
private noncomputable def reluApproxTaylorScanStateEquivFin (d r : Nat) :
    ReLUApproxTaylorScanState d r ≃
      Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxTaylorPayload d r))) :=
  (Equiv.sumCongr (Equiv.refl (Fin d))
    (reluApproxTaylorAccumulatorWorkEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxTaylorScanStateValue {d r : Nat}
    (x : Fin d -> Real)
    (payload : ReLUApproxTaylorPayload d r -> Real) :
    ReLUApproxTaylorScanState d r -> Real
  | .inl q => x q
  | .inr (.inl p) => payload p
  | .inr (.inr _) => 0

/-- Reading the concrete terminal vector-scan state through the aligned
equivalence gives the semantic input/payload state exactly. -/
private theorem reluApproxVectorBoxScanState_taylorEquiv
    {d r : Nat} (x : Fin d -> Real)
    (payload : ReLUApproxTaylorPayload d r -> Real) :
    (fun z => reluApproxVectorBoxScanState x
      (fun j => payload ((reluApproxTaylorPayloadEquivFin d r).symm j))
      (reluApproxTaylorScanStateEquivFin d r z)) =
      reluApproxTaylorScanStateValue x payload := by
  funext z
  rcases z with q | (p | (u | (p | p)))
  · rw [show reluApproxTaylorScanStateEquivFin d r (.inl q) =
        Fin.castAdd _ q by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxTaylorScanStateValue]
  · rw [show reluApproxTaylorScanStateEquivFin d r (.inr (.inl p)) =
        Fin.natAdd d (Fin.castAdd _
          (reluApproxTaylorPayloadEquivFin d r p)) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxTaylorScanStateValue,
      reluApproxTaylorPayloadEquivFin]
  · rw [show reluApproxTaylorScanStateEquivFin d r
        (.inr (.inr (.inl u))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxTaylorPayload d r))
          (Fin.castAdd _ u)) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxTaylorScanStateValue]
  · rw [show reluApproxTaylorScanStateEquivFin d r
        (.inr (.inr (.inr (.inl p)))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxTaylorPayload d r))
          (Fin.natAdd 1 (Fin.castAdd _
            (reluApproxTaylorPayloadEquivFin d r p)))) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxTaylorScanStateValue]
  · rw [show reluApproxTaylorScanStateEquivFin d r
        (.inr (.inr (.inr (.inr p)))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxTaylorPayload d r))
          (Fin.natAdd 1 (Fin.natAdd
            (Fintype.card (ReLUApproxTaylorPayload d r))
            (reluApproxTaylorPayloadEquivFin d r p)))) by rfl]
    simp only [reluApproxVectorBoxScanState,
      reluApproxTaylorScanStateValue, Fin.addCases_right]

/-- On a safe coarse box, the concrete vector scan loads the complete semantic
Taylor payload selected by that box.  This is the interface between the coarse
selection pass and the parallel Taylor-tail decoder. -/
private theorem reluApproxTaylorScanState_of_unique
    {d r T : Nat} {R : Real} (hR : 0 < R)
    (lower upper : Fin T -> Fin d -> Real)
    (payload : Fin T -> ReLUApproxTaylorPayload d r -> Real)
    (x : Fin d -> Real) (active : Fin T)
    (hpayload : forall i : Fin T, forall p : ReLUApproxTaylorPayload d r,
      |payload i p| <= R)
    (hactive : forall q : Fin d,
      lower active q + R⁻¹ <= x q /\ x q <= upper active q - R⁻¹)
    (hinactive : forall i : Fin T, i ≠ active -> exists q : Fin d,
      x q <= lower i q \/ upper i q <= x q) :
    (fun z => reluApproxVectorBoxScanState x
      (reluApproxVectorBoxScanAccumulator R lower upper
        (fun i j => payload i ((reluApproxTaylorPayloadEquivFin d r).symm j))
        x T)
      (reluApproxTaylorScanStateEquivFin d r z)) =
      reluApproxTaylorScanStateValue x (payload active) := by
  let payloadFin : Fin T ->
      Fin (Fintype.card (ReLUApproxTaylorPayload d r)) -> Real :=
    fun i j => payload i ((reluApproxTaylorPayloadEquivFin d r).symm j)
  have hpayloadFin : forall i : Fin T,
      forall j : Fin (Fintype.card (ReLUApproxTaylorPayload d r)),
        |payloadFin i j| <= R := by
    intro i j
    exact hpayload i ((reluApproxTaylorPayloadEquivFin d r).symm j)
  have hacc :
      reluApproxVectorBoxScanAccumulator R lower upper payloadFin x T =
        payloadFin active := by
    funext j
    rw [reluApproxVectorBoxScanAccumulator_eq_sum]
    exact reluApprox_sum_boxGate_eq_payload_of_unique hR lower upper
      (fun i => payloadFin i j) x active (fun i => hpayloadFin i j)
      hactive hinactive
  rw [show (fun i j =>
      payload i ((reluApproxTaylorPayloadEquivFin d r).symm j)) =
        payloadFin by rfl, hacc]
  simpa [payloadFin] using
    reluApproxVectorBoxScanState_taylorEquiv x (payload active)

/-- Temporary registers carried by the vector box scan but not used by the
Taylor recurrence after the coarse payload has been selected. -/
private abbrev ReLUApproxTaylorScanWork (d r : Nat) :=
  Fin 1 ⊕ (ReLUApproxTaylorPayload d r ⊕
    ReLUApproxTaylorPayload d r)

/-- A Taylor-machine state together with the obsolete coarse-scan workspace. -/
private abbrev ReLUApproxTaylorMachineWithWork (d r : Nat) :=
  ReLUApproxTaylorMachineRegister d r ⊕ ReLUApproxTaylorScanWork d r

/-- Reassociate the semantic box-scan layout into the Taylor machine registers
and a disjoint work suffix. -/
private def reluApproxTaylorMachineWithWorkEquivScanState (d r : Nat) :
    ReLUApproxTaylorMachineWithWork d r ≃ ReLUApproxTaylorScanState d r where
  toFun
    | .inl (.inl (.inl q)) => .inl q
    | .inl (.inl (.inr q)) => .inr (.inl (.inl (.inl q)))
    | .inl (.inr (.inl a)) => .inr (.inl (.inl (.inr a)))
    | .inl (.inr (.inr a)) => .inr (.inl (.inr a))
    | .inr w => .inr (.inr w)
  invFun
    | .inl q => .inl (.inl (.inl q))
    | .inr (.inl (.inl (.inl q))) => .inl (.inl (.inr q))
    | .inr (.inl (.inl (.inr a))) => .inl (.inr (.inl a))
    | .inr (.inl (.inr a)) => .inl (.inr (.inr a))
    | .inr (.inr w) => .inr w
  left_inv z := by
    rcases z with ((q | q) | (a | a)) | w <;> rfl
  right_inv z := by
    rcases z with q | (((q | a) | a) | w) <;> rfl

/-- Package a center, Taylor jet, and correction tails as one coarse-scan
payload. -/
noncomputable def reluApproxTaylorPayloadState {d r : Nat}
    (center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorPayload d r -> Real
  | .inl (.inl q) => center q
  | .inl (.inr a) => coefficient a
  | .inr a => tail a

/-- Extend a Taylor-machine state by zero on the completed scan workspace. -/
private noncomputable def reluApproxTaylorMachineWithWorkState {d r : Nat}
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    ReLUApproxTaylorMachineWithWork d r -> Real
  | .inl z => reluApproxTaylorMachineState x center coefficient tail z
  | .inr _ => 0

private theorem reluApproxTaylorMachineWithWorkState_eq_sumElim
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    reluApproxTaylorMachineWithWorkState x center coefficient tail =
      Sum.elim (reluApproxTaylorMachineState x center coefficient tail)
        (fun _ => 0) := by
  funext z
  rcases z with z | w <;> rfl

/-- The selected scan payload is exactly the corresponding Taylor-machine
state, with every obsolete work register equal to zero. -/
private theorem reluApproxTaylorScanStateValue_equiv_machineWithWork
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real) :
    (fun z => reluApproxTaylorScanStateValue x
      (reluApproxTaylorPayloadState center coefficient tail)
      (reluApproxTaylorMachineWithWorkEquivScanState d r z)) =
      reluApproxTaylorMachineWithWorkState x center coefficient tail := by
  funext z
  rcases z with ((q | q) | (a | a)) | w <;>
    simp [reluApproxTaylorMachineWithWorkEquivScanState,
      reluApproxTaylorScanStateValue, reluApproxTaylorPayloadState,
      reluApproxTaylorMachineWithWorkState,
      reluApproxTaylorMachineState]

/-- Extend an affine Taylor-state update by zero on an auxiliary work suffix. -/
private noncomputable def reluApproxAffineMapWithZeroWork {S W : Type*}
    (P : S -> S -> Real) : (S ⊕ W) -> (S ⊕ W) -> Real
  | .inl i, .inl j => P i j
  | _, _ => 0

/-- Extend an affine bias by zero on an auxiliary work suffix. -/
private noncomputable def reluApproxBiasWithZeroWork {S W : Type*}
    (bias : S -> Real) : S ⊕ W -> Real
  | .inl i => bias i
  | .inr _ => 0

/-- Extend parallel decoded-digit coefficients by zero on a work suffix. -/
private noncomputable def reluApproxDigitCoeffWithZeroWork {S W A : Type*}
    (digitCoeff : S -> A -> Real) : (S ⊕ W) -> A -> Real
  | .inl i => digitCoeff i
  | .inr _ => fun _ => 0

/-- A parallel affine/digit update on the Taylor prefix leaves a zero work
suffix equal to zero. -/
private theorem reluApproxParallelFloorDigitState_withZeroWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (digit : A -> Nat)
    (u : S -> Real) :
    reluApproxParallelFloorDigitState
      (reluApproxAffineMapWithZeroWork (W := W) P)
      (reluApproxBiasWithZeroWork (W := W) bias)
      (reluApproxDigitCoeffWithZeroWork (W := W) digitCoeff)
      digit (Sum.elim u (fun _ => 0)) =
        Sum.elim
          (reluApproxParallelFloorDigitState P bias digitCoeff digit u)
          (fun _ => 0) := by
  funext z
  rcases z with i | w
  · simp [reluApproxParallelFloorDigitState,
      reluApproxTypedAffineMap, reluApproxAffineMapWithZeroWork,
      reluApproxBiasWithZeroWork, reluApproxDigitCoeffWithZeroWork,
      Fintype.sum_sum_type]
  · simp [reluApproxParallelFloorDigitState,
      reluApproxTypedAffineMap, reluApproxAffineMapWithZeroWork,
      reluApproxBiasWithZeroWork, reluApproxDigitCoeffWithZeroWork,
      Fintype.sum_sum_type]

/-- The zero-work extension commutes with every finite prescribed-digit
recursion, not merely with one update. -/
private theorem reluApproxParallelFloorDigitRecursionFrom_withZeroWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    {T : Nat}
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real)
    (digit : Fin T -> A -> Nat) (u : S -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorDigitRecursionFrom
      (fun k => reluApproxAffineMapWithZeroWork (W := W) (P k))
      (fun k => reluApproxBiasWithZeroWork (W := W) (bias k))
      (fun k => reluApproxDigitCoeffWithZeroWork (W := W) (digitCoeff k))
      digit (Sum.elim u (fun _ => 0)) t =
        Sum.elim
          (reluApproxParallelFloorDigitRecursionFrom
            P bias digitCoeff digit u t)
          (fun _ => 0) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxParallelFloorDigitRecursionFrom,
        reluApproxParallelFloorDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxParallelFloorDigitState_withZeroWork
        (P ⟨t, htlt⟩) (bias ⟨t, htlt⟩)
        (digitCoeff ⟨t, htlt⟩) (digit ⟨t, htlt⟩)
        (reluApproxParallelFloorDigitRecursionFrom
          P bias digitCoeff digit u t)

/-- The concrete truncated-floor state update also commutes with adjoining a
zero work suffix. -/
private theorem reluApproxParallelFloorState_withZeroWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    (R : Real) (B : Nat) (base : Real) (tail : A -> S)
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (u : S -> Real) :
    reluApproxParallelFloorState R B base (fun a => Sum.inl (tail a))
      (reluApproxAffineMapWithZeroWork (W := W) P)
      (reluApproxBiasWithZeroWork (W := W) bias)
      (reluApproxDigitCoeffWithZeroWork (W := W) digitCoeff)
      (Sum.elim u (fun _ => 0)) =
        Sum.elim
          (reluApproxParallelFloorState R B base tail P bias digitCoeff u)
          (fun _ => 0) := by
  funext z
  rcases z with i | w
  · simp [reluApproxParallelFloorState,
      reluApproxTypedAffineMap, reluApproxAffineMapWithZeroWork,
      reluApproxBiasWithZeroWork, reluApproxDigitCoeffWithZeroWork,
      Fintype.sum_sum_type]
  · simp [reluApproxParallelFloorState,
      reluApproxTypedAffineMap, reluApproxAffineMapWithZeroWork,
      reluApproxBiasWithZeroWork, reluApproxDigitCoeffWithZeroWork,
      Fintype.sum_sum_type]

/-- A complete concrete parallel floor schedule on a Taylor-state prefix is
unchanged when compiled with an additional zero workspace. -/
private theorem reluApproxParallelFloorMacroRecursionFrom_withZeroWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    [DecidableEq S] [DecidableEq W]
    {T : Nat}
    (R : Real) (B : Nat) (base : Real) (tail : Fin T -> A -> S)
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real) (u : S -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorMacroRecursionFrom R B base
      (fun k a => Sum.inl (tail k a))
      (fun k => reluApproxAffineMapWithZeroWork (W := W) (P k))
      (fun k => reluApproxBiasWithZeroWork (W := W) (bias k))
      (fun k => reluApproxDigitCoeffWithZeroWork (W := W) (digitCoeff k))
      (Sum.elim u (fun _ => 0)) t =
        Sum.elim
          (reluApproxParallelFloorMacroRecursionFrom
            R B base tail P bias digitCoeff u t)
          (fun _ => 0) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      have iht := ih (Nat.le_of_succ_le ht)
      change reluApproxTypedMacroRecursionFrom _ _ _ _ _ t =
        Sum.elim (reluApproxTypedMacroRecursionFrom _ _ _ _ _ t)
          (fun _ => 0) at iht
      simp only [reluApproxParallelFloorMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom, dif_pos htlt]
      rw [iht]
      rw [reluApproxParallelFloorMacro_exact,
        reluApproxParallelFloorMacro_exact]
      exact reluApproxParallelFloorState_withZeroWork
        R B base (tail ⟨t, htlt⟩) (P ⟨t, htlt⟩)
        (bias ⟨t, htlt⟩) (digitCoeff ⟨t, htlt⟩)
        (reluApproxParallelFloorMacroRecursionFrom
          R B base tail P bias digitCoeff u t)

/-! ## Taylor updates with persistent selected registers

The fine pass transports the current Taylor jet while retaining the center and
coefficients selected by earlier box gates.  These extensions act as the given
affine/digit update on the Taylor prefix and as the identity on an arbitrary
work suffix.
-/

/-- Center and Taylor-coefficient registers retained after a successful fine
box selection. -/
private abbrev ReLUApproxSelectedTaylorRegisters (d r : Nat) :=
  Fin d ⊕ TaylorMultiindex r d

/-- Semantic contents of the registers selected by a fine box gate. -/
noncomputable def reluApproxSelectedTaylorState {d r : Nat}
    (center : Fin d -> Real)
    (coefficient : TaylorMultiindex r d -> Real) :
    ReLUApproxSelectedTaylorRegisters d r -> Real
  | .inl q => center q
  | .inr a => coefficient a

/-- Accumulator registers used by the fine pass: the current center, Taylor
jet and correction tails, followed by the center and jet selected for `x`. -/
abbrev ReLUApproxFineAccumulator (d r : Nat) :=
  ReLUApproxTaylorPayload d r ⊕ ReLUApproxSelectedTaylorRegisters d r

/-- The current-center coordinate inside the fine-pass accumulator. -/
private def reluApproxFineCurrentCenterRegister {d r : Nat} (q : Fin d) :
    ReLUApproxFineAccumulator d r :=
  .inl (.inl (.inl q))

/-- The current-coefficient coordinate inside the fine-pass accumulator. -/
private def reluApproxFineCurrentCoefficientRegister {d r : Nat}
    (a : TaylorMultiindex r d) : ReLUApproxFineAccumulator d r :=
  .inl (.inl (.inr a))

/-- Source register read by a fine-box selection payload.  Current registers
are mapped to themselves but suppressed by a zero gain; selected registers
read the corresponding current center or Taylor coefficient. -/
private def reluApproxFineSelectionSource {d r : Nat} :
    ReLUApproxFineAccumulator d r → ReLUApproxFineAccumulator d r
  | .inl p => .inl p
  | .inr (.inl q) => reluApproxFineCurrentCenterRegister q
  | .inr (.inr a) => reluApproxFineCurrentCoefficientRegister a

/-- Gain of the fine-box selection payload: preserve all current registers and
gate only the selected center and coefficient registers. -/
private def reluApproxFineSelectionGain {d r : Nat} :
    ReLUApproxFineAccumulator d r → Real
  | .inl _ => 0
  | .inr _ => 1

/-- Payload presented to one fine-box gate. -/
private noncomputable def reluApproxFineSelectionPayload {d r : Nat}
    (acc : ReLUApproxFineAccumulator d r → Real) :
    ReLUApproxFineAccumulator d r → Real :=
  fun z => reluApproxFineSelectionGain z *
    acc (reluApproxFineSelectionSource z)

/-- Semantic fine-box accumulator update around the current center. -/
private noncomputable def reluApproxFineSelectionAccumulator {d r : Nat}
    (R radius : Real) (x : Fin d → Real)
    (acc : ReLUApproxFineAccumulator d r → Real) :
    ReLUApproxFineAccumulator d r → Real :=
  fun z => acc z + reluApproxBoxGate R
    (fun q => acc (reluApproxFineCurrentCenterRegister q) - radius)
    (fun q => acc (reluApproxFineCurrentCenterRegister q) + radius)
    x (reluApproxFineSelectionPayload acc z)

/-- Selected center after testing the box around the current Taylor center. -/
private noncomputable def reluApproxFineSelectedCenterStep {d : Nat}
    (R radius : Real) (x center selectedCenter : Fin d -> Real) :
    Fin d -> Real :=
  fun q => selectedCenter q + reluApproxBoxGate R
    (fun u => center u - radius) (fun u => center u + radius) x (center q)

/-- Selected Taylor jet after testing the box around the current center. -/
private noncomputable def reluApproxFineSelectedCoefficientStep {d r : Nat}
    (R radius : Real) (x center : Fin d -> Real)
    (coefficient selectedCoefficient : TaylorMultiindex r d -> Real) :
    TaylorMultiindex r d -> Real :=
  fun a => selectedCoefficient a + reluApproxBoxGate R
    (fun u => center u - radius) (fun u => center u + radius) x
    (coefficient a)

/-- On a semantic Taylor accumulator, one fine selection step preserves the
current center/jet/tails and only adds a gated copy to the selected registers. -/
private theorem reluApproxFineSelectionAccumulator_state
    {d r : Nat} (R radius : Real) (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxFineSelectionAccumulator R radius x
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient)) =
      Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
        (reluApproxSelectedTaylorState
          (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
          (reluApproxFineSelectedCoefficientStep R radius x center coefficient
            selectedCoefficient)) := by
  funext z
  rcases z with (((q | a) | a) | (q | a)) <;>
    simp [reluApproxFineSelectionAccumulator,
      reluApproxFineSelectionPayload, reluApproxFineSelectionGain,
      reluApproxFineSelectionSource, reluApproxFineCurrentCenterRegister,
      reluApproxFineCurrentCoefficientRegister,
      reluApproxTaylorPayloadState, reluApproxSelectedTaylorState,
      reluApproxFineSelectedCenterStep,
      reluApproxFineSelectedCoefficientStep, reluApproxBoxGate]

/-- Canonical finite indexing of the fine-pass accumulator. -/
private noncomputable def reluApproxFineAccumulatorEquivFin (d r : Nat) :
    ReLUApproxFineAccumulator d r ≃
      Fin (Fintype.card (ReLUApproxFineAccumulator d r)) :=
  Fintype.equivFin _

/-- Temporary violation and signed-payload registers used by one fine-box
selection cycle. -/
private abbrev ReLUApproxFineScanWork (d r : Nat) :=
  Fin 1 ⊕ (ReLUApproxFineAccumulator d r ⊕
    ReLUApproxFineAccumulator d r)

/-- Typed version of the concrete vector-box state used throughout the fine
pass.  Its middle block contains both the current Taylor payload and the
selected center/jet registers. -/
private abbrev ReLUApproxFineScanState (d r : Nat) :=
  Fin d ⊕ (ReLUApproxFineAccumulator d r ⊕
    ReLUApproxFineScanWork d r)

private noncomputable def reluApproxFineAccumulatorPairEquivFin (d r : Nat) :
    (ReLUApproxFineAccumulator d r ⊕
      ReLUApproxFineAccumulator d r) ≃
      Fin (Fintype.card (ReLUApproxFineAccumulator d r) +
        Fintype.card (ReLUApproxFineAccumulator d r)) :=
  (Equiv.sumCongr (reluApproxFineAccumulatorEquivFin d r)
    (reluApproxFineAccumulatorEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxFineScanWorkEquivFin (d r : Nat) :
    ReLUApproxFineScanWork d r ≃
      Fin (1 + (Fintype.card (ReLUApproxFineAccumulator d r) +
        Fintype.card (ReLUApproxFineAccumulator d r))) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
    (reluApproxFineAccumulatorPairEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxFineAccumulatorWorkEquivFin (d r : Nat) :
    (ReLUApproxFineAccumulator d r ⊕
      ReLUApproxFineScanWork d r) ≃
      Fin (Fintype.card (ReLUApproxFineAccumulator d r) +
        (1 + (Fintype.card (ReLUApproxFineAccumulator d r) +
          Fintype.card (ReLUApproxFineAccumulator d r)))) :=
  (Equiv.sumCongr (reluApproxFineAccumulatorEquivFin d r)
    (reluApproxFineScanWorkEquivFin d r)).trans finSumFinEquiv

/-- Canonical alignment between the typed fine-pass state and the concrete
state layout consumed by the vector box-scan matrices. -/
private noncomputable def reluApproxFineScanStateEquivFin (d r : Nat) :
    ReLUApproxFineScanState d r ≃
      Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))) :=
  (Equiv.sumCongr (Equiv.refl (Fin d))
    (reluApproxFineAccumulatorWorkEquivFin d r)).trans finSumFinEquiv

private noncomputable def reluApproxFineScanStateValue {d r : Nat}
    (x : Fin d -> Real)
    (acc : ReLUApproxFineAccumulator d r -> Real) :
    ReLUApproxFineScanState d r -> Real
  | .inl q => x q
  | .inr (.inl z) => acc z
  | .inr (.inr _) => 0

/-- Reading a canonical concrete vector-box state through the fine-pass
equivalence gives exactly the typed input/accumulator state. -/
private theorem reluApproxVectorBoxScanState_fineEquiv
    {d r : Nat} (x : Fin d -> Real)
    (acc : ReLUApproxFineAccumulator d r -> Real) :
    (fun z => reluApproxVectorBoxScanState x
      (fun j => acc ((reluApproxFineAccumulatorEquivFin d r).symm j))
      (reluApproxFineScanStateEquivFin d r z)) =
      reluApproxFineScanStateValue x acc := by
  funext z
  rcases z with q | (p | (u | (p | p)))
  · rw [show reluApproxFineScanStateEquivFin d r (.inl q) =
        Fin.castAdd _ q by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxFineScanStateValue]
  · rw [show reluApproxFineScanStateEquivFin d r (.inr (.inl p)) =
        Fin.natAdd d (Fin.castAdd _
          (reluApproxFineAccumulatorEquivFin d r p)) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxFineScanStateValue,
      reluApproxFineAccumulatorEquivFin]
  · rw [show reluApproxFineScanStateEquivFin d r
        (.inr (.inr (.inl u))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxFineAccumulator d r))
          (Fin.castAdd _ u)) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxFineScanStateValue]
  · rw [show reluApproxFineScanStateEquivFin d r
        (.inr (.inr (.inr (.inl p)))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxFineAccumulator d r))
          (Fin.natAdd 1 (Fin.castAdd _
            (reluApproxFineAccumulatorEquivFin d r p)))) by rfl]
    simp [reluApproxVectorBoxScanState,
      reluApproxFineScanStateValue,
      reluApproxFineAccumulatorEquivFin]
  · rw [show reluApproxFineScanStateEquivFin d r
        (.inr (.inr (.inr (.inr p)))) =
        Fin.natAdd d (Fin.natAdd
          (Fintype.card (ReLUApproxFineAccumulator d r))
          (Fin.natAdd 1 (Fin.natAdd
            (Fintype.card (ReLUApproxFineAccumulator d r))
            (reluApproxFineAccumulatorEquivFin d r p)))) by rfl]
    simp only [reluApproxVectorBoxScanState,
      reluApproxFineScanStateValue, Fin.addCases_right]

/-- The complete typed state of the fine pass.  The Taylor machine is the
active prefix updated by the digit decoder; the selected registers and the
box-scan scratch space form a persistent suffix. -/
private abbrev ReLUApproxFineMachineState (d r : Nat) :=
  ReLUApproxTaylorMachineRegister d r ⊕
    (ReLUApproxSelectedTaylorRegisters d r ⊕
      ReLUApproxFineScanWork d r)

/-- Reassociate the complete fine machine into the concrete vector-box scan
layout.  In particular, the input is shared by both machines and the current
center, coefficient and tail registers form the accumulator prefix. -/
private def reluApproxFineMachineEquivScanState (d r : Nat) :
    ReLUApproxFineMachineState d r ≃ ReLUApproxFineScanState d r where
  toFun
    | .inl (.inl (.inl q)) => .inl q
    | .inl (.inl (.inr q)) => .inr (.inl (.inl (.inl (.inl q))))
    | .inl (.inr (.inl a)) => .inr (.inl (.inl (.inl (.inr a))))
    | .inl (.inr (.inr a)) => .inr (.inl (.inl (.inr a)))
    | .inr (.inl (.inl q)) => .inr (.inl (.inr (.inl q)))
    | .inr (.inl (.inr a)) => .inr (.inl (.inr (.inr a)))
    | .inr (.inr w) => .inr (.inr w)
  invFun
    | .inl q => .inl (.inl (.inl q))
    | .inr (.inl (.inl (.inl (.inl q)))) => .inl (.inl (.inr q))
    | .inr (.inl (.inl (.inl (.inr a)))) => .inl (.inr (.inl a))
    | .inr (.inl (.inl (.inr a))) => .inl (.inr (.inr a))
    | .inr (.inl (.inr (.inl q))) => .inr (.inl (.inl q))
    | .inr (.inl (.inr (.inr a))) => .inr (.inl (.inr a))
    | .inr (.inr w) => .inr (.inr w)
  left_inv z := by
    rcases z with ((q | q) | (a | a)) | ((q | a) | w) <;> rfl
  right_inv z := by
    rcases z with q | ((((q | a) | a) | (q | a)) | w) <;> rfl

/-- Concrete finite indexing of the complete fine machine, aligned with the
vector-box scan rather than an arbitrary `Fintype.equivFin` ordering. -/
private noncomputable def reluApproxFineMachineEquivFin (d r : Nat) :
    ReLUApproxFineMachineState d r ≃
      Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))) :=
  (reluApproxFineMachineEquivScanState d r).trans
    (reluApproxFineScanStateEquivFin d r)

/-- Semantic contents of the complete fine-pass state with cleared box-scan
scratch registers. -/
private noncomputable def reluApproxFineMachineStateValue {d r : Nat}
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    ReLUApproxFineMachineState d r -> Real
  | .inl z => reluApproxTaylorMachineState x center coefficient tail z
  | .inr (.inl z) =>
      reluApproxSelectedTaylorState selectedCenter selectedCoefficient z
  | .inr (.inr _) => 0

/-! ## Dynamic Taylor readout coordinates -/

/-- Inputs required by the terminal Taylor evaluator: coordinate differences
and the selected normalized Taylor coefficients. -/
private abbrev ReLUApproxTaylorEvaluationInput (d r : Nat) :=
  Fin d ⊕ TaylorMultiindex r d

/-- A fixed finite indexing of the terminal Taylor-evaluator inputs. -/
noncomputable def reluApproxTaylorEvaluationInputEquivFin (d r : Nat) :
    ReLUApproxTaylorEvaluationInput d r ≃
      Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) :=
  Fintype.equivFin _

/-- Terminal evaluator input assembled from the original input, the selected
fine-grid center, and the selected Taylor coefficients. -/
noncomputable def reluApproxTaylorEvaluationInputValue {d r : Nat}
    (x center : Fin d → Real) (coefficient : TaylorMultiindex r d → Real) :
    Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) → Real :=
  fun i => Sum.elim (fun q => x q - center q) coefficient
    ((reluApproxTaylorEvaluationInputEquivFin d r).symm i)

/-- Every Taylor term is represented as one coefficient coordinate followed
by its coordinate-difference factors. -/
def reluApproxTaylorEvaluationDegree {d r : Nat}
    (a : TaylorMultiindex r d) : Nat := a.1.val + 1

noncomputable def reluApproxTaylorEvaluationCoord {d r : Nat}
    (a : TaylorMultiindex r d) :
    Fin (reluApproxTaylorEvaluationDegree a) →
      Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) :=
  Fin.cases
    (reluApproxTaylorEvaluationInputEquivFin d r (.inr a))
    (fun q => reluApproxTaylorEvaluationInputEquivFin d r (.inl (a.2 q)))

@[simp] theorem reluApproxTaylorEvaluationInputValue_delta {d r : Nat}
    (x center : Fin d → Real) (coefficient : TaylorMultiindex r d → Real)
    (q : Fin d) :
    reluApproxTaylorEvaluationInputValue x center coefficient
        (reluApproxTaylorEvaluationInputEquivFin d r (.inl q)) =
      x q - center q := by
  simp [reluApproxTaylorEvaluationInputValue]

@[simp] theorem reluApproxTaylorEvaluationInputValue_coefficient {d r : Nat}
    (x center : Fin d → Real) (coefficient : TaylorMultiindex r d → Real)
    (a : TaylorMultiindex r d) :
    reluApproxTaylorEvaluationInputValue x center coefficient
        (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) =
      coefficient a := by
  simp [reluApproxTaylorEvaluationInputValue]

/-- Affine read from a terminal fine-machine state into the dynamic Taylor
evaluator.  The work suffix is ignored; coordinate rows subtract the selected
center from the preserved input, while coefficient rows read the selected jet. -/
private noncomputable def reluApproxTaylorEvaluationReadMatrix (d r work : ℕ) :
    Matrix (Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)) + work)) ℝ :=
  fun i j ↦
    match (reluApproxTaylorEvaluationInputEquivFin d r).symm i with
    | .inl q =>
        if j = Fin.castAdd work
            (reluApproxFineMachineEquivFin d r (.inl (.inl (.inl q))))
          then 1 else if j = Fin.castAdd work
            (reluApproxFineMachineEquivFin d r (.inr (.inl (.inl q))))
          then -1 else 0
    | .inr a =>
        if j = Fin.castAdd work
            (reluApproxFineMachineEquivFin d r (.inr (.inl (.inr a))))
          then 1 else 0

/-- The terminal-state affine read is exactly the evaluator input vector. -/
private theorem reluApproxTaylorEvaluationReadMatrix_exact {d r work : ℕ}
    (x center : Fin d → ℝ)
    (coefficient tail : TaylorMultiindex r d → ℝ)
    (selectedCenter : Fin d → ℝ)
    (selectedCoefficient : TaylorMultiindex r d → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxTaylorEvaluationReadMatrix d r work) (fun _ ↦ 0)
        (Fin.addCases
          (fun i ↦ reluApproxFineMachineStateValue x center coefficient tail
            selectedCenter selectedCoefficient
              ((reluApproxFineMachineEquivFin d r).symm i))
          (fun _ : Fin work ↦ 0)) =
      reluApproxTaylorEvaluationInputValue x selectedCenter
        selectedCoefficient := by
  classical
  funext i
  generalize hz : (reluApproxTaylorEvaluationInputEquivFin d r).symm i = z
  have hi : reluApproxTaylorEvaluationInputEquivFin d r z = i := by
    rw [← hz]
    exact (reluApproxTaylorEvaluationInputEquivFin d r).apply_symm_apply i
  rcases z with q | a
  · subst i
    let ix := reluApproxFineMachineEquivFin d r (.inl (.inl (.inl q)))
    let ic := reluApproxFineMachineEquivFin d r (.inr (.inl (.inl q)))
    let v : Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))) → ℝ :=
      fun j ↦ reluApproxFineMachineStateValue x center coefficient tail
        selectedCenter selectedCoefficient
          ((reluApproxFineMachineEquivFin d r).symm j)
    have hneq :
        ix ≠ ic := by
      intro h
      have h' := (reluApproxFineMachineEquivFin d r).injective h
      simpa [ix, ic] using h'
    simp [reluApproxFiniteAffineMap,
      reluApproxTaylorEvaluationReadMatrix,
      reluApproxTaylorEvaluationInputValue,
      reluApproxFineMachineStateValue,
      reluApproxTaylorMachineState,
      reluApproxSelectedTaylorState, Fin.sum_univ_add]
    change (∑ j, if j = ix then v j else if j = ic then -v j else 0) =
      x q - selectedCenter q
    calc
      (∑ j, if j = ix then v j else if j = ic then -v j else 0) =
          (∑ j, if j = ix then v j else 0) +
            ∑ j, if j = ic then -v j else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjx : j = ix
        · subst j
          simp [hneq]
        · simp [hjx]
      _ = v ix - v ic := by
        rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
        ring
      _ = x q - selectedCenter q := by
        simp [v, ix, ic, reluApproxFineMachineStateValue,
          reluApproxTaylorMachineState, reluApproxSelectedTaylorState]
  · subst i
    simp [reluApproxFiniteAffineMap,
      reluApproxTaylorEvaluationReadMatrix,
      reluApproxTaylorEvaluationInputValue,
      reluApproxFineMachineStateValue,
      reluApproxTaylorMachineState,
      reluApproxSelectedTaylorState, Fin.sum_univ_add]

/-- Taylor-evaluator input with the factorial normalization required by the
multivariate Taylor formula.  The state machine stores raw iterated
derivatives, so normalization belongs to this affine readout. -/
noncomputable def reluApproxNormalizedTaylorEvaluationInputValue {d r : Nat}
    (x center : Fin d -> Real) (coefficient : TaylorMultiindex r d -> Real) :
    Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) -> Real :=
  reluApproxTaylorEvaluationInputValue x center
    (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * coefficient a)

/-- Affine terminal-state read that normalizes each raw derivative register by
the factorial of its order. -/
noncomputable def reluApproxNormalizedTaylorEvaluationReadMatrix
    (d r work : Nat) :
    Matrix (Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)) + work)) Real :=
  fun i j =>
    match (reluApproxTaylorEvaluationInputEquivFin d r).symm i with
    | .inl _ => reluApproxTaylorEvaluationReadMatrix d r work i j
    | .inr a => ((Nat.factorial a.1.val : Real)⁻¹) *
        reluApproxTaylorEvaluationReadMatrix d r work i j

private theorem reluApproxNormalizedTaylorEvaluationReadMatrix_exact
    {d r work : Nat}
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxFiniteAffineMap
        (reluApproxNormalizedTaylorEvaluationReadMatrix d r work)
        (fun _ => 0)
        (Fin.addCases
          (fun i => reluApproxFineMachineStateValue x center coefficient tail
            selectedCenter selectedCoefficient
              ((reluApproxFineMachineEquivFin d r).symm i))
          (fun _ : Fin work => 0)) =
      reluApproxNormalizedTaylorEvaluationInputValue x selectedCenter
        selectedCoefficient := by
  classical
  have hraw := reluApproxTaylorEvaluationReadMatrix_exact (work := work)
    x center coefficient tail selectedCenter selectedCoefficient
  funext i
  generalize hz : (reluApproxTaylorEvaluationInputEquivFin d r).symm i = z
  have hi : reluApproxTaylorEvaluationInputEquivFin d r z = i := by
    rw [← hz]
    exact (reluApproxTaylorEvaluationInputEquivFin d r).apply_symm_apply i
  rcases z with q | a
  · subst i
    have hrow :
        reluApproxNormalizedTaylorEvaluationReadMatrix d r work
            (reluApproxTaylorEvaluationInputEquivFin d r (.inl q)) =
          reluApproxTaylorEvaluationReadMatrix d r work
            (reluApproxTaylorEvaluationInputEquivFin d r (.inl q)) := by
      funext j
      simp [reluApproxNormalizedTaylorEvaluationReadMatrix]
    simp only [reluApproxFiniteAffineMap]
    rw [hrow]
    simpa [reluApproxNormalizedTaylorEvaluationInputValue,
      reluApproxTaylorEvaluationInputValue,
      reluApproxFiniteAffineMap] using congrFun hraw
      (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))
  · subst i
    have hrow :
        reluApproxNormalizedTaylorEvaluationReadMatrix d r work
            (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) =
          fun j => ((Nat.factorial a.1.val : Real)⁻¹) *
            reluApproxTaylorEvaluationReadMatrix d r work
              (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) j := by
      funext j
      simp [reluApproxNormalizedTaylorEvaluationReadMatrix]
    simp only [reluApproxFiniteAffineMap]
    rw [hrow]
    simp only [reluApproxNormalizedTaylorEvaluationInputValue,
      reluApproxTaylorEvaluationInputValue, Equiv.symm_apply_apply,
      Pi.zero_apply, add_zero]
    change (Finset.univ.sum fun j =>
        (((Nat.factorial a.1.val : Real)⁻¹) *
          reluApproxTaylorEvaluationReadMatrix d r work
            (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) j) *
          Fin.addCases
            (fun i => reluApproxFineMachineStateValue x center coefficient tail
              selectedCenter selectedCoefficient
                ((reluApproxFineMachineEquivFin d r).symm i))
            (fun _ : Fin work => 0) j) =
      ((Nat.factorial a.1.val : Real)⁻¹) * selectedCoefficient a
    calc
      (Finset.univ.sum fun j =>
          (((Nat.factorial a.1.val : Real)⁻¹) *
            reluApproxTaylorEvaluationReadMatrix d r work
              (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) j) *
            Fin.addCases
              (fun i => reluApproxFineMachineStateValue x center coefficient tail
                selectedCenter selectedCoefficient
                  ((reluApproxFineMachineEquivFin d r).symm i))
              (fun _ : Fin work => 0) j) =
          ((Nat.factorial a.1.val : Real)⁻¹) *
            (Finset.univ.sum fun j =>
              reluApproxTaylorEvaluationReadMatrix d r work
                (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) j *
              Fin.addCases
                (fun i => reluApproxFineMachineStateValue x center coefficient tail
                  selectedCenter selectedCoefficient
                    ((reluApproxFineMachineEquivFin d r).symm i))
                (fun _ : Fin work => 0) j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = ((Nat.factorial a.1.val : Real)⁻¹) * selectedCoefficient a := by
        rw [show (Finset.univ.sum fun j =>
            reluApproxTaylorEvaluationReadMatrix d r work
              (reluApproxTaylorEvaluationInputEquivFin d r (.inr a)) j *
            Fin.addCases
              (fun i => reluApproxFineMachineStateValue x center coefficient tail
                selectedCenter selectedCoefficient
                  ((reluApproxFineMachineEquivFin d r).symm i))
              (fun _ : Fin work => 0) j) =
          selectedCoefficient a by
            simpa [reluApproxFiniteAffineMap] using congrFun hraw
              (reluApproxTaylorEvaluationInputEquivFin d r (.inr a))]

/-- A degree-dependent derivative error of order
`rho^(r - degree + beta)` contributes the uniform Taylor-polynomial error
`rho^(r + beta)` after multiplication by its centered monomial. -/
theorem normalized_centered_taylor_polynomial_error_of_residual_profile
    {d r : Nat} {beta C rho : Real}
    (hC : 0 <= C) (hrho : 0 < rho)
    (center x : Fin d -> Real)
    (coeff decoded : TaylorMultiindex r d -> Real)
    (hdecoded : forall a,
      |decoded a - coeff a| <=
        reluApproxTaylorResidualScale beta C rho a)
    (hbox : forall q : Fin d, |x q - center q| <= rho) :
    |finiteLinearCombination
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * decoded a)
        (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
          y (a.2 k) - center (a.2 k)) x -
      finiteLinearCombination
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a => ((Nat.factorial a.1.val : Real)⁻¹) * coeff a)
        (fun a y => Finset.univ.prod fun k : Fin a.1.val =>
          y (a.2 k) - center (a.2 k)) x| <=
      (Fintype.card (TaylorMultiindex r d) : Real) *
        ((C + 1) * Real.rpow rho ((r : Real) + beta)) := by
  classical
  let monomial : TaylorMultiindex r d -> Real := fun a =>
    Finset.univ.prod fun k : Fin a.1.val =>
      x (a.2 k) - center (a.2 k)
  have hmono : forall a : TaylorMultiindex r d,
      |monomial a| <= rho ^ a.1.val := by
    intro a
    dsimp [monomial]
    calc
      |Finset.univ.prod fun k : Fin a.1.val =>
          x (a.2 k) - center (a.2 k)| =
          Finset.univ.prod fun k : Fin a.1.val =>
            |x (a.2 k) - center (a.2 k)| := by
              exact Finset.abs_prod Finset.univ _
      _ <= Finset.univ.prod fun _k : Fin a.1.val => rho := by
        apply Finset.prod_le_prod
        · intro k _hk
          exact abs_nonneg _
        · intro k _hk
          exact hbox (a.2 k)
      _ = rho ^ a.1.val := by simp
  have hterm : forall a : TaylorMultiindex r d,
      |(((Nat.factorial a.1.val : Real)⁻¹) *
          (decoded a - coeff a)) * monomial a| <=
        (C + 1) * Real.rpow rho ((r : Real) + beta) := by
    intro a
    have hfac_pos : 0 < (Nat.factorial a.1.val : Real) := by
      exact_mod_cast Nat.factorial_pos a.1.val
    have hfac_one : (1 : Real) <= (Nat.factorial a.1.val : Real) := by
      exact_mod_cast Nat.factorial_pos a.1.val
    have hfac_nonneg : 0 <= (Nat.factorial a.1.val : Real)⁻¹ :=
      (inv_pos.mpr hfac_pos).le
    have hfac_le : (Nat.factorial a.1.val : Real)⁻¹ <= 1 :=
      (inv_le_one₀ hfac_pos).2 hfac_one
    have hscale_nonneg :
        0 <= reluApproxTaylorResidualScale beta C rho a := by
      unfold reluApproxTaylorResidualScale
      exact mul_nonneg (by linarith) (Real.rpow_nonneg hrho.le _)
    have hrhopow_nonneg : 0 <= rho ^ a.1.val :=
      pow_nonneg hrho.le _
    rw [abs_mul, abs_mul, abs_of_nonneg hfac_nonneg]
    have hpair :
        (Nat.factorial a.1.val : Real)⁻¹ * |decoded a - coeff a| <=
          1 * reluApproxTaylorResidualScale beta C rho a := by
      exact mul_le_mul hfac_le (hdecoded a) (abs_nonneg _) zero_le_one
    calc
      (Nat.factorial a.1.val : Real)⁻¹ * |decoded a - coeff a| *
          |monomial a| <=
          1 * reluApproxTaylorResidualScale beta C rho a *
            (rho ^ a.1.val) := by
        exact mul_le_mul hpair (hmono a) (abs_nonneg _)
          (mul_nonneg zero_le_one hscale_nonneg)
      _ = (C + 1) * Real.rpow rho ((r : Real) + beta) := by
        unfold reluApproxTaylorResidualScale
        rw [one_mul]
        calc
          (C + 1) * Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) *
              rho ^ a.1.val =
              (C + 1) *
                (Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) *
                  rho ^ a.1.val) := by ring
          _ = (C + 1) *
                (Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) *
                  Real.rpow rho (a.1.val : Real)) := by
              have hpow : rho ^ a.1.val =
                  Real.rpow rho (a.1.val : Real) := by
                exact (Real.rpow_natCast rho a.1.val).symm
              rw [hpow]
          _ = (C + 1) * Real.rpow rho
                ((((r - a.1.val : Nat) : Real) + beta) +
                  (a.1.val : Real)) := by
              exact congrArg (fun z : Real => (C + 1) * z)
                (Real.rpow_add hrho
                  (((r - a.1.val : Nat) : Real) + beta)
                  (a.1.val : Real)).symm
          _ = (C + 1) * Real.rpow rho ((r : Real) + beta) := by
              congr 2
              have hdeg : a.1.val <= r := Nat.le_of_lt_succ a.1.isLt
              have hnat : r - a.1.val + a.1.val = r :=
                Nat.sub_add_cancel hdeg
              have hcast : ((r - a.1.val : Nat) : Real) +
                  (a.1.val : Real) = r := by
                exact_mod_cast hnat
              linarith
  unfold finiteLinearCombination
  have hrewrite :
      (Finset.univ.sum fun a : TaylorMultiindex r d =>
          (Nat.factorial a.1.val : Real)⁻¹ * decoded a * monomial a) -
        (Finset.univ.sum fun a : TaylorMultiindex r d =>
          (Nat.factorial a.1.val : Real)⁻¹ * coeff a * monomial a) =
      Finset.univ.sum fun a : TaylorMultiindex r d =>
        ((Nat.factorial a.1.val : Real)⁻¹ * (decoded a - coeff a)) * monomial a := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  change |(Finset.univ.sum fun a : TaylorMultiindex r d =>
      (Nat.factorial a.1.val : Real)⁻¹ * decoded a * monomial a) -
    (Finset.univ.sum fun a : TaylorMultiindex r d =>
      (Nat.factorial a.1.val : Real)⁻¹ * coeff a * monomial a)| <= _
  rw [hrewrite]
  calc
    |Finset.univ.sum fun a : TaylorMultiindex r d =>
        ((Nat.factorial a.1.val : Real)⁻¹ * (decoded a - coeff a)) * monomial a| <=
        Finset.univ.sum fun a : TaylorMultiindex r d =>
          |((Nat.factorial a.1.val : Real)⁻¹ * (decoded a - coeff a)) * monomial a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum fun _a : TaylorMultiindex r d =>
        (C + 1) * Real.rpow rho ((r : Real) + beta) := by
      exact Finset.sum_le_sum fun a _ha => hterm a
    _ = (Fintype.card (TaylorMultiindex r d) : Real) *
        ((C + 1) * Real.rpow rho ((r : Real) + beta)) := by simp

/-- A degree-profiled raw-derivative error preserves a uniform bound after the
factorial normalization used by the terminal Taylor evaluator. -/
theorem abs_normalized_taylor_coefficient_le_of_residual_profile
    {d r : Nat} {beta C rho A : Real}
    (hbeta : 0 <= beta) (hC : 0 <= C)
    (hrho : 0 <= rho) (hrho_one : rho <= 1)
    (coeff decoded : TaylorMultiindex r d -> Real)
    (hcoeff : forall a,
      |((Nat.factorial a.1.val : Real)⁻¹) * coeff a| <= A)
    (hdecoded : forall a,
      |decoded a - coeff a| <=
        reluApproxTaylorResidualScale beta C rho a)
    (a : TaylorMultiindex r d) :
    |((Nat.factorial a.1.val : Real)⁻¹) * decoded a| <= A + C + 1 := by
  have hfac_pos : 0 < (Nat.factorial a.1.val : Real) := by
    exact_mod_cast Nat.factorial_pos a.1.val
  have hfac_one : (1 : Real) <= (Nat.factorial a.1.val : Real) := by
    exact_mod_cast Nat.factorial_pos a.1.val
  have hfac_nonneg : 0 <= (Nat.factorial a.1.val : Real)⁻¹ :=
    (inv_pos.mpr hfac_pos).le
  have hfac_le : (Nat.factorial a.1.val : Real)⁻¹ <= 1 :=
    (inv_le_one₀ hfac_pos).2 hfac_one
  have hexp : 0 <= ((r - a.1.val : Nat) : Real) + beta := by positivity
  have hrpow : Real.rpow rho (((r - a.1.val : Nat) : Real) + beta) <= 1 :=
    Real.rpow_le_one hrho hrho_one hexp
  have hscale_nonneg :
      0 <= reluApproxTaylorResidualScale beta C rho a := by
    unfold reluApproxTaylorResidualScale
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hrho _)
  have hscale_le :
      reluApproxTaylorResidualScale beta C rho a <= C + 1 := by
    unfold reluApproxTaylorResidualScale
    have hmul := mul_le_mul_of_nonneg_left hrpow
      (show 0 <= C + 1 by linarith)
    simpa using hmul
  have herr :
      |((Nat.factorial a.1.val : Real)⁻¹) * (decoded a - coeff a)| <= C + 1 := by
    rw [abs_mul, abs_of_nonneg hfac_nonneg]
    calc
      (Nat.factorial a.1.val : Real)⁻¹ * |decoded a - coeff a| <=
          1 * reluApproxTaylorResidualScale beta C rho a :=
        mul_le_mul hfac_le (hdecoded a) (abs_nonneg _) zero_le_one
      _ <= C + 1 := by simpa using hscale_le
  calc
    |((Nat.factorial a.1.val : Real)⁻¹) * decoded a| =
        |((Nat.factorial a.1.val : Real)⁻¹) * coeff a +
          ((Nat.factorial a.1.val : Real)⁻¹) * (decoded a - coeff a)| := by
            congr 1
            ring
    _ <= |((Nat.factorial a.1.val : Real)⁻¹) * coeff a| +
        |((Nat.factorial a.1.val : Real)⁻¹) * (decoded a - coeff a)| :=
      abs_add_le _ _
    _ <= A + (C + 1) := add_le_add (hcoeff a) herr
    _ = A + C + 1 := by ring

/-- Affine read of `x - selectedCenter` from a terminal fine-machine state. -/
private noncomputable def reluApproxSelectedDifferenceReadMatrix (d r work : ℕ) :
    Matrix (Fin d)
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)) + work)) ℝ :=
  fun q ↦ reluApproxTaylorEvaluationReadMatrix d r work
    (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))

private theorem reluApproxSelectedDifferenceReadMatrix_exact {d r work : ℕ}
    (x center : Fin d → ℝ)
    (coefficient tail : TaylorMultiindex r d → ℝ)
    (selectedCenter : Fin d → ℝ)
    (selectedCoefficient : TaylorMultiindex r d → ℝ) :
    reluApproxFiniteAffineMap
        (reluApproxSelectedDifferenceReadMatrix d r work) (fun _ ↦ 0)
        (Fin.addCases
          (fun i ↦ reluApproxFineMachineStateValue x center coefficient tail
            selectedCenter selectedCoefficient
              ((reluApproxFineMachineEquivFin d r).symm i))
          (fun _ : Fin work ↦ 0)) =
      fun q ↦ x q - selectedCenter q := by
  have h := reluApproxTaylorEvaluationReadMatrix_exact (work := work)
    x center coefficient tail selectedCenter selectedCoefficient
  funext q
  simpa [reluApproxSelectedDifferenceReadMatrix] using congrFun h
    (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))

/-- Translating both the input and center by the same vector does not change a
tensor tent weight. -/
theorem axisAlignedBoxTentWeight_zero_center_difference
    {d : ℕ} (x center scale : Fin d → ℝ) :
    axisAlignedBoxTentWeight (fun _ ↦ 0) scale (fun q ↦ x q - center q) =
      axisAlignedBoxTentWeight center scale x := by
  unfold axisAlignedBoxTentWeight coordinateTentReLUFunction
  apply Finset.prod_congr rfl
  intro q _hq
  congr 2 <;> ring

theorem reluApproxTaylorEvaluation_monomial_identity {d r : Nat}
    (x center : Fin d → Real) (coefficient : TaylorMultiindex r d → Real)
    (a : TaylorMultiindex r d) :
    (∏ q : Fin (reluApproxTaylorEvaluationDegree a),
        reluApproxTaylorEvaluationInputValue x center coefficient
          (reluApproxTaylorEvaluationCoord a q)) =
      coefficient a * ∏ q : Fin a.1.val, (x (a.2 q) - center (a.2 q)) := by
  unfold reluApproxTaylorEvaluationDegree
  rw [Fin.prod_univ_succ]
  simp [reluApproxTaylorEvaluationDegree, reluApproxTaylorEvaluationCoord]

/-- A uniform coordinate bound controls the whole dynamic Taylor-evaluation
sum.  The extra coefficient coordinate makes every monomial degree at most
`r + 1`. -/
theorem abs_reluApproxTaylorEvaluation_sum_le
    {d r : Nat} {R : Real} (hR : 1 <= R)
    (y : Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) -> Real)
    (hy : forall q, |y q| <= R) :
    |Finset.univ.sum fun a : TaylorMultiindex r d =>
        Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
          y (reluApproxTaylorEvaluationCoord a q)| <=
      (Fintype.card (TaylorMultiindex r d) : Real) * R ^ (r + 1) := by
  have hterm : forall a : TaylorMultiindex r d,
      |Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
          y (reluApproxTaylorEvaluationCoord a q)| <= R ^ (r + 1) := by
    intro a
    calc
      |Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
          y (reluApproxTaylorEvaluationCoord a q)| =
          Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
            |y (reluApproxTaylorEvaluationCoord a q)| := by
              exact Finset.abs_prod Finset.univ _
      _ <= Finset.univ.prod fun _q : Fin (reluApproxTaylorEvaluationDegree a) =>
          R := by
            apply Finset.prod_le_prod
            · intro q _hq
              exact abs_nonneg _
            · intro q _hq
              exact hy _
      _ = R ^ reluApproxTaylorEvaluationDegree a := by simp
      _ <= R ^ (r + 1) := by
        apply pow_le_pow_right₀ hR
        unfold reluApproxTaylorEvaluationDegree
        omega
  calc
    |Finset.univ.sum fun a : TaylorMultiindex r d =>
        Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
          y (reluApproxTaylorEvaluationCoord a q)| <=
        Finset.univ.sum fun a : TaylorMultiindex r d =>
          |Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
            y (reluApproxTaylorEvaluationCoord a q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum fun _a : TaylorMultiindex r d => R ^ (r + 1) := by
      exact Finset.sum_le_sum fun a _ha => hterm a
    _ = (Fintype.card (TaylorMultiindex r d) : Real) * R ^ (r + 1) := by simp

/-- Taylor-evaluator compiler with a caller-supplied propagation constant.  In
the final uniform theorem this constant is selected before the mesh parameter
`M`, which makes its independence of the resolution explicit. -/
theorem exists_reluNetworkClass_taylorEvaluation_fixed_width_rate_of_error_bound
    {d r M : ℕ} {beta R K : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) (hR : 0 < R) (hK : 0 ≤ K)
    (hKbound : ∀ e : ℝ, 0 ≤ e → e ≤ 8 →
      finiteCenteredMonomialPolynomialFixedWidthApproxError e R 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) ≤ K * e) :
    ∃ (Wpoly : ℕ) (cDepth : ℝ) (D P : ℕ)
        (g : (Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) → ℝ) → ℝ),
      0 < Wpoly ∧
      Wpoly = finiteCenteredMonomialPolynomialFixedWidthBound 10
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a ↦ reluApproxTaylorEvaluationDegree a) ∧
      0 < cDepth ∧ 0 < D ∧
      cDepth = 1 + (Finset.univ : Finset (TaylorMultiindex r d)).sum
        (fun a ↦
          max 1 (10 * (((r + 1) * M ^ d) + 2) : ℕ) *
            ((reluApproxTaylorEvaluationDegree a : ℝ) + 1)) ∧
      (D : ℝ) ≤ cDepth * 2 ∧
      P = fullyConnectedReLUParameterCount
        (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) D Wpoly ∧
      g ∈ reluNetworkClass
        (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) D Wpoly P ∧
      ∀ y : Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) → ℝ,
        (∀ q, |y q| ≤ R) →
          |g y - ∑ a : TaylorMultiindex r d,
              ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
                y (reluApproxTaylorEvaluationCoord a q)| ≤
            (8 * K) * shallowReLUResolutionRate M r beta := by
  classical
  let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
  let cMulErr : ℝ := 8 * shallowReLUResolutionRate M r beta
  have hmulSpec :=
    exists_reluNetworkClass_mul_fixed_width_rate_scaled_family
      (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one
  dsimp only at hmulSpec
  rcases hmulSpec with ⟨hcMulDepth, hcMulErr, hmul⟩
  obtain ⟨Wpoly, hWpoly, hWpolyEq, cDepth, hcDepth, hcDepthEq, hpoly⟩ :=
    exists_reluNetworkClass_finite_centered_monomial_polynomial_fixed_width_depth_rate_from_mul_gadget_explicit
      (d := Fintype.card (ReLUApproxTaylorEvaluationInput d r))
      (Wmul := 10) (cMulDepth := cMulDepth) (cMulErr := cMulErr)
      (by norm_num) hcMulDepth hcMulErr hmul
      (Finset.univ : Finset (TaylorMultiindex r d))
      (fun a ↦ reluApproxTaylorEvaluationDegree a)
      reluApproxTaylorEvaluationCoord (fun _ ↦ (1 : ℝ))
  obtain ⟨D, P, hD, hDbound, hP, g, hgClass, hgError⟩ :=
    hpoly 1 (by norm_num) R hR (fun _ ↦ 0)
  have hMpos : 0 < M := by omega
  have hrate_nonneg : 0 ≤ shallowReLUResolutionRate M r beta := by
    unfold shallowReLUResolutionRate
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _).le
  have hrate_le_one : shallowReLUResolutionRate M r beta ≤ 1 := by
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hexp : -(2 * ((r : ℝ) + beta)) ≤ 0 := by
      have hr : 0 ≤ (r : ℝ) := by positivity
      nlinarith
    unfold shallowReLUResolutionRate
    exact Real.rpow_le_one_of_one_le_of_nonpos hMone hexp
  have hcMulErr_nonneg : 0 ≤ cMulErr := by
    dsimp [cMulErr]
    positivity
  have hcMulErr_le : cMulErr ≤ 8 := by
    dsimp [cMulErr]
    nlinarith
  have hpropagated :
      finiteCenteredMonomialPolynomialFixedWidthApproxError cMulErr R 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) ≤
        K * cMulErr :=
    hKbound cMulErr hcMulErr_nonneg hcMulErr_le
  refine ⟨Wpoly, cDepth, D, P, g, hWpoly, hWpolyEq, hcDepth, hD, ?_,
    ?_, hP, hgClass, ?_⟩
  · simpa [cMulDepth] using hcDepthEq
  · norm_num at hDbound ⊢
    exact hDbound
  · intro y hy
    have hcentered : ∀ q, |y q - (0 : ℝ)| ≤ R := by
      simpa using hy
    calc
      |g y - ∑ a : TaylorMultiindex r d,
          ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
            y (reluApproxTaylorEvaluationCoord a q)| =
          |g y - finiteLinearCombination
            (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
            (fun a z ↦ ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
              (z (reluApproxTaylorEvaluationCoord a q) - 0)) y| := by
                simp [finiteLinearCombination]
      _ ≤ finiteCenteredMonomialPolynomialFixedWidthApproxError cMulErr R 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) :=
            hgError y hcentered
      _ ≤ K * cMulErr := hpropagated
      _ = (8 * K) * shallowReLUResolutionRate M r beta := by
        dsimp [cMulErr]
        ring

/-- The concrete exponential multiplier and the reusable finite-polynomial
compiler give a fixed-width network for the dynamic terminal Taylor readout.
The displayed depth constant retains its exact dependence on the mesh size;
its later `O(M^d)` estimate is therefore purely finite arithmetic. -/
theorem exists_reluNetworkClass_taylorEvaluation_fixed_width_rate
    {d r M : ℕ} {beta R : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) (hR : 0 < R) :
    ∃ (Wpoly : ℕ) (cDepth K : ℝ) (D P : ℕ)
        (g : (Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) → ℝ) → ℝ),
      0 < Wpoly ∧
      Wpoly = finiteCenteredMonomialPolynomialFixedWidthBound 10
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a ↦ reluApproxTaylorEvaluationDegree a) ∧
      0 < cDepth ∧ 0 ≤ K ∧ 0 < D ∧
      cDepth = 1 + (Finset.univ : Finset (TaylorMultiindex r d)).sum
        (fun a ↦
          max 1 (10 * (((r + 1) * M ^ d) + 2) : ℕ) *
            ((reluApproxTaylorEvaluationDegree a : ℝ) + 1)) ∧
      (D : ℝ) ≤ cDepth * 2 ∧
      P = fullyConnectedReLUParameterCount
        (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) D Wpoly ∧
      g ∈ reluNetworkClass
        (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) D Wpoly P ∧
      ∀ y : Fin (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) → ℝ,
        (∀ q, |y q| ≤ R) →
          |g y - ∑ a : TaylorMultiindex r d,
              ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
                y (reluApproxTaylorEvaluationCoord a q)| ≤
            (8 * K) * shallowReLUResolutionRate M r beta := by
  classical
  let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
  let cMulErr : ℝ := 8 * shallowReLUResolutionRate M r beta
  have hmulSpec :=
    exists_reluNetworkClass_mul_fixed_width_rate_scaled_family
      (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one
  dsimp only at hmulSpec
  rcases hmulSpec with ⟨hcMulDepth, hcMulErr, hmul⟩
  obtain ⟨K, hK, hKbound⟩ :=
    exists_finiteCenteredMonomialPolynomialFixedWidthApproxError_linear_mul_error_bound
      R hR.le (fun a : TaylorMultiindex r d ↦
        reluApproxTaylorEvaluationDegree a)
  obtain ⟨Wpoly, hWpoly, hWpolyEq, cDepth, hcDepth, hcDepthEq, hpoly⟩ :=
    exists_reluNetworkClass_finite_centered_monomial_polynomial_fixed_width_depth_rate_from_mul_gadget_explicit
      (d := Fintype.card (ReLUApproxTaylorEvaluationInput d r))
      (Wmul := 10) (cMulDepth := cMulDepth) (cMulErr := cMulErr)
      (by norm_num) hcMulDepth hcMulErr hmul
      (Finset.univ : Finset (TaylorMultiindex r d))
      (fun a ↦ reluApproxTaylorEvaluationDegree a)
      reluApproxTaylorEvaluationCoord (fun _ ↦ (1 : ℝ))
  obtain ⟨D, P, hD, hDbound, hP, g, hgClass, hgError⟩ :=
    hpoly 1 (by norm_num) R hR (fun _ ↦ 0)
  have hMpos : 0 < M := by omega
  have hrate_nonneg : 0 ≤ shallowReLUResolutionRate M r beta := by
    unfold shallowReLUResolutionRate
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _).le
  have hrate_le_one : shallowReLUResolutionRate M r beta ≤ 1 := by
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hexp : -(2 * ((r : ℝ) + beta)) ≤ 0 := by
      have hr : 0 ≤ (r : ℝ) := by positivity
      nlinarith
    unfold shallowReLUResolutionRate
    exact Real.rpow_le_one_of_one_le_of_nonpos hMone hexp
  have hcMulErr_nonneg : 0 ≤ cMulErr := by
    dsimp [cMulErr]
    positivity
  have hcMulErr_le : cMulErr ≤ 8 := by
    dsimp [cMulErr]
    nlinarith
  have hpropagated :
      finiteCenteredMonomialPolynomialFixedWidthApproxError cMulErr R 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) ≤
        K * cMulErr :=
    hKbound cMulErr hcMulErr_nonneg hcMulErr_le
  refine ⟨Wpoly, cDepth, K, D, P, g, hWpoly, hWpolyEq, hcDepth, hK, hD, ?_,
    ?_, hP, hgClass, ?_⟩
  · simpa [cMulDepth] using hcDepthEq
  · norm_num at hDbound ⊢
    exact hDbound
  · intro y hy
    have hcentered : ∀ q, |y q - (0 : ℝ)| ≤ R := by
      simpa using hy
    calc
      |g y - ∑ a : TaylorMultiindex r d,
          ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
            y (reluApproxTaylorEvaluationCoord a q)| =
          |g y - finiteLinearCombination
            (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
            (fun a z ↦ ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
              (z (reluApproxTaylorEvaluationCoord a q) - 0)) y| := by
                simp [finiteLinearCombination]
      _ ≤ finiteCenteredMonomialPolynomialFixedWidthApproxError cMulErr R 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) :=
            hgError y hcentered
      _ ≤ K * cMulErr := hpropagated
      _ = (8 * K) * shallowReLUResolutionRate M r beta := by
        dsimp [cMulErr]
        ring

/-- Concrete-network form of the terminal Taylor evaluator.  The coefficient
is itself one of the affine-read inputs, so the resulting monomial identity is
the selected Taylor polynomial rather than a polynomial with frozen weights. -/
theorem exists_fullyConnectedReLUNet_taylorEvaluation_fixed_width_rate
    {d r M : ℕ} {beta R : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M) (hbeta_pos : 0 < beta)
    (hbeta_le_one : beta ≤ 1) (hR : 0 < R) :
    ∃ (Wpoly : ℕ) (cDepth K : ℝ) (D P : ℕ)
        (N : FullyConnectedReLUNet
          (Fintype.card (ReLUApproxTaylorEvaluationInput d r))),
      0 < Wpoly ∧
      Wpoly = finiteCenteredMonomialPolynomialFixedWidthBound 10
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a ↦ reluApproxTaylorEvaluationDegree a) ∧
      0 < cDepth ∧ 0 ≤ K ∧ 0 < D ∧
      cDepth = 1 + (Finset.univ : Finset (TaylorMultiindex r d)).sum
        (fun a ↦
          max 1 (10 * (((r + 1) * M ^ d) + 2) : ℕ) *
            ((reluApproxTaylorEvaluationDegree a : ℝ) + 1)) ∧
      N.depth ≤ D ∧ N.width ≤ Wpoly ∧ N.parameterCount ≤ P ∧
      P = fullyConnectedReLUParameterCount
        (Fintype.card (ReLUApproxTaylorEvaluationInput d r)) D Wpoly ∧
      (D : ℝ) ≤ cDepth * 2 ∧
      ∀ (x center : Fin d → ℝ)
          (coefficient : TaylorMultiindex r d → ℝ),
        (∀ q,
          |reluApproxTaylorEvaluationInputValue x center coefficient q| ≤ R) →
          |N.realize
              (reluApproxTaylorEvaluationInputValue x center coefficient) -
            ∑ a : TaylorMultiindex r d,
              coefficient a *
                ∏ q : Fin a.1.val, (x (a.2 q) - center (a.2 q))| ≤
            (8 * K) * shallowReLUResolutionRate M r beta := by
  classical
  rcases exists_reluNetworkClass_taylorEvaluation_fixed_width_rate
      (d := d) (r := r) (M := M) (beta := beta) (R := R)
      hd hM hbeta_pos hbeta_le_one hR with
    ⟨Wpoly, cDepth, K, D, P, g, hWpoly, hWpolyEq, hcDepth, hK, hD,
      hcDepthEq, hDbound, hP, hgClass, hgError⟩
  change ∃ N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)),
      0 < N.depth ∧ N.depth ≤ D ∧ N.width ≤ Wpoly ∧
        N.parameterCount ≤ P ∧ ∀ y, g y = N.realize y at hgClass
  rcases hgClass with ⟨N, hNdepth, hNdepthLe, hNwidth, hNparam, hgN⟩
  refine ⟨Wpoly, cDepth, K, D, P, N, hWpoly, hWpolyEq, hcDepth, hK, hD,
    hcDepthEq, hNdepthLe, hNwidth, hNparam, hP, hDbound, ?_⟩
  intro x center coefficient hinput
  have hraw := hgError
    (reluApproxTaylorEvaluationInputValue x center coefficient) hinput
  have hsum :
      (∑ a : TaylorMultiindex r d,
          ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
            reluApproxTaylorEvaluationInputValue x center coefficient
              (reluApproxTaylorEvaluationCoord a q)) =
        ∑ a : TaylorMultiindex r d,
          coefficient a * ∏ q : Fin a.1.val,
            (x (a.2 q) - center (a.2 q)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact reluApproxTaylorEvaluation_monomial_identity x center coefficient a
  calc
    |N.realize (reluApproxTaylorEvaluationInputValue x center coefficient) -
        ∑ a : TaylorMultiindex r d,
          coefficient a * ∏ q : Fin a.1.val,
            (x (a.2 q) - center (a.2 q))| =
      |g (reluApproxTaylorEvaluationInputValue x center coefficient) -
        ∑ a : TaylorMultiindex r d,
          ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
            reluApproxTaylorEvaluationInputValue x center coefficient
              (reluApproxTaylorEvaluationCoord a q)| := by
        rw [hgN]
        rw [hsum]
    _ ≤ (8 * K) * shallowReLUResolutionRate M r beta := hraw

/-! ## Tensor-tent evaluation at the paper rate -/

/-- A dimension-only majorant for the errors accumulated while multiplying
the coordinate tent factors.  The factor `8` is the constant in the concrete
shallow ReLU multiplier. -/
noncomputable def tentProductRateConstant : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      8 * (1 + tentProductRateConstant k) ^ 2 +
        (1 + tentProductRateConstant k) *
          tentProductRateConstant k

theorem tentProductRateConstant_nonneg :
    ∀ k : ℕ, 0 ≤ tentProductRateConstant k := by
  intro k
  induction k with
  | zero => simp [tentProductRateConstant]
  | succ k ih =>
      simp only [tentProductRateConstant]
      positivity

/-- The tensor product of the exact coordinate tents admits a fixed-width
network whose error retains the full shallow ReLU paper rate.  Unlike the
generic tent compiler, this theorem does not replace the propagated error
constant by `max _ 1`; the small multiplier error is factored out at every
induction step. -/
theorem exists_reluNetworkClass_axisAlignedBoxTentWeight_fixed_width_rate
    {d r M : ℕ} {beta : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (center scale : Fin d → ℝ) (hscale : ∀ q, 0 ≤ scale q) :
    let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    ∃ D P : ℕ,
      0 < D ∧
      (D : ℝ) ≤ 2 + (d : ℝ) * (2 + cMulDepth) ∧
      P = fullyConnectedReLUParameterCount d D Wtent ∧
      ∃ g : (Fin d → ℝ) → ℝ,
        g ∈ reluNetworkClass d D Wtent P ∧
        ∀ x : Fin d → ℝ,
          |g x - axisAlignedBoxTentWeight center scale x| ≤
            tentProductRateConstant d *
              shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  let rate : ℝ := shallowReLUResolutionRate M r beta
  let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
  let cMulErr : ℝ := 8 * rate
  have hMpos : 0 < M := by omega
  have hrate_pos : 0 < rate := by
    dsimp [rate, shallowReLUResolutionRate]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _
  have hrate_nonneg : 0 ≤ rate := hrate_pos.le
  have hrate_le_one : rate ≤ 1 := by
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hexp : -(2 * ((r : ℝ) + beta)) ≤ 0 := by
      have hr : 0 ≤ (r : ℝ) := by positivity
      nlinarith
    dsimp [rate, shallowReLUResolutionRate]
    exact Real.rpow_le_one_of_one_le_of_nonpos hMone hexp
  have hmulSpec :=
    exists_reluNetworkClass_mul_fixed_width_rate_scaled_family
      (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one
  dsimp only at hmulSpec
  rcases hmulSpec with ⟨hcMulDepth, hcMulErr, hmul⟩
  have hcMulDepth_eq :
      cMulDepth = (10 * (((r + 1) * M ^ d) + 2) : ℕ) := rfl
  have hcMulErr_eq : cMulErr = 8 * rate := rfl
  have htent_bounds : ∀ (q : Fin d) (x : Fin d → ℝ),
      0 ≤ coordinateTentReLUFunction q (center q) (scale q) x ∧
        coordinateTentReLUFunction q (center q) (scale q) x ≤ 1 := by
    intro q x
    constructor
    · unfold coordinateTentReLUFunction relu
      exact le_max_right _ _
    · unfold coordinateTentReLUFunction relu
      apply max_le
      · have hleft : 0 ≤ max (x q - center q) 0 := le_max_right _ _
        have hright : 0 ≤ max (center q - x q) 0 := le_max_right _ _
        have hprod :
            0 ≤ scale q *
              (max (x q - center q) 0 + max (center q - x q) 0) :=
          mul_nonneg (hscale q) (add_nonneg hleft hright)
        linarith
      · norm_num
  have hprefix_bounds : ∀ (k : ℕ), k ≤ d → ∀ x : Fin d → ℝ,
      let Tk := ∏ q : {q : Fin d // q.val < k},
        coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x
      0 ≤ Tk ∧ Tk ≤ 1 := by
    intro k hkd x
    dsimp only
    constructor
    · exact Finset.prod_nonneg (fun q _hq => (htent_bounds q.1 x).1)
    · exact Finset.prod_le_one
        (fun q _hq => (htent_bounds q.1 x).1)
        (fun q _hq => (htent_bounds q.1 x).2)
  have hprefix_succ : ∀ (k : ℕ) (hkd : k < d) (x : Fin d → ℝ),
      (∏ q : {q : Fin d // q.val < k + 1},
          coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x) =
        (∏ q : {q : Fin d // q.val < k},
          coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x) *
          coordinateTentReLUFunction ⟨k, hkd⟩
            (center ⟨k, hkd⟩) (scale ⟨k, hkd⟩) x := by
    intro k hkd x
    let qk : Fin d := ⟨k, hkd⟩
    let f : Fin d → ℝ := fun q ↦
      coordinateTentReLUFunction q (center q) (scale q) x
    let s : Finset (Fin d) := Finset.univ.filter (fun q ↦ q.val < k)
    let s' : Finset (Fin d) := Finset.univ.filter (fun q ↦ q.val < k + 1)
    have hs : ∀ q : Fin d, q ∈ s ↔ q.val < k := by
      intro q
      simp [s]
    have hs' : ∀ q : Fin d, q ∈ s' ↔ q.val < k + 1 := by
      intro q
      simp [s']
    have hqk_notin : qk ∉ s := by simp [s, qk]
    have hsu : s' = insert qk s := by
      ext q
      simp [s, s', qk, Fin.ext_iff]
      omega
    have hleft :
        (∏ q : {q : Fin d // q.val < k + 1}, f q.1) = ∏ q ∈ s', f q := by
      rw [Finset.prod_subtype s' hs' f]
    have hright :
        (∏ q : {q : Fin d // q.val < k}, f q.1) = ∏ q ∈ s, f q := by
      rw [Finset.prod_subtype s hs f]
    rw [hleft, hright, hsu, Finset.prod_insert hqk_notin]
    dsimp [qk, f]
    ring
  have h_step : ∀ (k : ℕ), 1 ≤ k → k < d →
      (∃ D P : ℕ,
        0 < D ∧
        (D : ℝ) ≤ 2 + (k : ℝ) * (2 + cMulDepth) ∧
        P = fullyConnectedReLUParameterCount d D (2 + (k - 1) * (10 + 2)) ∧
        ∃ g : (Fin d → ℝ) → ℝ,
          g ∈ reluNetworkClass d D (2 + (k - 1) * (10 + 2)) P ∧
          ∀ x,
            |g x - (∏ q : {q : Fin d // q.val < k},
              coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x)| ≤
                tentProductRateConstant k * rate) →
      ∃ D P : ℕ,
        0 < D ∧
        (D : ℝ) ≤ 2 + ((k + 1 : ℕ) : ℝ) * (2 + cMulDepth) ∧
        P = fullyConnectedReLUParameterCount d D
          (2 + ((k + 1) - 1) * (10 + 2)) ∧
        ∃ g : (Fin d → ℝ) → ℝ,
          g ∈ reluNetworkClass d D (2 + ((k + 1) - 1) * (10 + 2)) P ∧
          ∀ x,
            |g x - (∏ q : {q : Fin d // q.val < k + 1},
              coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x)| ≤
                tentProductRateConstant (k + 1) * rate := by
    intro k hk1 hkd hprev
    rcases hprev with ⟨Dk, Pk, hDk, hDkBound, hPk, gk, hgk, hgkErr⟩
    let qk : Fin d := ⟨k, hkd⟩
    let Tk : (Fin d → ℝ) → ℝ := fun x ↦
      ∏ q : {q : Fin d // q.val < k},
        coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x
    let t : (Fin d → ℝ) → ℝ := fun x ↦
      coordinateTentReLUFunction qk (center qk) (scale qk) x
    let K : ℝ := tentProductRateConstant k
    let eta : ℝ := K * rate
    let R : ℝ := 1 + eta
    have hK : 0 ≤ K := tentProductRateConstant_nonneg k
    have heta : 0 ≤ eta := mul_nonneg hK hrate_nonneg
    have hR : 0 < R := by dsimp [R]; linarith
    have hR_le : R ≤ 1 + K := by
      dsimp [R, eta]
      have hKr : K * rate ≤ K * 1 := mul_le_mul_of_nonneg_left hrate_le_one hK
      linarith
    have hR_nonneg : 0 ≤ R := hR.le
    have hKone_nonneg : 0 ≤ 1 + K := by linarith
    have hR_sq : R ^ 2 ≤ (1 + K) ^ 2 := by nlinarith
    have htClass :
        t ∈ reluNetworkClass d 2 2 (coordinateTentReLUParameterBound d) := by
      dsimp [t]
      exact coordinateTentReLUFunction_mem_reluNetworkClass_with_parameter_bound
        qk (center qk) (scale qk) (by norm_num) (by norm_num) le_rfl
    have hTkBounds : ∀ x, 0 ≤ Tk x ∧ Tk x ≤ 1 := by
      intro x
      exact hprefix_bounds k (le_of_lt hkd) x
    have htBounds : ∀ x, 0 ≤ t x ∧ t x ≤ 1 := by
      intro x
      exact htent_bounds qk x
    have hgkBound : ∀ x, |gk x| ≤ R := by
      intro x
      have htarget : |Tk x| ≤ 1 := by
        rw [abs_of_nonneg (hTkBounds x).1]
        exact (hTkBounds x).2
      calc
        |gk x| = |(gk x - Tk x) + Tk x| := by congr 1 <;> ring
        _ ≤ |gk x - Tk x| + |Tk x| := abs_add_le _ _
        _ ≤ eta + 1 := add_le_add (by simpa [Tk, eta] using hgkErr x) htarget
        _ = R := by simp [R]; ring
    have htBoundR : ∀ x, |t x| ≤ R := by
      intro x
      rw [abs_of_nonneg (htBounds x).1]
      linarith [(htBounds x).2, heta]
    obtain ⟨D, P, hD, hDBound, hP, g, hg, hgErr⟩ :=
      exists_reluNetworkClass_product_two_fixed_width_from_mul_gadget_depth_sum_bound
        (d := d) (Df := Dk) (Dg := 2)
        (Wf := 2 + (k - 1) * (10 + 2)) (Wg := 2)
        (Pf := Pk) (Pg := coordinateTentReLUParameterBound d) (Wmul := 10)
        hDk (by norm_num) (by omega) (by norm_num) (by norm_num)
        hcMulDepth hcMulErr hmul
        (domain := fun _ : Fin d → ℝ ↦ True)
        (targetF := Tk) (targetG := t) (approxF := gk) (approxG := t)
        (ηf := eta) (ηg := 0) (R := R)
        heta (by norm_num) hR hgk htClass
        (fun x _hx ↦ hgkBound x) (fun x _hx ↦ htBoundR x)
        (fun x _hx ↦ htBoundR x)
        (fun x _hx ↦ by simpa [Tk, eta] using hgkErr x)
        (fun x _hx ↦ by simp) 1 (by norm_num)
    have hwidth :
        (2 + (k - 1) * (10 + 2)) + 2 + 10 =
          2 + ((k + 1) - 1) * (10 + 2) := by
      omega
    have hmaxNat : max Dk 2 ≤ Dk + 2 := by omega
    have hmaxReal : (max Dk 2 : ℝ) ≤ (Dk : ℝ) + 2 := by
      exact_mod_cast hmaxNat
    have hdepth :
        (D : ℝ) ≤ 2 + ((k + 1 : ℕ) : ℝ) * (2 + cMulDepth) := by
      calc
        (D : ℝ) ≤ (max Dk 2 : ℝ) + cMulDepth * (1 : ℝ) := by
          simpa [cMulDepth] using hDBound
        _ ≤ (Dk : ℝ) + 2 + cMulDepth := by nlinarith
        _ ≤ (2 + (k : ℝ) * (2 + cMulDepth)) + 2 + cMulDepth := by
          nlinarith
        _ = 2 + ((k + 1 : ℕ) : ℝ) * (2 + cMulDepth) := by
          push_cast
          ring
    have herror : ∀ x,
        |g x - (∏ q : {q : Fin d // q.val < k + 1},
          coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x)| ≤
            tentProductRateConstant (k + 1) * rate := by
      intro x
      have hraw := hgErr x trivial
      have hmulTerm : cMulErr * R ^ 2 ≤ 8 * (1 + K) ^ 2 * rate := by
        calc
          cMulErr * R ^ 2 = 8 * R ^ 2 * rate := by simp [cMulErr, rate]; ring
          _ ≤ 8 * (1 + K) ^ 2 * rate := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hR_sq (by norm_num)) hrate_nonneg
      have hpropTerm : R * eta ≤ (1 + K) * K * rate := by
        have hRK : R * K ≤ (1 + K) * K :=
          mul_le_mul_of_nonneg_right hR_le hK
        dsimp [eta]
        nlinarith
      rw [hprefix_succ k hkd x]
      calc
        |g x - Tk x * t x| ≤ cMulErr * R ^ 2 * (1 : ℝ).rpow (-2 : ℝ) +
            R * 0 + R * eta := by simpa [Tk, t] using hraw
        _ = cMulErr * R ^ 2 + R * eta := by norm_num
        _ ≤ 8 * (1 + K) ^ 2 * rate + (1 + K) * K * rate :=
          add_le_add hmulTerm hpropTerm
        _ = tentProductRateConstant (k + 1) * rate := by
          simp [tentProductRateConstant, K]
          ring
    refine ⟨D, P, hD, hdepth, ?_, g, ?_, herror⟩
    · simpa [hwidth] using hP
    · simpa [hwidth] using hg
  have h_base :
      ∃ D P : ℕ,
        0 < D ∧
        (D : ℝ) ≤ 2 + (1 : ℝ) * (2 + cMulDepth) ∧
        P = fullyConnectedReLUParameterCount d D (2 + (1 - 1) * (10 + 2)) ∧
        ∃ g : (Fin d → ℝ) → ℝ,
          g ∈ reluNetworkClass d D (2 + (1 - 1) * (10 + 2)) P ∧
          ∀ x,
            |g x - (∏ q : {q : Fin d // q.val < 1},
              coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x)| ≤
                tentProductRateConstant 1 * rate := by
    let q0 : Fin d := ⟨0, hd⟩
    let t : (Fin d → ℝ) → ℝ := fun x ↦
      coordinateTentReLUFunction q0 (center q0) (scale q0) x
    refine ⟨2, fullyConnectedReLUParameterCount d 2 2, by norm_num, ?_, ?_, t, ?_, ?_⟩
    · dsimp [cMulDepth]
      norm_num
      positivity
    · norm_num
    · simpa [t] using
        (coordinateTentReLUFunction_mem_reluNetworkClass_with_parameter_bound
          q0 (center q0) (scale q0) (by norm_num) (by norm_num) le_rfl)
    · intro x
      have hprod :
          (∏ q : {q : Fin d // q.val < 1},
            coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x) = t x := by
        let a : {q : Fin d // q.val < 1} := ⟨q0, by simp [q0]⟩
        have hsub : ∀ b : {q : Fin d // q.val < 1}, b = a := by
          intro b
          apply Subtype.ext
          apply Fin.ext
          omega
        have huniv :
            (Finset.univ : Finset {q : Fin d // q.val < 1}) = {a} := by
          ext b
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
          exact hsub b
        rw [huniv]
        simp [a, t, q0]
      rw [hprod]
      have hnonneg :
          0 ≤ tentProductRateConstant 1 * rate :=
        mul_nonneg (tentProductRateConstant_nonneg 1) hrate_nonneg
      simpa using hnonneg
  have h_ind : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      ∃ D P : ℕ,
        0 < D ∧
        (D : ℝ) ≤ 2 + (k : ℝ) * (2 + cMulDepth) ∧
        P = fullyConnectedReLUParameterCount d D (2 + (k - 1) * (10 + 2)) ∧
        ∃ g : (Fin d → ℝ) → ℝ,
          g ∈ reluNetworkClass d D (2 + (k - 1) * (10 + 2)) P ∧
          ∀ x,
            |g x - (∏ q : {q : Fin d // q.val < k},
              coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x)| ≤
                tentProductRateConstant k * rate := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        intro hk1 hkd
        by_cases hk0 : k = 0
        · subst k
          simpa using h_base
        · have hk1' : 1 ≤ k := by omega
          have hklt : k < d := by omega
          exact h_step k hk1' hklt (ih hk1' (le_of_lt hklt))
  rcases h_ind d hd le_rfl with ⟨D, P, hD, hDBound, hP, g, hg, hgErr⟩
  have hfull : ∀ x : Fin d → ℝ,
      (∏ q : {q : Fin d // q.val < d},
        coordinateTentReLUFunction q.1 (center q.1) (scale q.1) x) =
        axisAlignedBoxTentWeight center scale x := by
    intro x
    unfold axisAlignedBoxTentWeight
    let f : Fin d → ℝ := fun q ↦
      coordinateTentReLUFunction q (center q) (scale q) x
    have hall : ∀ q : Fin d, q ∈ (Finset.univ : Finset (Fin d)) ↔ q.val < d := by
      intro q
      simp [Fin.isLt]
    simpa [f] using (Finset.prod_subtype (Finset.univ : Finset (Fin d)) hall f).symm
  refine ⟨D, P, hD, ?_, ?_, g, ?_, ?_⟩
  · simpa [hcMulDepth_eq] using hDBound
  · simpa using hP
  · simpa using hg
  · intro x
    rw [← hfull x]
    simpa [rate] using hgErr x

/-- Dynamic form of the tensor-tent evaluator.  The `d` geometric coordinates
are read from arbitrary coordinates of a larger state vector, which is the
form needed after the coarse/fine state recursion has selected a center. -/
theorem exists_reluNetworkClass_coordinateReadTentWeight_fixed_width_rate
    {n d r M : ℕ} {beta : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (readIndex : Fin d → Fin n) (scale : Fin d → ℝ)
    (hscale : ∀ q, 0 ≤ scale q) :
    let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    ∃ D P : ℕ,
      0 < D ∧
      (D : ℝ) ≤ 2 + (d : ℝ) * (2 + cMulDepth) ∧
      P = fullyConnectedReLUParameterCount n D Wtent ∧
      ∃ g : (Fin n → ℝ) → ℝ,
        g ∈ reluNetworkClass n D Wtent P ∧
        ∀ y : Fin n → ℝ,
          |g y - axisAlignedBoxTentWeight (fun _ ↦ 0) scale
              (fun q ↦ y (readIndex q))| ≤
            tentProductRateConstant d *
              shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
  rcases exists_reluNetworkClass_axisAlignedBoxTentWeight_fixed_width_rate
      (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one (fun _ ↦ 0) scale hscale with
    ⟨D, P0, hD, hDBound, hP0, g0, hg0, hg0Err⟩
  have hg0' : g0 ∈ reluNetworkClass d D Wtent
      (fullyConnectedReLUParameterCount d D Wtent) := by
    simpa [Wtent, hP0] using hg0
  obtain ⟨N, hNdepth, hNwidth, _hNparam, hNrealize⟩ :=
    exists_exactDepth_fullyConnectedReLUNet_of_mem_reluNetworkClass hg0'
  let Aread : Matrix (Fin d) (Fin n) ℝ :=
    fun q j ↦ if j = readIndex q then 1 else 0
  let bread : Fin d → ℝ := fun _ ↦ 0
  have hread : ∀ y : Fin n → ℝ,
      reluApproxFiniteAffineMap Aread bread y =
        fun q ↦ y (readIndex q) := by
    intro y
    funext q
    simp [reluApproxFiniteAffineMap, Aread, bread]
  let Nread : FullyConnectedReLUNet n :=
    FullyConnectedReLUNet.precomposeAffine N Aread bread
  have hNreadDepth : Nread.depth = D := by
    simpa [Nread, FullyConnectedReLUNet.precomposeAffine] using hNdepth
  have hNreadWidth : Nread.width ≤ Wtent := by
    simpa [Nread, FullyConnectedReLUNet.precomposeAffine] using hNwidth
  have hNreadParam : Nread.parameterCount ≤
      fullyConnectedReLUParameterCount n D Wtent := by
    change fullyConnectedReLUParameterCount n Nread.depth Nread.width ≤
      fullyConnectedReLUParameterCount n D Wtent
    rw [hNreadDepth]
    exact fullyConnectedReLUParameterCount_mono_width n D hNreadWidth
  have hNreadRealize : ∀ y : Fin n → ℝ,
      Nread.realize y =
        N.realize (reluApproxFiniteAffineMap Aread bread y) := by
    intro y
    simpa [Nread] using
      FullyConnectedReLUNet.precomposeAffine_realize N Aread bread y
  refine ⟨D, fullyConnectedReLUParameterCount n D Wtent,
    hD, hDBound, rfl, Nread.realize, ?_, ?_⟩
  · rw [reluNetworkClass]
    refine ⟨Nread, ?_, hNreadDepth.le, hNreadWidth, hNreadParam, fun _ ↦ rfl⟩
    rw [hNreadDepth]
    exact hD
  · intro y
    calc
      |Nread.realize y - axisAlignedBoxTentWeight (fun _ ↦ 0) scale
          (fun q ↦ y (readIndex q))| =
          |g0 (fun q ↦ y (readIndex q)) -
            axisAlignedBoxTentWeight (fun _ ↦ 0) scale
              (fun q ↦ y (readIndex q))| := by
            rw [hNreadRealize y, hread y, hNrealize]
      _ ≤ tentProductRateConstant d *
          shallowReLUResolutionRate M r beta := hg0Err _

/-- The paper-rate tensor-tent network on the same encoded input used by the
terminal Taylor evaluator.  Its coordinate reads are exactly the selected
displacements `x - center`, so the zero-centered tent is the tent centered at
the selected fine-cell center. -/
theorem exists_reluNetworkClass_taylorInputTentWeight_fixed_width_rate
    {d r M : ℕ} {beta : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (scale : Fin d → ℝ) (hscale : ∀ q, 0 ≤ scale q) :
    let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
    let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    ∃ D P : ℕ,
      0 < D ∧
      (D : ℝ) ≤ 2 + (d : ℝ) * (2 + cMulDepth) ∧
      P = fullyConnectedReLUParameterCount n D Wtent ∧
      ∃ g : (Fin n → ℝ) → ℝ,
        g ∈ reluNetworkClass n D Wtent P ∧
        ∀ (x center : Fin d → ℝ)
            (coefficient : TaylorMultiindex r d → ℝ),
          |g (reluApproxTaylorEvaluationInputValue x center coefficient) -
              axisAlignedBoxTentWeight center scale x| ≤
            tentProductRateConstant d *
              shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
  let readIndex : Fin d → Fin n :=
    fun q ↦ reluApproxTaylorEvaluationInputEquivFin d r (.inl q)
  rcases exists_reluNetworkClass_coordinateReadTentWeight_fixed_width_rate
      (n := n) (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one readIndex scale hscale with
    ⟨D, P, hD, hDbound, hP, g, hgClass, hgError⟩
  refine ⟨D, P, hD, hDbound, hP, g, hgClass, ?_⟩
  intro x center coefficient
  have hraw := hgError
    (reluApproxTaylorEvaluationInputValue x center coefficient)
  have hread :
      (fun q ↦ reluApproxTaylorEvaluationInputValue x center coefficient
        (readIndex q)) = fun q ↦ x q - center q := by
    funext q
    simp [readIndex]
  rw [hread, axisAlignedBoxTentWeight_zero_center_difference] at hraw
  exact hraw

/-- A single fixed-width network evaluates the selected Taylor polynomial and
its dynamic tensor-tent weight on their common encoded input, then multiplies
them at the paper rate.  The supplied Taylor propagation constant and target
radius are uniform in `M`; consequently the displayed product-error constant
is uniform as well. -/
theorem exists_reluNetworkClass_weightedTaylorInput_fixed_width_rate
    {d r M : ℕ} {beta Rin Rt K : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (hRin : 0 < Rin) (hRt : 0 ≤ Rt) (hK : 0 ≤ K)
    (hKbound : ∀ e : ℝ, 0 ≤ e → e ≤ 8 →
      finiteCenteredMonomialPolynomialFixedWidthApproxError e Rin 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) ≤ K * e)
    (scale : Fin d → ℝ) (hscale : ∀ q, 0 ≤ scale q) :
    let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
    let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    let Ktent := tentProductRateConstant d
    let Rprod := 1 + Rt + 8 * K + Ktent
    let Kprod := 8 * Rprod ^ 2 + Rprod * Ktent + Rprod * (8 * K)
    ∃ (Wpoly : ℕ) (cPolyDepth : ℝ) (D P : ℕ)
        (g : (Fin n → ℝ) → ℝ),
      0 < Wpoly ∧
      Wpoly = finiteCenteredMonomialPolynomialFixedWidthBound 10
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a ↦ reluApproxTaylorEvaluationDegree a) ∧
      0 < cPolyDepth ∧ 0 < D ∧
      cPolyDepth = 1 +
        (Finset.univ : Finset (TaylorMultiindex r d)).sum
          (fun a ↦
            max 1 (10 * (((r + 1) * M ^ d) + 2) : ℕ) *
              ((reluApproxTaylorEvaluationDegree a : ℝ) + 1)) ∧
      (D : ℝ) ≤ cPolyDepth * 2 +
        (2 + (d : ℝ) * (2 + cMulDepth)) + cMulDepth ∧
      P = fullyConnectedReLUParameterCount n D (Wpoly + Wtent + 10) ∧
      g ∈ reluNetworkClass n D (Wpoly + Wtent + 10) P ∧
      ∀ y : Fin n → ℝ,
        (∀ q, |y q| ≤ Rin) →
        |(∑ a : TaylorMultiindex r d,
            ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
              y (reluApproxTaylorEvaluationCoord a q))| ≤ Rt →
        |g y -
            axisAlignedBoxTentWeight (fun _ ↦ 0) scale
              (fun q ↦ y
                (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))) *
              (∑ a : TaylorMultiindex r d,
                ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
                  y (reluApproxTaylorEvaluationCoord a q))| ≤
          Kprod * shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
  let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
  let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
  let Ktent : ℝ := tentProductRateConstant d
  let Rprod : ℝ := 1 + Rt + 8 * K + Ktent
  let Kprod : ℝ := 8 * Rprod ^ 2 + Rprod * Ktent + Rprod * (8 * K)
  let readIndex : Fin d → Fin n :=
    fun q ↦ reluApproxTaylorEvaluationInputEquivFin d r (.inl q)
  let targetTaylor : (Fin n → ℝ) → ℝ := fun y ↦
    ∑ a : TaylorMultiindex r d,
      ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
        y (reluApproxTaylorEvaluationCoord a q)
  let targetTent : (Fin n → ℝ) → ℝ := fun y ↦
    axisAlignedBoxTentWeight (fun _ ↦ 0) scale (fun q ↦ y (readIndex q))
  let rate : ℝ := shallowReLUResolutionRate M r beta
  let etaTaylor : ℝ := (8 * K) * rate
  let etaTent : ℝ := Ktent * rate
  have hMpos : 0 < M := by omega
  have hrate_pos : 0 < rate := by
    dsimp [rate, shallowReLUResolutionRate]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _
  have hrate_le_one : rate ≤ 1 := by
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hexp : -(2 * ((r : ℝ) + beta)) ≤ 0 := by
      have hr : 0 ≤ (r : ℝ) := by positivity
      nlinarith
    dsimp [rate, shallowReLUResolutionRate]
    exact Real.rpow_le_one_of_one_le_of_nonpos hMone hexp
  have hKtent : 0 ≤ Ktent := by
    exact tentProductRateConstant_nonneg d
  have hRprod : 0 < Rprod := by
    dsimp [Rprod]
    positivity
  have hetaTaylor : 0 ≤ etaTaylor := by
    dsimp [etaTaylor]
    positivity
  have hetaTent : 0 ≤ etaTent := by
    dsimp [etaTent]
    positivity
  have hetaTaylor_le : etaTaylor ≤ 8 * K := by
    dsimp [etaTaylor]
    nlinarith [mul_le_mul_of_nonneg_left hrate_le_one (by positivity : 0 ≤ 8 * K)]
  have hetaTent_le : etaTent ≤ Ktent := by
    dsimp [etaTent]
    nlinarith [mul_le_mul_of_nonneg_left hrate_le_one hKtent]
  rcases exists_reluNetworkClass_taylorEvaluation_fixed_width_rate_of_error_bound
      (d := d) (r := r) (M := M) (beta := beta) (R := Rin) (K := K)
      hd hM hbeta_pos hbeta_le_one hRin hK hKbound with
    ⟨Wpoly, cPolyDepth, Dpoly, Ppoly, gTaylor,
      hWpoly, hWpolyEq, hcPolyDepth, hDpoly, hcPolyDepthEq,
      hDpolyBound, hPpoly, hgTaylor, hgTaylorError⟩
  rcases exists_reluNetworkClass_coordinateReadTentWeight_fixed_width_rate
      (n := n) (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one readIndex scale hscale with
    ⟨Dtent, Ptent, hDtent, hDtentBound, hPtent,
      gTent, hgTent, hgTentError⟩
  have hmulSpec :=
    exists_reluNetworkClass_mul_fixed_width_rate_scaled_family
      (d := d) (r := r) (M := M) (beta := beta)
      hd hM hbeta_pos hbeta_le_one
  dsimp only at hmulSpec
  rcases hmulSpec with ⟨hcMulDepth, hcMulErr, hmul⟩
  have htargetTentBounds : ∀ y, 0 ≤ targetTent y ∧ targetTent y ≤ 1 := by
    intro y
    have hbounds := axisAlignedBoxTentWeight_bounds_and_support
      (fun _ ↦ 0) scale (fun q ↦ y (readIndex q)) hscale
    exact ⟨hbounds.1, hbounds.2.1⟩
  let domain : (Fin n → ℝ) → Prop := fun y ↦
    (∀ q, |y q| ≤ Rin) ∧ |targetTaylor y| ≤ Rt
  have hgTaylorError' : ∀ y, domain y →
      |gTaylor y - targetTaylor y| ≤ etaTaylor := by
    intro y hy
    simpa [targetTaylor, etaTaylor, rate] using hgTaylorError y hy.1
  have hgTentError' : ∀ y, domain y →
      |gTent y - targetTent y| ≤ etaTent := by
    intro y _hy
    simpa [targetTent, etaTent, Ktent, rate] using hgTentError y
  have hgTaylorBound : ∀ y, domain y → |gTaylor y| ≤ Rprod := by
    intro y hy
    calc
      |gTaylor y| = |(gTaylor y - targetTaylor y) + targetTaylor y| := by
        congr 1
        ring
      _ ≤ |gTaylor y - targetTaylor y| + |targetTaylor y| := abs_add_le _ _
      _ ≤ etaTaylor + Rt := add_le_add (hgTaylorError' y hy) hy.2
      _ ≤ Rprod := by
        dsimp [Rprod]
        nlinarith
  have hgTentBound : ∀ y, domain y → |gTent y| ≤ Rprod := by
    intro y hy
    have htargetAbs : |targetTent y| ≤ 1 := by
      rw [abs_of_nonneg (htargetTentBounds y).1]
      exact (htargetTentBounds y).2
    calc
      |gTent y| = |(gTent y - targetTent y) + targetTent y| := by
        congr 1
        ring
      _ ≤ |gTent y - targetTent y| + |targetTent y| := abs_add_le _ _
      _ ≤ etaTent + 1 := add_le_add (hgTentError' y hy) htargetAbs
      _ ≤ Rprod := by
        dsimp [Rprod]
        nlinarith
  have htargetTentBound : ∀ y, domain y → |targetTent y| ≤ Rprod := by
    intro y _hy
    rw [abs_of_nonneg (htargetTentBounds y).1]
    dsimp [Rprod]
    nlinarith [(htargetTentBounds y).2]
  obtain ⟨D, P, hD, hDbound, hP, g, hg, hgError⟩ :=
    exists_reluNetworkClass_product_two_fixed_width_from_mul_gadget_depth_sum_bound
      (d := n) (Df := Dpoly) (Dg := Dtent)
      (Wf := Wpoly) (Wg := Wtent) (Pf := Ppoly) (Pg := Ptent)
      (Wmul := 10) hDpoly hDtent hWpoly (by
        dsimp [Wtent]
        omega) (by norm_num) hcMulDepth hcMulErr hmul
      (domain := domain) (targetF := targetTaylor) (targetG := targetTent)
      (approxF := gTaylor) (approxG := gTent)
      (ηf := etaTaylor) (ηg := etaTent) (R := Rprod)
      hetaTaylor hetaTent hRprod hgTaylor hgTent
      hgTaylorBound hgTentBound htargetTentBound
      hgTaylorError' hgTentError' 1 (by norm_num)
  have hdepth : (D : ℝ) ≤ cPolyDepth * 2 +
      (2 + (d : ℝ) * (2 + cMulDepth)) + cMulDepth := by
    have hmaxNat : max Dpoly Dtent ≤ Dpoly + Dtent := by omega
    have hmaxReal : (max Dpoly Dtent : ℝ) ≤ (Dpoly : ℝ) + Dtent := by
      exact_mod_cast hmaxNat
    calc
      (D : ℝ) ≤ (max Dpoly Dtent : ℝ) + cMulDepth * (1 : ℝ) := by
        simpa [cMulDepth] using hDbound
      _ ≤ (Dpoly : ℝ) + Dtent + cMulDepth := by nlinarith
      _ ≤ cPolyDepth * 2 +
          (2 + (d : ℝ) * (2 + cMulDepth)) + cMulDepth := by
        nlinarith
  refine ⟨Wpoly, cPolyDepth, D, P, g, hWpoly, hWpolyEq, hcPolyDepth, hD,
    hcPolyDepthEq, hdepth, ?_, ?_, ?_⟩
  · simpa [n, Wtent] using hP
  · simpa [n, Wtent] using hg
  · intro y hy htarget
    have hyDomain : domain y := ⟨hy, by simpa [targetTaylor] using htarget⟩
    have hraw := hgError y hyDomain
    calc
      |g y - targetTent y * targetTaylor y| =
          |g y - targetTaylor y * targetTent y| := by
            congr 2
            ring
      _ ≤ (8 * rate) * Rprod ^ 2 * (1 : ℝ).rpow (-2 : ℝ) +
          Rprod * etaTent + Rprod * etaTaylor := by
            simpa [cMulDepth, targetTaylor, targetTent, readIndex, rate,
              etaTaylor, etaTent, Ktent] using hraw
      _ = Kprod * rate := by
        norm_num
        dsimp [Kprod, etaTaylor, etaTent]
        ring

/-- Concrete-network form of the weighted terminal Taylor evaluator.  This is
the form needed when the evaluator is appended to a coarse/fine macro program. -/
theorem exists_fullyConnectedReLUNet_weightedTaylorInput_fixed_width_rate
    {d r M : ℕ} {beta Rin Rt K : ℝ}
    (hd : 0 < d) (hM : 2 ≤ M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1)
    (hRin : 0 < Rin) (hRt : 0 ≤ Rt) (hK : 0 ≤ K)
    (hKbound : ∀ e : ℝ, 0 ≤ e → e ≤ 8 →
      finiteCenteredMonomialPolynomialFixedWidthApproxError e Rin 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ ↦ (1 : ℝ))
          (fun a ↦ reluApproxTaylorEvaluationDegree a) ≤ K * e)
    (scale : Fin d → ℝ) (hscale : ∀ q, 0 ≤ scale q) :
    let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
    let Wtent : ℕ := 2 + (d - 1) * (10 + 2)
    let cMulDepth : ℝ := (10 * (((r + 1) * M ^ d) + 2) : ℕ)
    let Ktent := tentProductRateConstant d
    let Rprod := 1 + Rt + 8 * K + Ktent
    let Kprod := 8 * Rprod ^ 2 + Rprod * Ktent + Rprod * (8 * K)
    ∃ (Wpoly : ℕ) (cPolyDepth : ℝ) (D P : ℕ)
        (N : FullyConnectedReLUNet n),
      0 < Wpoly ∧
      Wpoly = finiteCenteredMonomialPolynomialFixedWidthBound 10
        (Finset.univ : Finset (TaylorMultiindex r d))
        (fun a ↦ reluApproxTaylorEvaluationDegree a) ∧
      0 < cPolyDepth ∧ 0 < D ∧
      cPolyDepth = 1 +
        (Finset.univ : Finset (TaylorMultiindex r d)).sum
          (fun a ↦
            max 1 (10 * (((r + 1) * M ^ d) + 2) : ℕ) *
              ((reluApproxTaylorEvaluationDegree a : ℝ) + 1)) ∧
      (D : ℝ) ≤ cPolyDepth * 2 +
        (2 + (d : ℝ) * (2 + cMulDepth)) + cMulDepth ∧
      N.depth ≤ D ∧ N.width ≤ Wpoly + Wtent + 10 ∧
      N.parameterCount ≤ P ∧
      P = fullyConnectedReLUParameterCount n D (Wpoly + Wtent + 10) ∧
      ∀ y : Fin n → ℝ,
        (∀ q, |y q| ≤ Rin) →
        |(∑ a : TaylorMultiindex r d,
            ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
              y (reluApproxTaylorEvaluationCoord a q))| ≤ Rt →
        |N.realize y -
            axisAlignedBoxTentWeight (fun _ ↦ 0) scale
              (fun q ↦ y
                (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))) *
              (∑ a : TaylorMultiindex r d,
                ∏ q : Fin (reluApproxTaylorEvaluationDegree a),
                  y (reluApproxTaylorEvaluationCoord a q))| ≤
          Kprod * shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  rcases exists_reluNetworkClass_weightedTaylorInput_fixed_width_rate
      (d := d) (r := r) (M := M) (beta := beta)
      (Rin := Rin) (Rt := Rt) (K := K)
      hd hM hbeta_pos hbeta_le_one hRin hRt hK hKbound scale hscale with
    ⟨Wpoly, cPolyDepth, D, P, g, hWpoly, hWpolyEq, hcPolyDepth, hD,
      hcPolyDepthEq, hDbound, hP, hgClass, hgError⟩
  change ∃ N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)),
      0 < N.depth ∧ N.depth ≤ D ∧
      N.width ≤ Wpoly + (2 + (d - 1) * (10 + 2)) + 10 ∧
      N.parameterCount ≤ P ∧ ∀ y, g y = N.realize y at hgClass
  rcases hgClass with ⟨N, hNdepth, hNdepthLe, hNwidth, hNparam, hgN⟩
  refine ⟨Wpoly, cPolyDepth, D, P, N, hWpoly, hWpolyEq, hcPolyDepth, hD,
    hcPolyDepthEq, hDbound, hNdepthLe, hNwidth, hNparam, hP, ?_⟩
  intro y hy htarget
  simpa [hgN y] using hgError y hy htarget

abbrev weightedTaylorDepthFactor (d r : Nat) : Nat :=
  let card := Fintype.card (TaylorMultiindex r d)
  let polyTerm := 10 * (r + 3) * (r + 2)
  let polyFactor := 1 + card * polyTerm
  let mulFactor := 10 * (r + 3)
  2 * polyFactor + 2 + d * (2 + mulFactor) + mulFactor

abbrev weightedTaylorWidthBound (d r : Nat) : Nat :=
  finiteCenteredMonomialPolynomialFixedWidthBound 10
      (Finset.univ : Finset (TaylorMultiindex r d))
      (fun a => reluApproxTaylorEvaluationDegree a) +
    (2 + (d - 1) * (10 + 2)) + 10

set_option maxHeartbeats 2000000 in
theorem exists_fullyConnectedReLUNet_weightedTaylorInput_fixed_width_rate_uniformResource
    {d r M : Nat} {beta Rin Rt K : Real}
    (hd : 0 < d) (hM : 2 <= M)
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta <= 1)
    (hRin : 0 < Rin) (hRt : 0 <= Rt) (hK : 0 <= K)
    (hKbound : forall e : Real, 0 <= e -> e <= 8 ->
      finiteCenteredMonomialPolynomialFixedWidthApproxError e Rin 1
          (Finset.univ : Finset (TaylorMultiindex r d)) (fun _ => (1 : Real))
          (fun a => reluApproxTaylorEvaluationDegree a) <= K * e)
    (scale : Fin d -> Real) (hscale : forall q, 0 <= scale q) :
    let n := Fintype.card (ReLUApproxTaylorEvaluationInput d r)
    let Ktent := tentProductRateConstant d
    let Rprod := 1 + Rt + 8 * K + Ktent
    let Kprod := 8 * Rprod ^ 2 + Rprod * Ktent + Rprod * (8 * K)
    exists N : FullyConnectedReLUNet n,
      N.depth <= weightedTaylorDepthFactor d r * M ^ d /\
      N.width <= weightedTaylorWidthBound d r /\
      forall y : Fin n -> Real,
        (forall q, |y q| <= Rin) ->
        |(Finset.univ.sum fun a : TaylorMultiindex r d =>
            Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
              y (reluApproxTaylorEvaluationCoord a q))| <= Rt ->
        |N.realize y -
            axisAlignedBoxTentWeight (fun _ => 0) scale
              (fun q => y
                (reluApproxTaylorEvaluationInputEquivFin d r (.inl q))) *
              (Finset.univ.sum fun a : TaylorMultiindex r d =>
                Finset.univ.prod fun q : Fin (reluApproxTaylorEvaluationDegree a) =>
                  y (reluApproxTaylorEvaluationCoord a q))| <=
          Kprod * shallowReLUResolutionRate M r beta := by
  classical
  dsimp only
  obtain ⟨Wpoly, cPolyDepth, D, _P, N, _hWpoly, hWpolyEq,
      _hcPolyDepth, _hD, hcPolyDepthEq, hDbound, hNdepth, hNwidth,
      _hNparam, _hP, hNerror⟩ :=
    exists_fullyConnectedReLUNet_weightedTaylorInput_fixed_width_rate
      hd hM hbeta_pos hbeta_le_one hRin hRt hK hKbound scale hscale
  let T : Nat := M ^ d
  have hMpos : 0 < M := by omega
  have hTpos : 0 < T := by
    dsimp [T]
    exact Nat.pow_pos hMpos
  have hTone : 1 <= T := hTpos
  let mulFactor : Nat := 10 * (r + 3)
  let polyTerm : Nat := mulFactor * (r + 2)
  let card : Nat := Fintype.card (TaylorMultiindex r d)
  let polyFactor : Nat := 1 + card * polyTerm
  have hrawMul : 10 * ((r + 1) * T + 2) <= mulFactor * T := by
    have htwo : 2 <= 2 * T := by omega
    dsimp [mulFactor]
    calc
      10 * ((r + 1) * T + 2) <=
          10 * ((r + 1) * T + 2 * T) := Nat.mul_le_mul_left 10 (Nat.add_le_add_left htwo _)
      _ = 10 * (r + 3) * T := by ring
  have hrawMulReal :
      ((10 * ((r + 1) * T + 2) : Nat) : Real) <=
        (mulFactor : Real) * (T : Real) := by
    exact_mod_cast hrawMul
  have hrawMulOne : 1 <= 10 * ((r + 1) * T + 2) := by omega
  have hterm : forall a : TaylorMultiindex r d,
      ((max 1 (10 * ((r + 1) * T + 2)) : Nat) : Real) *
          ((reluApproxTaylorEvaluationDegree a : Real) + 1) <=
        (polyTerm : Real) * (T : Real) := by
    intro a
    have hmaxNat : max 1 (10 * ((r + 1) * T + 2)) <= mulFactor * T :=
      max_le (le_trans hrawMulOne hrawMul) hrawMul
    have hmax : ((max 1 (10 * ((r + 1) * T + 2)) : Nat) : Real) <=
        (mulFactor : Real) * (T : Real) := by
      exact_mod_cast hmaxNat
    have hdegreeNat : reluApproxTaylorEvaluationDegree a + 1 <= r + 2 := by
      unfold reluApproxTaylorEvaluationDegree
      omega
    have hdegree : (reluApproxTaylorEvaluationDegree a : Real) + 1 <=
        (r + 2 : Nat) := by exact_mod_cast hdegreeNat
    have hdegreeNonneg : 0 <= (reluApproxTaylorEvaluationDegree a : Real) + 1 := by
      positivity
    calc
      ((max 1 (10 * ((r + 1) * T + 2)) : Nat) : Real) *
          ((reluApproxTaylorEvaluationDegree a : Real) + 1) <=
          ((mulFactor : Real) * (T : Real)) * (r + 2 : Nat) := by
            exact mul_le_mul hmax hdegree hdegreeNonneg (by positivity)
      _ = (polyTerm : Real) * (T : Real) := by
        dsimp [polyTerm]
        push_cast
        ring
  have hsum :
      (Finset.univ : Finset (TaylorMultiindex r d)).sum
          (fun a => ((max 1 (10 * ((r + 1) * T + 2)) : Nat) : Real) *
              ((reluApproxTaylorEvaluationDegree a : Real) + 1)) <=
        (card : Real) * ((polyTerm : Real) * (T : Real)) := by
    calc
      _ <= (Finset.univ : Finset (TaylorMultiindex r d)).sum
          (fun _ => (polyTerm : Real) * (T : Real)) :=
        Finset.sum_le_sum fun a _ => hterm a
      _ = (card : Real) * ((polyTerm : Real) * (T : Real)) := by
        simp [card]
  have hcPolyBound : cPolyDepth <= (polyFactor : Real) * (T : Real) := by
    rw [hcPolyDepthEq]
    have hOneReal : (1 : Real) <= (T : Real) := by exact_mod_cast hTone
    calc
      1 + (Finset.univ : Finset (TaylorMultiindex r d)).sum
          (fun a => ((max 1 (10 * (((r + 1) * M ^ d) + 2)) : Nat) : Real) *
              ((reluApproxTaylorEvaluationDegree a : Real) + 1)) <=
          (T : Real) + (card : Real) * ((polyTerm : Real) * (T : Real)) := by
            dsimp [T] at hsum
            exact add_le_add hOneReal hsum
      _ = (polyFactor : Real) * (T : Real) := by
        dsimp [polyFactor]
        push_cast
        ring
  have hmulDepth :
      ((10 * (((r + 1) * M ^ d) + 2) : Nat) : Real) <=
        (mulFactor : Real) * (T : Real) := by
    simpa [T] using hrawMulReal
  have hTwoReal : (2 : Real) <= 2 * (T : Real) := by
    have : (1 : Real) <= (T : Real) := by exact_mod_cast hTone
    linarith
  have hDreal : (D : Real) <=
      (weightedTaylorDepthFactor d r : Real) * (T : Real) := by
    calc
      (D : Real) <= cPolyDepth * 2 +
          (2 + (d : Real) *
            (2 + (10 * (((r + 1) * M ^ d) + 2) : Nat))) +
          (10 * (((r + 1) * M ^ d) + 2) : Nat) := hDbound
      _ <= ((polyFactor : Real) * (T : Real)) * 2 +
          (2 * (T : Real) + (d : Real) *
            (2 * (T : Real) + (mulFactor : Real) * (T : Real))) +
          (mulFactor : Real) * (T : Real) := by
            gcongr
      _ = (weightedTaylorDepthFactor d r : Real) * (T : Real) := by
        dsimp [weightedTaylorDepthFactor, polyFactor, polyTerm,
          mulFactor, card]
        push_cast
        ring
  have hDnat : D <= weightedTaylorDepthFactor d r * T := by
    exact_mod_cast hDreal
  refine ⟨N, le_trans hNdepth hDnat, ?_, hNerror⟩
  simpa [weightedTaylorWidthBound, hWpolyEq] using hNwidth


private theorem reluApproxFineMachineStateValue_eq_sumElim
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxFineMachineStateValue x center coefficient tail
        selectedCenter selectedCoefficient =
      Sum.elim (reluApproxTaylorMachineState x center coefficient tail)
        (Sum.elim
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient)
          (fun _ => 0)) := by
  funext z
  rcases z with z | (z | w) <;> rfl

/-- The semantic complete fine-machine state is exactly the vector-box state
obtained from the corresponding current and selected accumulator registers. -/
private theorem reluApproxFineScanStateValue_equiv_machine
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    (fun z => reluApproxFineScanStateValue x
      (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
        (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
      (reluApproxFineMachineEquivScanState d r z)) =
      reluApproxFineMachineStateValue x center coefficient tail
        selectedCenter selectedCoefficient := by
  funext z
  rcases z with ((q | q) | (a | a)) | ((q | a) | w) <;> rfl

/-- The concrete finite vector used to start a fine pass is the canonical
finite indexing of its complete semantic machine state. -/
private theorem reluApproxVectorBoxScanState_fineMachineEquiv
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxVectorBoxScanState x (fun k =>
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
          ((reluApproxFineAccumulatorEquivFin d r).symm k)) =
      fun i => reluApproxFineMachineStateValue x center coefficient tail
        selectedCenter selectedCoefficient
        ((reluApproxFineMachineEquivFin d r).symm i) := by
  let acc : ReLUApproxFineAccumulator d r -> Real :=
    Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
      (reluApproxSelectedTaylorState selectedCenter selectedCoefficient)
  funext i
  let z := (reluApproxFineMachineEquivFin d r).symm i
  have hscan := congrFun
    (reluApproxVectorBoxScanState_fineEquiv x acc)
    (reluApproxFineMachineEquivScanState d r z)
  calc
    reluApproxVectorBoxScanState x (fun k =>
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
          ((reluApproxFineAccumulatorEquivFin d r).symm k)) i =
        reluApproxFineScanStateValue x acc
          (reluApproxFineMachineEquivScanState d r z) := by
            simpa [acc, z, reluApproxFineMachineEquivFin] using hscan
    _ = reluApproxFineMachineStateValue x center coefficient tail
          selectedCenter selectedCoefficient z := by
            exact congrFun
              (reluApproxFineScanStateValue_equiv_machine x center coefficient tail
                selectedCenter selectedCoefficient) z
    _ = reluApproxFineMachineStateValue x center coefficient tail
          selectedCenter selectedCoefficient
          ((reluApproxFineMachineEquivFin d r).symm i) := rfl

/-- Finite index of a current-center register. -/
private noncomputable def reluApproxFineCurrentCenterIndex (d r : Nat) (q : Fin d) :
    Fin (Fintype.card (ReLUApproxFineAccumulator d r)) :=
  reluApproxFineAccumulatorEquivFin d r
    (reluApproxFineCurrentCenterRegister q)

/-- Finite source map for the concrete affine payload reader. -/
private noncomputable def reluApproxFineSelectionSourceFin (d r : Nat) :
    Fin (Fintype.card (ReLUApproxFineAccumulator d r)) →
      Fin (Fintype.card (ReLUApproxFineAccumulator d r)) :=
  fun k => reluApproxFineAccumulatorEquivFin d r
    (reluApproxFineSelectionSource
      ((reluApproxFineAccumulatorEquivFin d r).symm k))

/-- Finite gain vector for the concrete affine payload reader. -/
private noncomputable def reluApproxFineSelectionGainFin (d r : Nat) :
    Fin (Fintype.card (ReLUApproxFineAccumulator d r)) → Real :=
  fun k => reluApproxFineSelectionGain
    ((reluApproxFineAccumulatorEquivFin d r).symm k)

/-- The concrete finite payload reader agrees with the typed fine-selection
payload coordinate by coordinate. -/
private theorem reluApproxFineSelectionPayloadFin_exact {d r : Nat}
    (acc : ReLUApproxFineAccumulator d r → Real)
    (k : Fin (Fintype.card (ReLUApproxFineAccumulator d r))) :
    reluApproxFineSelectionGainFin d r k *
        acc ((reluApproxFineAccumulatorEquivFin d r).symm
          (reluApproxFineSelectionSourceFin d r k)) =
      reluApproxFineSelectionPayload acc
        ((reluApproxFineAccumulatorEquivFin d r).symm k) := by
  simp [reluApproxFineSelectionGainFin,
    reluApproxFineSelectionSourceFin,
    reluApproxFineSelectionPayload]

/-- The concrete finite current-center index reads the typed accumulator. -/
private theorem reluApproxFineCurrentCenterIndex_exact {d r : Nat}
    (acc : ReLUApproxFineAccumulator d r → Real) (q : Fin d) :
    acc ((reluApproxFineAccumulatorEquivFin d r).symm
        (reluApproxFineCurrentCenterIndex d r q)) =
      acc (reluApproxFineCurrentCenterRegister q) := by
  simp [reluApproxFineCurrentCenterIndex]

/-- Four affine/ReLU layers implementing one fine-box selection cycle on the
canonical finite register vector. -/
private noncomputable def reluApproxFineSelectionCycle {d r : Nat}
    (R radius : Real) (x : Fin d → Real)
    (acc : ReLUApproxFineAccumulator d r → Real) :
    Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) → Real :=
  let m := Fintype.card (ReLUApproxFineAccumulator d r)
  let e := reluApproxFineAccumulatorEquivFin d r
  let accFin : Fin m → Real := fun k => acc (e.symm k)
  let centerIndex : Fin d → Fin m := reluApproxFineCurrentCenterIndex d r
  let source : Fin m → Fin m := reluApproxFineSelectionSourceFin d r
  let gain : Fin m → Real := reluApproxFineSelectionGainFin d r
  let lowerArg := reluApproxVectorBoxScanCenteredLowerArg centerIndex
  let upperArg := reluApproxVectorBoxScanCenteredUpperArg centerIndex
  let payloadArg := reluApproxVectorBoxScanAccumulatorPayloadArg source gain
  let faceBias : Fin d → Real := fun _ => R⁻¹ - radius
  let payloadBias : Fin m → Real := fun _ => 0
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
            faceBias faceBias payloadBias)
          (reluApproxVectorBoxScanState x accFin) j))) i))

/-- Two-macro feature schedule for one state-dependent fine-box test. -/
private noncomputable def reluApproxFineSelectionFeatureSchedule (d r : Nat)
    (R : Real) :
    Fin 2 -> Matrix
      (Fin (reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)))) Real :=
  fun k => if k.val = 0 then
    reluApproxVectorBoxScanAffineLoadFeatureMatrix
      (reluApproxVectorBoxScanCenteredLowerArg
        (reluApproxFineCurrentCenterIndex d r))
      (reluApproxVectorBoxScanCenteredUpperArg
        (reluApproxFineCurrentCenterIndex d r))
      (reluApproxVectorBoxScanAccumulatorPayloadArg
        (reluApproxFineSelectionSourceFin d r)
        (reluApproxFineSelectionGainFin d r))
  else
    reluApproxVectorBoxScanAccFeatureMatrix d
      (Fintype.card (ReLUApproxFineAccumulator d r)) R

/-- Bias schedule for one state-dependent fine-box test. -/
private noncomputable def reluApproxFineSelectionFeatureBiasSchedule (d r : Nat)
    (R radius : Real) :
    Fin 2 -> Fin (reluApproxVectorBoxScanFeatureSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  fun k => if k.val = 0 then
    reluApproxVectorBoxScanAffineLoadFeatureBias
      (fun _ => R⁻¹ - radius) (fun _ => R⁻¹ - radius) (fun _ => 0)
  else
    fun _ => 0

/-- Update matrices for one state-dependent fine-box test. -/
private noncomputable def reluApproxFineSelectionUpdateSchedule (d r : Nat) :
    Fin 2 -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))))
      (Fin (reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)))) Real :=
  fun k => if k.val = 0 then
    reluApproxVectorBoxScanLoadUpdateMatrix d
      (Fintype.card (ReLUApproxFineAccumulator d r))
  else
    reluApproxVectorBoxScanAccUpdateMatrix d
      (Fintype.card (ReLUApproxFineAccumulator d r))

/-- Both update biases in one fine-box test vanish. -/
private noncomputable def reluApproxFineSelectionUpdateBiasSchedule (d r : Nat) :
    Fin 2 -> Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  fun _ _ => 0

/-- Executing the two concrete selector macros from a canonical scan state is
definitionally the nested four-layer selector cycle. -/
private theorem reluApproxFineSelectionSchedule_exact {d r : Nat}
    (R radius : Real) (x : Fin d -> Real)
    (acc : ReLUApproxFineAccumulator d r -> Real) :
    reluApproxMacroRecursionFrom
      (reluApproxFineSelectionFeatureSchedule d r R)
      (reluApproxFineSelectionFeatureBiasSchedule d r R radius)
      (reluApproxFineSelectionUpdateSchedule d r)
      (reluApproxFineSelectionUpdateBiasSchedule d r)
      (reluApproxVectorBoxScanState x (fun k =>
        acc ((reluApproxFineAccumulatorEquivFin d r).symm k))) 2 =
      reluApproxFineSelectionCycle R radius x acc := by
  funext i
  simp [reluApproxMacroRecursionFrom,
    reluApproxFineSelectionFeatureSchedule,
    reluApproxFineSelectionFeatureBiasSchedule,
    reluApproxFineSelectionUpdateSchedule,
    reluApproxFineSelectionUpdateBiasSchedule,
    reluApproxFineSelectionCycle]
  rfl

/-- Exact semantic law for one concrete fine-box selection cycle. -/
private theorem reluApproxFineSelectionCycle_exact {d r : Nat}
    (R radius : Real) (x : Fin d → Real)
    (acc : ReLUApproxFineAccumulator d r → Real) :
    reluApproxFineSelectionCycle R radius x acc =
      reluApproxVectorBoxScanState x (fun k =>
        reluApproxFineSelectionAccumulator R radius x acc
          ((reluApproxFineAccumulatorEquivFin d r).symm k)) := by
  classical
  let m := Fintype.card (ReLUApproxFineAccumulator d r)
  let e := reluApproxFineAccumulatorEquivFin d r
  let accFin : Fin m → Real := fun k => acc (e.symm k)
  let centerIndex : Fin d → Fin m := reluApproxFineCurrentCenterIndex d r
  let source : Fin m → Fin m := reluApproxFineSelectionSourceFin d r
  let gain : Fin m → Real := reluApproxFineSelectionGainFin d r
  let lower : Fin d → Real := fun q =>
    acc (reluApproxFineCurrentCenterRegister q) - radius
  let upper : Fin d → Real := fun q =>
    acc (reluApproxFineCurrentCenterRegister q) + radius
  let payload : Fin m → Real := fun k =>
    reluApproxFineSelectionPayload acc (e.symm k)
  have hlower : ∀ q,
      reluApproxFiniteAffineMap
          (reluApproxVectorBoxScanCenteredLowerArg centerIndex)
          (fun _ ↦ R⁻¹ - radius)
          (reluApproxVectorBoxScanState x accFin) q =
        lower q + R⁻¹ - x q := by
    intro q
    simpa [accFin, centerIndex, lower, e,
      reluApproxFineCurrentCenterIndex] using
      (reluApproxVectorBoxScanCenteredLowerArg_exact
        R radius centerIndex x accFin q)
  have hupper : ∀ q,
      reluApproxFiniteAffineMap
          (reluApproxVectorBoxScanCenteredUpperArg centerIndex)
          (fun _ ↦ R⁻¹ - radius)
          (reluApproxVectorBoxScanState x accFin) q =
        x q - upper q + R⁻¹ := by
    intro q
    simpa [accFin, centerIndex, upper, e,
      reluApproxFineCurrentCenterIndex] using
      (reluApproxVectorBoxScanCenteredUpperArg_exact
        R radius centerIndex x accFin q)
  have hpayload : ∀ k,
      reluApproxFiniteAffineMap
          (reluApproxVectorBoxScanAccumulatorPayloadArg source gain)
          (fun _ ↦ 0) (reluApproxVectorBoxScanState x accFin) k =
        payload k := by
    intro k
    rw [reluApproxVectorBoxScanAccumulatorPayloadArg_exact]
    exact reluApproxFineSelectionPayloadFin_exact acc k
  have hcycle := reluApproxVectorBoxScanAffineCycle_exact
    R lower upper x payload accFin
    (reluApproxVectorBoxScanCenteredLowerArg centerIndex)
    (reluApproxVectorBoxScanCenteredUpperArg centerIndex)
    (reluApproxVectorBoxScanAccumulatorPayloadArg source gain)
    (fun _ ↦ R⁻¹ - radius) (fun _ ↦ R⁻¹ - radius)
    (fun _ ↦ 0) hlower hupper hpayload
  simpa [reluApproxFineSelectionCycle, m, e, accFin, centerIndex,
    source, gain, lower, upper, payload,
    reluApproxFineSelectionAccumulator] using hcycle

/-- Reindexed to the complete typed fine-machine state, one concrete box cycle
preserves the current Taylor state and performs exactly the semantic selected
register update. -/
private theorem reluApproxFineSelectionCycle_machine_exact {d r : Nat}
    (R radius : Real) (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    (fun z => reluApproxFineSelectionCycle R radius x
      (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
        (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
      (reluApproxFineMachineEquivFin d r z)) =
    reluApproxFineMachineStateValue x center coefficient tail
      (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
      (reluApproxFineSelectedCoefficientStep R radius x center coefficient
        selectedCoefficient) := by
  let acc : ReLUApproxFineAccumulator d r -> Real :=
    Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
      (reluApproxSelectedTaylorState selectedCenter selectedCoefficient)
  funext z
  have hcycle := congrFun (reluApproxFineSelectionCycle_exact R radius x acc)
    (reluApproxFineMachineEquivFin d r z)
  rw [hcycle]
  have hscan := congrFun
    (reluApproxVectorBoxScanState_fineEquiv x
      (reluApproxFineSelectionAccumulator R radius x acc))
    (reluApproxFineMachineEquivScanState d r z)
  calc
    reluApproxVectorBoxScanState x (fun k =>
          reluApproxFineSelectionAccumulator R radius x acc
            ((reluApproxFineAccumulatorEquivFin d r).symm k))
        (reluApproxFineMachineEquivFin d r z) =
        reluApproxFineScanStateValue x
          (reluApproxFineSelectionAccumulator R radius x acc)
          (reluApproxFineMachineEquivScanState d r z) := by
            simpa [reluApproxFineMachineEquivFin] using hscan
    _ = reluApproxFineScanStateValue x
          (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
            (reluApproxSelectedTaylorState
              (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
              (reluApproxFineSelectedCoefficientStep R radius x center coefficient
                selectedCoefficient)))
          (reluApproxFineMachineEquivScanState d r z) := by
            rw [show acc = Sum.elim
              (reluApproxTaylorPayloadState center coefficient tail)
              (reluApproxSelectedTaylorState selectedCenter selectedCoefficient) by rfl]
            rw [reluApproxFineSelectionAccumulator_state]
    _ = reluApproxFineMachineStateValue x center coefficient tail
          (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
          (reluApproxFineSelectedCoefficientStep R radius x center coefficient
            selectedCoefficient) z := by
            exact congrFun
              (reluApproxFineScanStateValue_equiv_machine x center coefficient tail
                (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
                (reluApproxFineSelectedCoefficientStep R radius x center coefficient
                  selectedCoefficient)) z

/-- Extend an affine state update by the identity on a persistent suffix. -/
private noncomputable def reluApproxAffineMapWithPersistentWork {S W : Type*}
    [DecidableEq W]
    (P : S -> S -> Real) : (S ⊕ W) -> (S ⊕ W) -> Real
  | .inl i, .inl j => P i j
  | .inr i, .inr j => if j = i then 1 else 0
  | _, _ => 0

/-- Extend an affine bias by zero on a persistent suffix. -/
private noncomputable def reluApproxBiasWithPersistentWork {S W : Type*}
    (bias : S -> Real) : S ⊕ W -> Real
  | .inl i => bias i
  | .inr _ => 0

/-- Extend decoded-digit coefficients by zero on a persistent suffix. -/
private noncomputable def reluApproxDigitCoeffWithPersistentWork
    {S W A : Type*} (digitCoeff : S -> A -> Real) :
    (S ⊕ W) -> A -> Real
  | .inl i => digitCoeff i
  | .inr _ => fun _ => 0

/-- One prescribed-digit Taylor update preserves every persistent register. -/
private theorem reluApproxParallelFloorDigitState_withPersistentWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    [DecidableEq W]
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (digit : A -> Nat)
    (u : S -> Real) (work : W -> Real) :
    reluApproxParallelFloorDigitState
      (reluApproxAffineMapWithPersistentWork P)
      (reluApproxBiasWithPersistentWork (W := W) bias)
      (reluApproxDigitCoeffWithPersistentWork (W := W) digitCoeff)
      digit (Sum.elim u work) =
        Sum.elim
          (reluApproxParallelFloorDigitState P bias digitCoeff digit u)
          work := by
  funext z
  rcases z with i | w
  · simp [reluApproxParallelFloorDigitState,
      reluApproxTypedAffineMap,
      reluApproxAffineMapWithPersistentWork,
      reluApproxBiasWithPersistentWork,
      reluApproxDigitCoeffWithPersistentWork,
      Fintype.sum_sum_type]
  · simp [reluApproxParallelFloorDigitState,
      reluApproxTypedAffineMap,
      reluApproxAffineMapWithPersistentWork,
      reluApproxBiasWithPersistentWork,
      reluApproxDigitCoeffWithPersistentWork,
      Fintype.sum_sum_type]

/-- A prescribed decoded digit simultaneously advances the current Taylor
state and leaves both the selected output registers and the fine-scan scratch
space unchanged. -/
private theorem reluApproxTaylorMachineDigitState_withFineRegisters_exact
    {d r : Nat}
    (base : Real) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : TaylorMultiindex r d -> Nat)
    (correction : TaylorMultiindex r d -> Int)
    (hdigit : forall a, (digit a : Int) = correction a + (shift : Int))
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxParallelFloorDigitState
      (reluApproxAffineMapWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineMatrix base trans))
      (reluApproxBiasWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineBias step shift scale))
      (reluApproxDigitCoeffWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineDigitCoeff scale))
      digit
      (reluApproxFineMachineStateValue x center coefficient tail
        selectedCenter selectedCoefficient) =
    reluApproxFineMachineStateValue x (fun q => center q + step q)
      (fun a => Finset.univ.sum (fun b => trans a b * coefficient b) +
        (correction a : Real) * scale a)
      (fun a => base * tail a - (digit a : Real))
      selectedCenter selectedCoefficient := by
  rw [reluApproxFineMachineStateValue_eq_sumElim,
    reluApproxFineMachineStateValue_eq_sumElim,
    reluApproxParallelFloorDigitState_withPersistentWork,
    reluApproxTaylorMachineDigitState_exact base step shift scale trans digit
      correction hdigit]

/-- One semantic fine round first tests the current fine box and then advances
the Taylor center, jet and code tails by one prescribed decoded digit. -/
private theorem reluApproxFineSelection_then_TaylorDigit_exact
    {d r : Nat}
    (R radius base : Real) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : TaylorMultiindex r d -> Nat)
    (correction : TaylorMultiindex r d -> Int)
    (hdigit : forall a, (digit a : Int) = correction a + (shift : Int))
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    reluApproxParallelFloorDigitState
      (reluApproxAffineMapWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineMatrix base trans))
      (reluApproxBiasWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineBias step shift scale))
      (reluApproxDigitCoeffWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineDigitCoeff scale))
      digit
      (fun z => reluApproxFineSelectionCycle R radius x
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
        (reluApproxFineMachineEquivFin d r z)) =
    reluApproxFineMachineStateValue x (fun q => center q + step q)
      (fun a => Finset.univ.sum (fun b => trans a b * coefficient b) +
        (correction a : Real) * scale a)
      (fun a => base * tail a - (digit a : Real))
      (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
      (reluApproxFineSelectedCoefficientStep R radius x center coefficient
        selectedCoefficient) := by
  rw [reluApproxFineSelectionCycle_machine_exact]
  exact reluApproxTaylorMachineDigitState_withFineRegisters_exact
    base step shift scale trans digit correction hdigit x center coefficient tail
    (reluApproxFineSelectedCenterStep R radius x center selectedCenter)
    (reluApproxFineSelectedCoefficientStep R radius x center coefficient
      selectedCoefficient)

/-- Tail register of one Taylor coefficient in the complete fine state. -/
private def reluApproxFineTaylorTailRegister {d r : Nat}
    (a : TaylorMultiindex r d) : ReLUApproxFineMachineState d r :=
  .inl (.inr (.inr a))

/-- Feature family used by one parallel floor/Taylor update on the complete
fine-machine state. -/
private abbrev ReLUApproxFineTaylorFeature (d r B : Nat) :=
  ReLUApproxParallelFloorFeature (ReLUApproxFineMachineState d r)
    (TaylorMultiindex r d) B

/-- Explicit width of the parallel floor feature family.  Keeping this
arithmetic form avoids relying on typeclass search through the dependent
Taylor multiindex type. -/
def fineTaylorFeatureSize (d r B : Nat) : Nat :=
  let s := reluApproxVectorBoxScanStateSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  (s + s) + Fintype.card (TaylorMultiindex r d) * (2 * B)

/-- Explicit finite numbering of the parallel floor features, aligned with
the complete fine-machine state numbering. -/
private noncomputable def reluApproxFineTaylorFeatureEquivFin (d r B : Nat) :
    ReLUApproxFineTaylorFeature d r B ≃
      Fin (fineTaylorFeatureSize d r B) :=
  let eS := reluApproxFineMachineEquivFin d r
  let eSS := (Equiv.sumCongr eS eS).trans finSumFinEquiv
  let eA := Fintype.equivFin (TaylorMultiindex r d)
  let eAF := (eA.prodCongr (Equiv.refl (Fin (2 * B)))).trans finProdFinEquiv
  (Equiv.sumCongr eSS eAF).trans finSumFinEquiv

/-- Concrete aligned feature matrix for one fine Taylor/floor macro. -/
private noncomputable def reluApproxFineTaylorFeatureSchedule
    (d r B : Nat) (base : Real) :
    Fin 1 -> Matrix (Fin (fineTaylorFeatureSize d r B))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)))) Real :=
  fun _ =>
    letI := Classical.decEq (ReLUApproxFineMachineState d r)
    reluApproxEquivFeatureMatrix
      (reluApproxFineMachineEquivFin d r)
      (reluApproxFineTaylorFeatureEquivFin d r B)
      (reluApproxParallelFloorFeatureMatrix base B
        (reluApproxFineTaylorTailRegister (d := d) (r := r)))

/-- Concrete aligned feature bias for one fine Taylor/floor macro. -/
private noncomputable def reluApproxFineTaylorFeatureBiasSchedule
    (d r B : Nat) (R : Real) :
    Fin 1 -> Fin (fineTaylorFeatureSize d r B) -> Real :=
  fun _ => reluApproxEquivFeatureBias
    (reluApproxFineTaylorFeatureEquivFin d r B)
    (reluApproxParallelFloorFeatureBias
      (S := ReLUApproxFineMachineState d r)
      (A := TaylorMultiindex r d) R B)

/-- Concrete aligned update matrix for one fine Taylor/floor macro. -/
private noncomputable def reluApproxFineTaylorUpdateSchedule
    (d r B : Nat) (R base : Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real) :
    Fin 1 -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))))
      (Fin (fineTaylorFeatureSize d r B)) Real :=
  fun _ => reluApproxEquivUpdateMatrix
    (reluApproxFineMachineEquivFin d r)
    (reluApproxFineTaylorFeatureEquivFin d r B)
    (reluApproxParallelFloorUpdateMatrix R B
      (reluApproxAffineMapWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineMatrix base trans))
      (reluApproxDigitCoeffWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineDigitCoeff scale)))

/-- Concrete aligned update bias for one fine Taylor/floor macro. -/
private noncomputable def reluApproxFineTaylorUpdateBiasSchedule
    (d r : Nat) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real) :
    Fin 1 -> Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  fun _ => reluApproxEquivUpdateBias
    (reluApproxFineMachineEquivFin d r)
    (reluApproxBiasWithPersistentWork
      (W := ReLUApproxSelectedTaylorRegisters d r ⊕
        ReLUApproxFineScanWork d r)
      (reluApproxTaylorMachineBias step shift scale))

/-- The aligned concrete one-macro floor schedule has exactly the typed
parallel floor/Taylor semantics. -/
private theorem reluApproxFineTaylorFloorSchedule_exact
    {d r B : Nat} (R base : Real) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (u : ReLUApproxFineMachineState d r -> Real) :
    (fun z => reluApproxMacroRecursionFrom
      (reluApproxFineTaylorFeatureSchedule d r B base)
      (reluApproxFineTaylorFeatureBiasSchedule d r B R)
      (reluApproxFineTaylorUpdateSchedule d r B R base trans scale)
      (reluApproxFineTaylorUpdateBiasSchedule d r step shift scale)
      (fun i => u ((reluApproxFineMachineEquivFin d r).symm i)) 1
      (reluApproxFineMachineEquivFin d r z)) =
    reluApproxParallelFloorState R B base
      (reluApproxFineTaylorTailRegister (d := d) (r := r))
      (reluApproxAffineMapWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineMatrix base trans))
      (reluApproxBiasWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineBias step shift scale))
      (reluApproxDigitCoeffWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineDigitCoeff scale)) u := by
  classical
  let eS := reluApproxFineMachineEquivFin d r
  let eH := reluApproxFineTaylorFeatureEquivFin d r B
  letI instStatePair : Fintype
      (ReLUApproxFineMachineState d r ⊕ ReLUApproxFineMachineState d r) :=
    instFintypeSum _ _
  letI instTaylorFloor : Fintype (TaylorMultiindex r d × Fin (2 * B)) :=
    instFintypeProd _ _
  letI instFeature : Fintype (ReLUApproxFineTaylorFeature d r B) :=
    instFintypeSum _ _
  let tail := reluApproxFineTaylorTailRegister (d := d) (r := r)
  let P := reluApproxAffineMapWithPersistentWork
    (W := ReLUApproxSelectedTaylorRegisters d r ⊕
      ReLUApproxFineScanWork d r)
    (reluApproxTaylorMachineMatrix base trans)
  let bias := reluApproxBiasWithPersistentWork
    (W := ReLUApproxSelectedTaylorRegisters d r ⊕
      ReLUApproxFineScanWork d r)
    (reluApproxTaylorMachineBias step shift scale)
  let digitCoeff := reluApproxDigitCoeffWithPersistentWork
    (W := ReLUApproxSelectedTaylorRegisters d r ⊕
      ReLUApproxFineScanWork d r)
    (reluApproxTaylorMachineDigitCoeff scale)
  have hreindex := reluApproxTypedMacroRecursionFrom_equiv eS eH
    (T := 1)
    (fun _ => reluApproxParallelFloorFeatureMatrix base B tail)
    (fun _ => reluApproxParallelFloorFeatureBias
      (S := ReLUApproxFineMachineState d r)
      (A := TaylorMultiindex r d) R B)
    (fun _ => reluApproxParallelFloorUpdateMatrix R B P digitCoeff)
    (fun _ => bias) u 1 le_rfl
  calc
    (fun z => reluApproxMacroRecursionFrom
      (reluApproxFineTaylorFeatureSchedule d r B base)
      (reluApproxFineTaylorFeatureBiasSchedule d r B R)
      (reluApproxFineTaylorUpdateSchedule d r B R base trans scale)
      (reluApproxFineTaylorUpdateBiasSchedule d r step shift scale)
      (fun i => u ((reluApproxFineMachineEquivFin d r).symm i)) 1
      (reluApproxFineMachineEquivFin d r z)) =
        reluApproxTypedMacroRecursionFrom
          (fun _ => reluApproxParallelFloorFeatureMatrix base B tail)
          (fun _ => reluApproxParallelFloorFeatureBias
            (S := ReLUApproxFineMachineState d r)
            (A := TaylorMultiindex r d) R B)
          (fun _ => reluApproxParallelFloorUpdateMatrix R B P digitCoeff)
          (fun _ => bias) u 1 := by
            simpa [eS, eH, tail, P, bias, digitCoeff,
              reluApproxFineTaylorFeatureSchedule,
              reluApproxFineTaylorFeatureBiasSchedule,
              reluApproxFineTaylorUpdateSchedule,
              reluApproxFineTaylorUpdateBiasSchedule] using hreindex
    _ = reluApproxParallelFloorState R B base tail P bias digitCoeff u := by
      rw [reluApproxTypedMacroRecursionFrom]
      simp only [dif_pos (show 0 < 1 by omega)]
      exact reluApproxParallelFloorMacro_exact R B base tail P bias digitCoeff u

/-- Common-workspace feature schedule for one complete fine round: two box
selection macros followed by one parallel floor/Taylor macro. -/
private noncomputable def reluApproxFineRoundFeatureSchedule
    (d r B : Nat) (Rselect Rfloor radius base : Real) :
    Fin 3 -> Matrix
      (Fin (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)))) Real :=
  reluApproxConcatFeatureSchedule
    (reluApproxFineSelectionFeatureSchedule d r Rselect)
    (reluApproxFineTaylorFeatureSchedule d r B base)

/-- Common-workspace feature biases for one complete fine round. -/
private noncomputable def reluApproxFineRoundFeatureBiasSchedule
    (d r B : Nat) (Rselect Rfloor radius : Real) :
    Fin 3 -> Fin
      (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B) -> Real :=
  reluApproxConcatFeatureBiasSchedule
    (reluApproxFineSelectionFeatureBiasSchedule d r Rselect radius)
    (reluApproxFineTaylorFeatureBiasSchedule d r B Rfloor)

/-- Common-workspace update matrices for one complete fine round. -/
private noncomputable def reluApproxFineRoundUpdateSchedule
    (d r B : Nat) (Rfloor base : Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real) :
    Fin 3 -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))))
      (Fin (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B)) Real :=
  reluApproxConcatUpdateSchedule
    (reluApproxFineSelectionUpdateSchedule d r)
    (reluApproxFineTaylorUpdateSchedule d r B Rfloor base trans scale)

/-- Common-workspace update biases for one complete fine round. -/
private noncomputable def reluApproxFineRoundUpdateBiasSchedule
    (d r : Nat) (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real) :
    Fin 3 -> Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  reluApproxConcatUpdateBiasSchedule
    (reluApproxFineSelectionUpdateBiasSchedule d r)
    (reluApproxFineTaylorUpdateBiasSchedule d r step shift scale)

/-- One concrete three-macro fine round has the expected selector followed by
parallel floor/Taylor semantics on the shared aligned state. -/
private theorem reluApproxFineRoundSchedule_floor_exact
    {d r B : Nat} (Rselect Rfloor radius base : Real)
    (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    (fun z => reluApproxMacroRecursionFrom
      (reluApproxFineRoundFeatureSchedule d r B
        Rselect Rfloor radius base)
      (reluApproxFineRoundFeatureBiasSchedule d r B
        Rselect Rfloor radius)
      (reluApproxFineRoundUpdateSchedule d r B Rfloor base trans scale)
      (reluApproxFineRoundUpdateBiasSchedule d r step shift scale)
      (reluApproxVectorBoxScanState x (fun k =>
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
          ((reluApproxFineAccumulatorEquivFin d r).symm k))) 3
      (reluApproxFineMachineEquivFin d r z)) =
    reluApproxParallelFloorState Rfloor B base
      (reluApproxFineTaylorTailRegister (d := d) (r := r))
      (reluApproxAffineMapWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineMatrix base trans))
      (reluApproxBiasWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineBias step shift scale))
      (reluApproxDigitCoeffWithPersistentWork
        (W := ReLUApproxSelectedTaylorRegisters d r ⊕
          ReLUApproxFineScanWork d r)
        (reluApproxTaylorMachineDigitCoeff scale))
      (reluApproxFineMachineStateValue x center coefficient tail
        (reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter)
        (reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
          selectedCoefficient)) := by
  let acc : ReLUApproxFineAccumulator d r -> Real :=
    Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
      (reluApproxSelectedTaylorState selectedCenter selectedCoefficient)
  let selectedState : ReLUApproxFineMachineState d r -> Real :=
    reluApproxFineMachineStateValue x center coefficient tail
      (reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter)
      (reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
        selectedCoefficient)
  have hconcat := reluApproxMacroRecursionFrom_concat
    (reluApproxFineSelectionFeatureSchedule d r Rselect)
    (reluApproxFineSelectionFeatureBiasSchedule d r Rselect radius)
    (reluApproxFineSelectionUpdateSchedule d r)
    (reluApproxFineSelectionUpdateBiasSchedule d r)
    (reluApproxFineTaylorFeatureSchedule d r B base)
    (reluApproxFineTaylorFeatureBiasSchedule d r B Rfloor)
    (reluApproxFineTaylorUpdateSchedule d r B Rfloor base trans scale)
    (reluApproxFineTaylorUpdateBiasSchedule d r step shift scale)
    (reluApproxVectorBoxScanState x (fun k =>
      acc ((reluApproxFineAccumulatorEquivFin d r).symm k)))
  have hselection := reluApproxFineSelectionSchedule_exact
    Rselect radius x acc
  have hselectionFin : reluApproxFineSelectionCycle Rselect radius x acc =
      fun i => selectedState ((reluApproxFineMachineEquivFin d r).symm i) := by
    funext i
    have h := congrFun
      (reluApproxFineSelectionCycle_machine_exact Rselect radius x center
        coefficient tail selectedCenter selectedCoefficient)
      ((reluApproxFineMachineEquivFin d r).symm i)
    simpa [acc, selectedState] using h
  have hconcat3 :
      reluApproxMacroRecursionFrom
        (reluApproxFineRoundFeatureSchedule d r B
          Rselect Rfloor radius base)
        (reluApproxFineRoundFeatureBiasSchedule d r B
          Rselect Rfloor radius)
        (reluApproxFineRoundUpdateSchedule d r B Rfloor base trans scale)
        (reluApproxFineRoundUpdateBiasSchedule d r step shift scale)
        (reluApproxVectorBoxScanState x (fun k =>
          acc ((reluApproxFineAccumulatorEquivFin d r).symm k))) 3 =
      reluApproxMacroRecursionFrom
        (reluApproxFineTaylorFeatureSchedule d r B base)
        (reluApproxFineTaylorFeatureBiasSchedule d r B Rfloor)
        (reluApproxFineTaylorUpdateSchedule d r B Rfloor base trans scale)
        (reluApproxFineTaylorUpdateBiasSchedule d r step shift scale)
        (reluApproxMacroRecursionFrom
          (reluApproxFineSelectionFeatureSchedule d r Rselect)
          (reluApproxFineSelectionFeatureBiasSchedule d r Rselect radius)
          (reluApproxFineSelectionUpdateSchedule d r)
          (reluApproxFineSelectionUpdateBiasSchedule d r)
          (reluApproxVectorBoxScanState x (fun k =>
            acc ((reluApproxFineAccumulatorEquivFin d r).symm k))) 2) 1 := by
    simpa [reluApproxFineRoundFeatureSchedule,
      reluApproxFineRoundFeatureBiasSchedule,
      reluApproxFineRoundUpdateSchedule,
      reluApproxFineRoundUpdateBiasSchedule] using hconcat
  rw [show (fun k =>
      (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
        (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
        ((reluApproxFineAccumulatorEquivFin d r).symm k)) =
      (fun k => acc ((reluApproxFineAccumulatorEquivFin d r).symm k)) by rfl]
  rw [hconcat3, hselection, hselectionFin]
  simpa [selectedState] using
    (reluApproxFineTaylorFloorSchedule_exact Rfloor base step shift scale trans
      selectedState)

/-- If every parallel floor bank reads the prescribed Taylor digit, the
concrete three-macro fine round performs exactly one semantic selection and
Taylor update. -/
private theorem reluApproxFineRoundSchedule_digit_exact
    {d r B : Nat} (Rselect Rfloor radius base : Real)
    (step : Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : TaylorMultiindex r d -> Nat)
    (correction : TaylorMultiindex r d -> Int)
    (hdigit : forall a, (digit a : Int) = correction a + (shift : Int))
    (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real)
    (hfloor : forall a,
      truncatedFloorReLUFunction Rfloor B (base * tail a) = (digit a : Real)) :
    (fun z => reluApproxMacroRecursionFrom
      (reluApproxFineRoundFeatureSchedule d r B
        Rselect Rfloor radius base)
      (reluApproxFineRoundFeatureBiasSchedule d r B
        Rselect Rfloor radius)
      (reluApproxFineRoundUpdateSchedule d r B Rfloor base trans scale)
      (reluApproxFineRoundUpdateBiasSchedule d r step shift scale)
      (reluApproxVectorBoxScanState x (fun k =>
        (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
          (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
          ((reluApproxFineAccumulatorEquivFin d r).symm k))) 3
      (reluApproxFineMachineEquivFin d r z)) =
    reluApproxFineMachineStateValue x (fun q => center q + step q)
      (fun a => Finset.univ.sum (fun b => trans a b * coefficient b) +
        (correction a : Real) * scale a)
      (fun a => base * tail a - (digit a : Real))
      (reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter)
      (reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
        selectedCoefficient) := by
  rw [reluApproxFineRoundSchedule_floor_exact]
  let selectedCenter' :=
    reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter
  let selectedCoefficient' :=
    reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
      selectedCoefficient
  let selectedState :=
    reluApproxFineMachineStateValue x center coefficient tail
      selectedCenter' selectedCoefficient'
  have hfloorState :
      reluApproxParallelFloorState Rfloor B base
        (reluApproxFineTaylorTailRegister (d := d) (r := r))
        (reluApproxAffineMapWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineMatrix base trans))
        (reluApproxBiasWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineBias step shift scale))
        (reluApproxDigitCoeffWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineDigitCoeff scale)) selectedState =
      reluApproxParallelFloorDigitState
        (reluApproxAffineMapWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineMatrix base trans))
        (reluApproxBiasWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineBias step shift scale))
        (reluApproxDigitCoeffWithPersistentWork
          (W := ReLUApproxSelectedTaylorRegisters d r ⊕
            ReLUApproxFineScanWork d r)
          (reluApproxTaylorMachineDigitCoeff scale)) digit selectedState := by
    funext i
    simp only [reluApproxParallelFloorState,
      reluApproxParallelFloorDigitState]
    congr 1
    apply Finset.sum_congr rfl
    intro a _ha
    rw [show selectedState
        (reluApproxFineTaylorTailRegister (d := d) (r := r) a) = tail a by rfl,
      hfloor a]
  rw [show reluApproxFineMachineStateValue x center coefficient tail
      (reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter)
      (reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
        selectedCoefficient) = selectedState by rfl,
    hfloorState]
  simpa [selectedCenter', selectedCoefficient', selectedState] using
    (reluApproxTaylorMachineDigitState_withFineRegisters_exact
      base step shift scale trans digit correction hdigit x center coefficient tail
      selectedCenter' selectedCoefficient')

/-- Flatten `T` three-macro fine rounds into one network schedule. -/
private noncomputable def reluApproxFineRoundsFeatureSchedule
    (T d r B : Nat) (Rselect Rfloor radius base : Real) :
    Fin (T * 3) -> Matrix
      (Fin (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B))
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r)))) Real :=
  fun k => reluApproxFineRoundFeatureSchedule d r B
    Rselect Rfloor radius base (finProdFinEquiv.symm k).2

private noncomputable def reluApproxFineRoundsFeatureBiasSchedule
    (T d r B : Nat) (Rselect Rfloor radius : Real) :
    Fin (T * 3) -> Fin
      (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B) -> Real :=
  fun k => reluApproxFineRoundFeatureBiasSchedule d r B
    Rselect Rfloor radius (finProdFinEquiv.symm k).2

private noncomputable def reluApproxFineRoundsUpdateSchedule
    (T d r B : Nat) (Rfloor base : Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real) :
    Fin (T * 3) -> Matrix
      (Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))))
      (Fin (reluApproxVectorBoxScanFeatureSize d
          (Fintype.card (ReLUApproxFineAccumulator d r)) +
        fineTaylorFeatureSize d r B)) Real :=
  fun k => reluApproxFineRoundUpdateSchedule d r B Rfloor base
    (trans (finProdFinEquiv.symm k).1) scale (finProdFinEquiv.symm k).2

private noncomputable def reluApproxFineRoundsUpdateBiasSchedule
    (T d r : Nat)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real) :
    Fin (T * 3) -> Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  fun k => reluApproxFineRoundUpdateBiasSchedule d r
    (step (finProdFinEquiv.symm k).1) shift scale
    (finProdFinEquiv.symm k).2

@[simp] theorem reluApproxFineRoundsFeatureSchedule_apply
    {T d r B : Nat} (Rselect Rfloor radius base : Real)
    (k : Fin T) (p : Fin 3) :
    reluApproxFineRoundsFeatureSchedule T d r B
        Rselect Rfloor radius base (finProdFinEquiv (k, p)) =
      reluApproxFineRoundFeatureSchedule d r B
        Rselect Rfloor radius base p := by
  simp [reluApproxFineRoundsFeatureSchedule]

@[simp] theorem reluApproxFineRoundsFeatureBiasSchedule_apply
    {T d r B : Nat} (Rselect Rfloor radius : Real)
    (k : Fin T) (p : Fin 3) :
    reluApproxFineRoundsFeatureBiasSchedule T d r B
        Rselect Rfloor radius (finProdFinEquiv (k, p)) =
      reluApproxFineRoundFeatureBiasSchedule d r B
        Rselect Rfloor radius p := by
  simp [reluApproxFineRoundsFeatureBiasSchedule]

@[simp] theorem reluApproxFineRoundsUpdateSchedule_apply
    {T d r B : Nat} (Rfloor base : Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real)
    (k : Fin T) (p : Fin 3) :
    reluApproxFineRoundsUpdateSchedule T d r B Rfloor base trans scale
        (finProdFinEquiv (k, p)) =
      reluApproxFineRoundUpdateSchedule d r B Rfloor base
        (trans k) scale p := by
  simp [reluApproxFineRoundsUpdateSchedule]

@[simp] theorem reluApproxFineRoundsUpdateBiasSchedule_apply
    {T d r : Nat} (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (k : Fin T) (p : Fin 3) :
    reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale
        (finProdFinEquiv (k, p)) =
      reluApproxFineRoundUpdateBiasSchedule d r (step k) shift scale p := by
  simp [reluApproxFineRoundsUpdateBiasSchedule]

/-- The three flat schedule entries belonging to one fine cell are exactly
that cell's concrete round schedule. -/
private theorem reluApproxFineRoundsOffset_eq_round
    {T d r B : Nat} (Rselect Rfloor radius base : Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (u : Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real)
    (k : Fin T) :
    reluApproxMacroRecursionFromOffset
        (reluApproxFineRoundsFeatureSchedule T d r B
          Rselect Rfloor radius base)
        (reluApproxFineRoundsFeatureBiasSchedule T d r B
          Rselect Rfloor radius)
        (reluApproxFineRoundsUpdateSchedule T d r B
          Rfloor base trans scale)
        (reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale)
        (3 * k.val) u 3 =
      reluApproxMacroRecursionFrom
        (reluApproxFineRoundFeatureSchedule d r B
          Rselect Rfloor radius base)
        (reluApproxFineRoundFeatureBiasSchedule d r B
          Rselect Rfloor radius)
        (reluApproxFineRoundUpdateSchedule d r B Rfloor base (trans k) scale)
        (reluApproxFineRoundUpdateBiasSchedule d r (step k) shift scale)
        u 3 := by
  have h0 : 3 * k.val + 0 < T * 3 := by omega
  have h1 : 3 * k.val + 1 < T * 3 := by omega
  have h2 : 3 * k.val + 2 < T * 3 := by omega
  have hi0 : (⟨3 * k.val + 0, h0⟩ : Fin (T * 3)) =
      finProdFinEquiv (k, (0 : Fin 3)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
  have hi1 : (⟨3 * k.val + 1, h1⟩ : Fin (T * 3)) =
      finProdFinEquiv (k, (1 : Fin 3)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  have hi2 : (⟨3 * k.val + 2, h2⟩ : Fin (T * 3)) =
      finProdFinEquiv (k, (2 : Fin 3)) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    omega
  funext i
  simp only [reluApproxMacroRecursionFromOffset,
    reluApproxMacroRecursionFrom, dif_pos h0, dif_pos h1, dif_pos h2,
    show 0 < 3 by omega, show 1 < 3 by omega, show 2 < 3 by omega]
  rw [hi0, hi1, hi2]
  simp

/-- Selected-center registers accumulated during the fine scan. -/
private noncomputable def reluApproxFineSelectedCenterRecursion
    {d T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real) (selectedCenter0 : Fin d -> Real) :
    Nat -> Fin d -> Real
  | 0 => selectedCenter0
  | t + 1 => if ht : t < T then
      reluApproxFineSelectedCenterStep R radius x (center t)
        (reluApproxFineSelectedCenterRecursion (T := T)
          R radius x center selectedCenter0 t)
    else
      reluApproxFineSelectedCenterRecursion (T := T)
        R radius x center selectedCenter0 t

/-- Selected Taylor-coefficient registers accumulated during the fine scan. -/
private noncomputable def reluApproxFineSelectedCoefficientRecursion
    {d r T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real)
    (coefficient : Nat -> TaylorMultiindex r d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real) :
    Nat -> TaylorMultiindex r d -> Real
  | 0 => selectedCoefficient0
  | t + 1 => if ht : t < T then
      reluApproxFineSelectedCoefficientStep R radius x (center t)
        (coefficient t)
        (reluApproxFineSelectedCoefficientRecursion (T := T)
          R radius x center coefficient selectedCoefficient0 t)
    else
      reluApproxFineSelectedCoefficientRecursion (T := T)
        R radius x center coefficient selectedCoefficient0 t

/-- The selected-center register is the initial value plus the box-gated
contributions of all fine centers processed so far. -/
private theorem reluApproxFineSelectedCenterRecursion_eq_sum
    {d T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real) (selectedCenter0 : Fin d -> Real)
    (n : Nat) (hn : n <= T) (q : Fin d) :
    reluApproxFineSelectedCenterRecursion (T := T) R radius x center
        selectedCenter0 n q =
      selectedCenter0 q + Finset.sum (Finset.range n) (fun k =>
        reluApproxBoxGate R (fun u => center k u - radius)
          (fun u => center k u + radius) x (center k q)) := by
  induction n with
  | zero => simp [reluApproxFineSelectedCenterRecursion]
  | succ n ih =>
      have hnT : n < T := Nat.lt_of_succ_le hn
      rw [reluApproxFineSelectedCenterRecursion, dif_pos hnT,
        reluApproxFineSelectedCenterStep, ih (Nat.le_of_succ_le hn),
        Finset.sum_range_succ]
      ring

/-- The selected-coefficient register obeys the analogous finite box-gate
sum identity. -/
private theorem reluApproxFineSelectedCoefficientRecursion_eq_sum
    {d r T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real)
    (coefficient : Nat -> TaylorMultiindex r d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (n : Nat) (hn : n <= T) (a : TaylorMultiindex r d) :
    reluApproxFineSelectedCoefficientRecursion (T := T) R radius x center
        coefficient selectedCoefficient0 n a =
      selectedCoefficient0 a + Finset.sum (Finset.range n) (fun k =>
        reluApproxBoxGate R (fun u => center k u - radius)
          (fun u => center k u + radius) x (coefficient k a)) := by
  induction n with
  | zero => simp [reluApproxFineSelectedCoefficientRecursion]
  | succ n ih =>
      have hnT : n < T := Nat.lt_of_succ_le hn
      rw [reluApproxFineSelectedCoefficientRecursion, dif_pos hnT,
        reluApproxFineSelectedCoefficientStep, ih (Nat.le_of_succ_le hn),
        Finset.sum_range_succ]
      ring

/-- Canonical degree-zero Taylor index, used as a dedicated scalar register in
auxiliary fine scans. -/
private def reluApproxZeroTaylorMultiindex (r d : Nat) : TaylorMultiindex r d :=
  ⟨⟨0, Nat.succ_pos r⟩, fun k => Fin.elim0 k⟩

/-- If one Taylor channel is kept constantly equal to one, its selected value
after the fine scan is exactly the total fine-box gate mass.  This lets the
same `O(T)` coarse/fine machine produce the hierarchical boundary checker,
without a flat scan through all coarse/fine pairs. -/
private theorem reluApproxFineSelectedUnitMass_eq_sum_boxGate
    {d r T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real) :
    reluApproxFineSelectedCoefficientRecursion (r := r) (T := T)
        R radius x center (fun _ _ => 1) (fun _ => 0) T
        (reluApproxZeroTaylorMultiindex r d) =
      Finset.univ.sum fun k : Fin T =>
        reluApproxBoxGate R (fun q => center k.val q - radius)
          (fun q => center k.val q + radius) x 1 := by
  rw [reluApproxFineSelectedCoefficientRecursion_eq_sum
    R radius x center (fun _ _ => 1) (fun _ => 0) T le_rfl]
  simp only [Pi.zero_apply, zero_add]
  exact (Fin.sum_univ_eq_sum_range (fun k : Nat =>
        reluApproxBoxGate R (fun q => center k q - radius)
      (fun q => center k q + radius) x 1) T).symm

/-- Concrete terminal-state coordinate holding the unit gate mass in an
auxiliary fine scan. -/
noncomputable def reluApproxFineSelectedUnitMassIndex (d r : Nat) :
    Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) :=
  reluApproxFineMachineEquivFin d r
    (.inr (.inl (.inr (reluApproxZeroTaylorMultiindex r d))))

/-- Linear readout that turns the selected unit mass into its complement. -/
private noncomputable def reluApproxFineBoundaryCheckOutputWeight (d r : Nat) :
    Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real :=
  fun i => if i = reluApproxFineSelectedUnitMassIndex d r then -1 else 0

/-- The checker readout of a semantic terminal fine-machine state is exactly
one minus the selected unit gate mass. -/
private theorem reluApproxFineBoundaryCheckOutputWeight_stateValue
    {d r : Nat} (x center : Fin d -> Real)
    (coefficient tail : TaylorMultiindex r d -> Real)
    (selectedCenter : Fin d -> Real)
    (selectedCoefficient : TaylorMultiindex r d -> Real) :
    (Finset.univ.sum fun i : Fin (reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))) =>
        reluApproxFineBoundaryCheckOutputWeight d r i *
          reluApproxFineMachineStateValue x center coefficient tail
            selectedCenter selectedCoefficient
            ((reluApproxFineMachineEquivFin d r).symm i)) + 1 =
      1 - selectedCoefficient (reluApproxZeroTaylorMultiindex r d) := by
  classical
  rw [Finset.sum_eq_single (reluApproxFineSelectedUnitMassIndex d r)]
  · simp [reluApproxFineBoundaryCheckOutputWeight,
      reluApproxFineSelectedUnitMassIndex,
      reluApproxFineMachineStateValue, reluApproxSelectedTaylorState]
    ring
  · intro i _hi hine
    simp [reluApproxFineBoundaryCheckOutputWeight, hine]
  · simp

/-- On a unique safe fine box, the selected registers contain exactly that
center and coefficient vector after the complete fine scan. -/
theorem reluApproxFineSelectedRecursions_eq_of_unique
    {d r T : Nat} {R radius : Real} (hR : 0 < R)
    (x : Fin d -> Real) (center : Nat -> Fin d -> Real)
    (coefficient : Nat -> TaylorMultiindex r d -> Real) (active : Fin T)
    (hcenterBound : forall k : Fin T, forall q, |center k.val q| <= R)
    (hcoefficientBound : forall k : Fin T, forall a, |coefficient k.val a| <= R)
    (hactive : forall q,
      center active.val q - radius + R⁻¹ <= x q /\
        x q <= center active.val q + radius - R⁻¹)
    (hinactive : forall k : Fin T, k ≠ active -> exists q,
      x q <= center k.val q - radius \/ center k.val q + radius <= x q) :
    (reluApproxFineSelectedCenterRecursion (T := T) R radius x center
        (fun _ => 0) T = center active.val) /\
      (reluApproxFineSelectedCoefficientRecursion (T := T) R radius x center
        coefficient (fun _ => 0) T = coefficient active.val) := by
  constructor
  · funext q
    rw [reluApproxFineSelectedCenterRecursion_eq_sum R radius x center
      (fun _ => 0) T le_rfl q, zero_add,
      <- Fin.sum_univ_eq_sum_range]
    exact reluApprox_sum_boxGate_eq_payload_of_unique hR
      (fun k u => center k.val u - radius)
      (fun k u => center k.val u + radius) (fun k => center k.val q)
      x active (fun k => hcenterBound k q) hactive hinactive
  · funext a
    rw [reluApproxFineSelectedCoefficientRecursion_eq_sum R radius x center
      coefficient (fun _ => 0) T le_rfl a, zero_add,
      <- Fin.sum_univ_eq_sum_range]
    exact reluApprox_sum_boxGate_eq_payload_of_unique hR
      (fun k u => center k.val u - radius)
      (fun k u => center k.val u + radius) (fun k => coefficient k.val a)
      x active (fun k => hcoefficientBound k a) hactive hinactive

/-- The flattened concrete fine schedule maintains the complete semantic
Taylor/selection invariant after every processed fine cell. -/
private theorem reluApproxFineRoundsSchedule_digit_exact
    {T d r B : Nat} (Rselect Rfloor radius base : Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (x center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (selectedCenter0 : Fin d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real))
    (t : Nat) (ht : t <= T) :
    reluApproxMacroRecursionFrom
        (reluApproxFineRoundsFeatureSchedule T d r B
          Rselect Rfloor radius base)
        (reluApproxFineRoundsFeatureBiasSchedule T d r B
          Rselect Rfloor radius)
        (reluApproxFineRoundsUpdateSchedule T d r B
          Rfloor base trans scale)
        (reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale)
        (reluApproxVectorBoxScanState x (fun k =>
          (Sum.elim
            (reluApproxTaylorPayloadState center0 coefficient0 tail0)
            (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
            ((reluApproxFineAccumulatorEquivFin d r).symm k))) (3 * t) =
      fun i => reluApproxFineMachineStateValue x
        (reluApproxTaylorCenterRecursion step center0 t)
        (reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 t)
        (reluApproxTaylorTailRecursion base digit tail0 t)
        (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0) selectedCenter0 t)
        (reluApproxFineSelectedCoefficientRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
          selectedCoefficient0 t)
        ((reluApproxFineMachineEquivFin d r).symm i) := by
  induction t with
  | zero =>
      simpa [reluApproxMacroRecursionFrom,
        reluApproxTaylorCenterRecursion,
        reluApproxTaylorCoefficientRecursion,
        reluApproxTaylorTailRecursion,
        reluApproxFineSelectedCenterRecursion,
        reluApproxFineSelectedCoefficientRecursion] using
        (reluApproxVectorBoxScanState_fineMachineEquiv x center0 coefficient0 tail0
          selectedCenter0 selectedCoefficient0)
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      have hprefix : t <= T := Nat.le_of_succ_le ht
      have hflat : 3 * t + 3 <= T * 3 := by omega
      rw [show 3 * (t + 1) = 3 * t + 3 by ring]
      rw [reluApproxMacroRecursionFrom_add_eq_offset _ _ _ _ _ _ _ hflat]
      rw [ih hprefix]
      let k : Fin T := ⟨t, htlt⟩
      rw [reluApproxFineRoundsOffset_eq_round
        Rselect Rfloor radius base step shift scale trans _ k]
      let center := reluApproxTaylorCenterRecursion step center0 t
      let coefficient :=
        reluApproxTaylorCoefficientRecursion scale trans correction coefficient0 t
      let tail := reluApproxTaylorTailRecursion base digit tail0 t
      let selectedCenter := reluApproxFineSelectedCenterRecursion (T := T)
        Rselect radius x
        (reluApproxTaylorCenterRecursion step center0) selectedCenter0 t
      let selectedCoefficient :=
        reluApproxFineSelectedCoefficientRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
          selectedCoefficient0 t
      have hstate := reluApproxVectorBoxScanState_fineMachineEquiv
        x center coefficient tail selectedCenter selectedCoefficient
      rw [show (fun i => reluApproxFineMachineStateValue x
          (reluApproxTaylorCenterRecursion step center0 t)
          (reluApproxTaylorCoefficientRecursion
            scale trans correction coefficient0 t)
          (reluApproxTaylorTailRecursion base digit tail0 t)
          (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
            (reluApproxTaylorCenterRecursion step center0) selectedCenter0 t)
          (reluApproxFineSelectedCoefficientRecursion (T := T) Rselect radius x
            (reluApproxTaylorCenterRecursion step center0)
            (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
            selectedCoefficient0 t)
          ((reluApproxFineMachineEquivFin d r).symm i)) =
        (fun i => reluApproxFineMachineStateValue x center coefficient tail
          selectedCenter selectedCoefficient
          ((reluApproxFineMachineEquivFin d r).symm i)) by rfl]
      rw [← hstate]
      have hround := reluApproxFineRoundSchedule_digit_exact
        Rselect Rfloor radius base (step k) shift scale (trans k)
        (digit k) (correction k) (hdigit k) x center coefficient tail
        selectedCenter selectedCoefficient (hfloor k)
      have hroundFin :
          reluApproxMacroRecursionFrom
            (reluApproxFineRoundFeatureSchedule d r B
              Rselect Rfloor radius base)
            (reluApproxFineRoundFeatureBiasSchedule d r B
              Rselect Rfloor radius)
            (reluApproxFineRoundUpdateSchedule d r B Rfloor base (trans k) scale)
            (reluApproxFineRoundUpdateBiasSchedule d r (step k) shift scale)
            (reluApproxVectorBoxScanState x (fun j =>
              (Sum.elim (reluApproxTaylorPayloadState center coefficient tail)
                (reluApproxSelectedTaylorState selectedCenter selectedCoefficient))
                ((reluApproxFineAccumulatorEquivFin d r).symm j))) 3 =
          fun i => reluApproxFineMachineStateValue x
            (fun q => center q + step k q)
            (fun a => Finset.univ.sum (fun b => trans k a b * coefficient b) +
              (correction k a : Real) * scale a)
            (fun a => base * tail a - (digit k a : Real))
            (reluApproxFineSelectedCenterStep Rselect radius x center selectedCenter)
            (reluApproxFineSelectedCoefficientStep Rselect radius x center coefficient
              selectedCoefficient)
            ((reluApproxFineMachineEquivFin d r).symm i) := by
        funext i
        simpa using congrFun hround ((reluApproxFineMachineEquivFin d r).symm i)
      rw [hroundFin]
      simp only [reluApproxTaylorCenterRecursion,
        reluApproxTaylorCoefficientRecursion,
        reluApproxTaylorTailRecursion,
        reluApproxFineSelectedCenterRecursion,
        reluApproxFineSelectedCoefficientRecursion, dif_pos htlt]
      rfl

/-- On a safe coarse cell, the vector box scan loads the complete initial
fine-machine state and the concatenated schedule then executes all fine
Taylor/selection rounds.  This is the exact state-level interface between the
two passes of the paper construction. -/
private theorem reluApproxCoarseScan_then_fineRounds_digit_exact
    {coarse T d r B : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (active : Fin coarse)
    (hRscan : 0 < Rscan)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (x : Fin d -> Real)
    (hactive : forall q,
      lower active q + Rscan⁻¹ <= x q /\ x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i, i ≠ active -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (selectedCenter0 : Fin d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (hpayload_active : payload active =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real)) :
    reluApproxSignedMacroRecursion
        (reluApproxVectorBoxScanInputMatrix d
          (Fintype.card (ReLUApproxFineAccumulator d r)))
        (fun _ => 0)
        (reluApproxConcatFeatureSchedule
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (reluApproxFineRoundsFeatureSchedule T d r B
            Rselect Rfloor radius base))
        (reluApproxConcatFeatureBiasSchedule
          (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper
            (fun i k => payload i
              ((reluApproxFineAccumulatorEquivFin d r).symm k)))
          (reluApproxFineRoundsFeatureBiasSchedule T d r B
            Rselect Rfloor radius))
        (reluApproxConcatUpdateSchedule
          (reluApproxVectorBoxScanUpdateSchedule
            (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
            (T := coarse))
          (reluApproxFineRoundsUpdateSchedule T d r B
            Rfloor base trans scale))
        (reluApproxConcatUpdateBiasSchedule
          (reluApproxVectorBoxScanUpdateBiasSchedule
            (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
            (T := coarse))
          (reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale))
        x (coarse * 2 + T * 3) =
      fun i => reluApproxFineMachineStateValue x
        (reluApproxTaylorCenterRecursion step center0 T)
        (reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 T)
        (reluApproxTaylorTailRecursion base digit tail0 T)
        (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0) selectedCenter0 T)
        (reluApproxFineSelectedCoefficientRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
          selectedCoefficient0 T)
        ((reluApproxFineMachineEquivFin d r).symm i) := by
  let payloadFin : Fin coarse ->
      Fin (Fintype.card (ReLUApproxFineAccumulator d r)) -> Real :=
    fun i k => payload i ((reluApproxFineAccumulatorEquivFin d r).symm k)
  have hpayloadFin : forall i k, |payloadFin i k| <= Rscan := by
    intro i k
    exact hpayload i ((reluApproxFineAccumulatorEquivFin d r).symm k)
  rw [reluApproxSignedMacroRecursion_concat]
  have hscan := reluApproxVectorBoxScanRecursion_eq_payload_of_unique
    hRscan lower upper payloadFin x active hpayloadFin hactive hinactive
  have hscan' :
      reluApproxSignedMacroRecursion
          (reluApproxVectorBoxScanInputMatrix d
            (Fintype.card (ReLUApproxFineAccumulator d r)))
          (fun _ => 0)
          (reluApproxVectorBoxScanFeatureSchedule Rscan)
          (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper payloadFin)
          reluApproxVectorBoxScanUpdateSchedule
          reluApproxVectorBoxScanUpdateBiasSchedule x (coarse * 2) =
        reluApproxVectorBoxScanState x (payloadFin active) := by
    simpa [Nat.mul_comm] using hscan
  rw [show (fun i k => payload i
      ((reluApproxFineAccumulatorEquivFin d r).symm k)) = payloadFin by rfl]
  rw [hscan']
  have hpayloadFin_active : payloadFin active = fun k =>
      (Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
        ((reluApproxFineAccumulatorEquivFin d r).symm k) := by
    funext k
    simp [payloadFin, hpayload_active]
  rw [hpayloadFin_active]
  simpa [Nat.mul_comm] using
    (reluApproxFineRoundsSchedule_digit_exact
      Rselect Rfloor radius base step shift scale trans digit correction hdigit
      x center0 coefficient0 tail0 selectedCenter0 selectedCoefficient0 hfloor T le_rfl)

/-- Compile the complete coarse-scan/fine-round schedule into one exact-depth
fully connected network.  The network is independent of the active coarse
cell; once a safe active cell is supplied, its output is the requested linear
readout of the terminal semantic Taylor-machine state. -/
private theorem exists_reluApproxCoarseScan_then_fineRoundsNet_exactDepth
    {coarse T d r B D W : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (outputWeight : Fin (reluApproxVectorBoxScanStateSize d
      (Fintype.card (ReLUApproxFineAccumulator d r))) -> Real)
    (outputBias : Real)
    (hdepth : 2 * (coarse * 2 + T * 3) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let hscan := reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let h := hscan + (hscan + fineTaylorFeatureSize d r B)
      (s + s) + h <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (active : Fin coarse),
          0 < Rscan ->
          (forall i p, |payload i p| <= Rscan) ->
          (forall q,
            lower active q + Rscan⁻¹ <= x q /\
              x q <= upper active q - Rscan⁻¹) ->
          (forall i, i ≠ active -> exists q,
            x q <= lower i q \/ upper i q <= x q) ->
          forall (digit : Fin T -> TaylorMultiindex r d -> Nat)
            (correction : Fin T -> TaylorMultiindex r d -> Int)
            (center0 : Fin d -> Real)
            (coefficient0 tail0 : TaylorMultiindex r d -> Real)
            (selectedCenter0 : Fin d -> Real)
            (selectedCoefficient0 : TaylorMultiindex r d -> Real),
          (forall k a,
            (digit k a : Int) = correction k a + (shift : Int)) ->
          payload active =
            Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
              (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0) ->
          (forall k a,
            truncatedFloorReLUFunction Rfloor B
                (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
              (digit k a : Real)) ->
          N.realize x =
            (Finset.univ.sum fun i => outputWeight i *
              reluApproxFineMachineStateValue x
                (reluApproxTaylorCenterRecursion step center0 T)
                (reluApproxTaylorCoefficientRecursion
                  scale trans correction coefficient0 T)
                (reluApproxTaylorTailRecursion base digit tail0 T)
                (reluApproxFineSelectedCenterRecursion (T := T)
                  Rselect radius x
                  (reluApproxTaylorCenterRecursion step center0)
                  selectedCenter0 T)
                (reluApproxFineSelectedCoefficientRecursion (T := T)
                  Rselect radius x
                  (reluApproxTaylorCenterRecursion step center0)
                  (reluApproxTaylorCoefficientRecursion
                    scale trans correction coefficient0)
                  selectedCoefficient0 T)
                ((reluApproxFineMachineEquivFin d r).symm i)) + outputBias := by
  let s := reluApproxVectorBoxScanStateSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  let hscan := reluApproxVectorBoxScanFeatureSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  let h := hscan + (hscan + fineTaylorFeatureSize d r B)
  let featureMatrix : Fin (coarse * 2 + T * 3) -> Matrix (Fin h) (Fin s) Real :=
    reluApproxConcatFeatureSchedule
      (reluApproxVectorBoxScanFeatureSchedule Rscan)
      (reluApproxFineRoundsFeatureSchedule T d r B
        Rselect Rfloor radius base)
  let featureBias : Fin (coarse * 2 + T * 3) -> Fin h -> Real :=
    reluApproxConcatFeatureBiasSchedule
      (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper
        (fun i k => payload i
          ((reluApproxFineAccumulatorEquivFin d r).symm k)))
      (reluApproxFineRoundsFeatureBiasSchedule T d r B
        Rselect Rfloor radius)
  let updateMatrix : Fin (coarse * 2 + T * 3) -> Matrix (Fin s) (Fin h) Real :=
    reluApproxConcatUpdateSchedule
      (reluApproxVectorBoxScanUpdateSchedule
        (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
        (T := coarse))
      (reluApproxFineRoundsUpdateSchedule T d r B
        Rfloor base trans scale)
  let updateBias : Fin (coarse * 2 + T * 3) -> Fin s -> Real :=
    reluApproxConcatUpdateBiasSchedule
      (reluApproxVectorBoxScanUpdateBiasSchedule
        (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
        (T := coarse))
      (reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale)
  rcases exists_reluApproxSignedMacroRecursionNet_exactDepth
      (reluApproxVectorBoxScanInputMatrix d
        (Fintype.card (ReLUApproxFineAccumulator d r)))
      (fun _ => 0) featureMatrix featureBias updateMatrix updateBias
      outputWeight outputBias hdepth hwidth with
    ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x active hRscan hpayload hactive hinactive digit correction center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hdigit
    hpayload_active hfloor
  rw [hNrealize x]
  simp only [featureMatrix, featureBias, updateMatrix, updateBias]
  rw [reluApproxCoarseScan_then_fineRounds_digit_exact
    Rscan Rselect Rfloor radius base lower upper payload active hRscan hpayload
    x hactive hinactive step shift scale trans digit correction hdigit center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hpayload_active hfloor]

/-! ## Deep boundary checking and clipping -/

/-- The paper's boundary checker is the complement of the serial sum of
unit-payload box gates.  It is zero on the safely selected cell and one when
the input is outside every box. -/
noncomputable def reluApproxBoundaryCheck {d T : Nat} (R : Real)
    (lower upper : Fin T -> Fin d -> Real) (x : Fin d -> Real) : Real :=
  1 - Finset.univ.sum (fun i : Fin T =>
    reluApproxBoxGate R (lower i) (upper i) x 1)

/-- The hierarchical fine-scan checker is the complement of the unit gate
mass stored in the distinguished selected-coefficient register. -/
private theorem one_sub_reluApproxFineSelectedUnitMass_eq_boundaryCheck
    {d r T : Nat} (R radius : Real) (x : Fin d -> Real)
    (center : Nat -> Fin d -> Real) :
    1 - reluApproxFineSelectedCoefficientRecursion (r := r) (T := T)
        R radius x center (fun _ _ => 1) (fun _ => 0) T
        (reluApproxZeroTaylorMultiindex r d) =
      reluApproxBoundaryCheck R
        (fun (k : Fin T) q => center k.val q - radius)
        (fun (k : Fin T) q => center k.val q + radius) x := by
  rw [reluApproxFineSelectedUnitMass_eq_sum_boxGate]
  rfl

/-- On a unique safe cell the boundary checker vanishes exactly. -/
theorem reluApproxBoundaryCheck_eq_zero_of_unique
    {d T : Nat} {R : Real} (hR : 0 < R) (hRone : 1 <= R)
    (lower upper : Fin T -> Fin d -> Real) (x : Fin d -> Real)
    (active : Fin T)
    (hactive : forall q : Fin d,
      lower active q + R⁻¹ <= x q /\ x q <= upper active q - R⁻¹)
    (hinactive : forall i : Fin T, i ≠ active -> exists q : Fin d,
      x q <= lower i q \/ upper i q <= x q) :
    reluApproxBoundaryCheck R lower upper x = 0 := by
  rw [reluApproxBoundaryCheck,
    reluApprox_sum_boxGate_eq_payload_of_unique hR lower upper
      (fun _ : Fin T => (1 : Real)) x active]
  · ring
  · intro i
    simpa using hRone
  · exact hactive
  · exact hinactive

/-- If the input is outside every scanned box, the boundary checker is one. -/
theorem reluApproxBoundaryCheck_eq_one_of_all_outside
    {d T : Nat} {R : Real} (hR : 0 < R) (hRone : 1 <= R)
    (lower upper : Fin T -> Fin d -> Real) (x : Fin d -> Real)
    (houtside : forall i : Fin T, exists q : Fin d,
      x q <= lower i q \/ upper i q <= x q) :
    reluApproxBoundaryCheck R lower upper x = 1 := by
  unfold reluApproxBoundaryCheck
  have hzero : (Finset.univ.sum (fun i : Fin T =>
      reluApproxBoxGate R (lower i) (upper i) x 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact reluApproxBoxGate_eq_zero_of_outside hR
      (lower i) (upper i) x 1 (by simpa using hRone) (houtside i)
  rw [hzero]
  ring

/-- Unit-payload gates over boxes with pairwise disjoint interiors have total
mass at most one, including throughout their ReLU transition strips. -/
private theorem reluApprox_sum_unitBoxGate_le_one_of_pairwise_disjoint
    {d T : Nat} {R : Real} (hR : 0 < R) (hRone : 1 <= R)
    (lower upper : Fin T -> Fin d -> Real)
    (hdisjoint : forall i j : Fin T, i ≠ j -> exists q : Fin d,
      upper i q <= lower j q \/ upper j q <= lower i q)
    (x : Fin d -> Real) :
    Finset.univ.sum (fun i : Fin T =>
      reluApproxBoxGate R (lower i) (upper i) x 1) <= 1 := by
  classical
  by_cases hexists : exists active : Fin T,
      reluApproxBoxGate R (lower active) (upper active) x 1 ≠ 0
  · rcases hexists with ⟨active, hactive⟩
    have hnotout : ¬(exists q : Fin d,
        x q <= lower active q \/ upper active q <= x q) := by
      intro hout
      exact hactive (reluApproxBoxGate_eq_zero_of_outside hR
        (lower active) (upper active) x 1 (by simpa using hRone) hout)
    rw [Finset.sum_eq_single active]
    · exact reluApproxBoxGate_le_of_nonneg R
        (lower active) (upper active) x (by norm_num)
    · intro j _hj hj_ne
      rcases hdisjoint active j (Ne.symm hj_ne) with ⟨q, hsep | hsep⟩
      · apply reluApproxBoxGate_eq_zero_of_outside hR
          (lower j) (upper j) x 1 (by simpa using hRone)
        exact ⟨q, Or.inl (by
          by_contra hnot
          apply hnotout
          exact ⟨q, Or.inr (by linarith)⟩)⟩
      · apply reluApproxBoxGate_eq_zero_of_outside hR
          (lower j) (upper j) x 1 (by simpa using hRone)
        exact ⟨q, Or.inr (by
          by_contra hnot
          apply hnotout
          exact ⟨q, Or.inl (by linarith)⟩)⟩
    · simp
  · push_neg at hexists
    rw [Finset.sum_eq_zero]
    · norm_num
    · intro i _hi
      exact hexists i

/-- For a pairwise-disjoint box scan the complementary checker is a genuine
`[0,1]`-valued cutoff. -/
theorem reluApproxBoundaryCheck_mem_Icc_of_pairwise_disjoint
    {d T : Nat} {R : Real} (hR : 0 < R) (hRone : 1 <= R)
    (lower upper : Fin T -> Fin d -> Real)
    (hdisjoint : forall i j : Fin T, i ≠ j -> exists q : Fin d,
      upper i q <= lower j q \/ upper j q <= lower i q)
    (x : Fin d -> Real) :
    reluApproxBoundaryCheck R lower upper x ∈ Set.Icc (0 : Real) 1 := by
  have hsum_nonneg : 0 <= Finset.univ.sum (fun i : Fin T =>
      reluApproxBoxGate R (lower i) (upper i) x 1) := by
    exact Finset.sum_nonneg fun i _ =>
      reluApproxBoxGate_nonneg_of_nonneg R (lower i) (upper i) x (by norm_num)
  have hsum_le := reluApprox_sum_unitBoxGate_le_one_of_pairwise_disjoint
    hR hRone lower upper hdisjoint x
  unfold reluApproxBoundaryCheck
  constructor <;> linarith

/-- Turn the output of a serial unit-box scan into its complementary boundary
checker without changing depth, width, or hidden layers. -/
private noncomputable def reluApproxBoundaryCheckNet {d : Nat}
    (N : FullyConnectedReLUNet d) : FullyConnectedReLUNet d where
  depth := N.depth
  width := N.width
  input := N.input
  hidden := N.hidden
  outputWeight := fun j => -N.outputWeight j
  outputBias := 1 - N.outputBias

@[simp] theorem reluApproxBoundaryCheckNet_depth {d : Nat}
    (N : FullyConnectedReLUNet d) :
    (reluApproxBoundaryCheckNet N).depth = N.depth := rfl

@[simp] theorem reluApproxBoundaryCheckNet_width {d : Nat}
    (N : FullyConnectedReLUNet d) :
    (reluApproxBoundaryCheckNet N).width = N.width := rfl

@[simp] theorem reluApproxBoundaryCheckNet_parameterCount {d : Nat}
    (N : FullyConnectedReLUNet d) :
    (reluApproxBoundaryCheckNet N).parameterCount = N.parameterCount := rfl

/-- Exact realization of the output-complement transformation. -/
private theorem reluApproxBoundaryCheckNet_realize {d : Nat}
    (N : FullyConnectedReLUNet d) (x : Fin d -> Real) :
    (reluApproxBoundaryCheckNet N).realize x = 1 - N.realize x := by
  have hhidden : forall t,
      (reluApproxBoundaryCheckNet N).hiddenState x t = N.hiddenState x t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        by_cases ht : t < N.depth - 1
        · rw [FullyConnectedReLUNet.hiddenState,
            FullyConnectedReLUNet.hiddenState]
          simp only [reluApproxBoundaryCheckNet, dif_pos ht]
          simpa only using congrArg
            (fun z => (N.hidden ⟨t, ht⟩).reluApply z) ih
        · rw [FullyConnectedReLUNet.hiddenState,
            FullyConnectedReLUNet.hiddenState]
          simp only [reluApproxBoundaryCheckNet, dif_neg ht]
          exact ih
  change
    (Finset.univ.sum fun j : Fin N.width =>
        -N.outputWeight j *
          (reluApproxBoundaryCheckNet N).hiddenState x (N.depth - 1) j) +
      (1 - N.outputBias) =
        1 - ((Finset.univ.sum fun j : Fin N.width =>
          N.outputWeight j * N.hiddenState x (N.depth - 1) j) + N.outputBias)
  rw [hhidden]
  have hsum :
      (Finset.univ.sum fun j : Fin N.width =>
        -N.outputWeight j * N.hiddenState x (N.depth - 1) j) =
        -(Finset.univ.sum fun j : Fin N.width =>
          N.outputWeight j * N.hiddenState x (N.depth - 1) j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hsum]
  ring

/-- A concrete deep checker network obtained from the existing fixed-width
serial box scan. -/
theorem exists_reluApproxBoundaryCheckNet {d T : Nat} (hd : 0 < d)
    (R : Real) (lower upper : Fin T -> Fin d -> Real) :
    exists N : FullyConnectedReLUNet d,
      0 < N.depth /\
      N.depth <= (T + 1) * (2 + 1) /\
      N.width <= 2 * d + ((d + d) + 2) + 3 /\
      N.parameterCount <=
        fullyConnectedReLUParameterCount d ((T + 1) * (2 + 1))
          (2 * d + ((d + d) + 2) + 3) /\
      forall x : Fin d -> Real,
        N.realize x = reluApproxBoundaryCheck R lower upper x := by
  obtain ⟨N, hdepth, hdepth_le, hwidth, hparam, hrealize⟩ :=
    exists_reluApproxBoxGateScanNet hd R lower upper
      (fun _ : Fin T => (1 : Real))
  refine ⟨reluApproxBoundaryCheckNet N, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hdepth
  · simpa using hdepth_le
  · simpa using hwidth
  · simpa using hparam
  · intro x
    rw [reluApproxBoundaryCheckNet_realize, hrealize]
    rfl

/-- The final robustification used in the paper: subtract the checker penalty
from both signed halves of a bounded raw output. -/
noncomputable def reluApproxBoundaryClip (B raw check : Real) : Real :=
  relu (raw - B * check) - relu (-raw - B * check)

/-- Boundary clipping cannot increase the magnitude of the raw branch output
when its clipping scale and checker are nonnegative. -/
theorem abs_reluApproxBoundaryClip_le_abs
    {B raw check : Real} (hB : 0 <= B) (hcheck : 0 <= check) :
    |reluApproxBoundaryClip B raw check| <= |raw| := by
  let penalty := B * check
  have hpenalty : 0 <= penalty := mul_nonneg hB hcheck
  unfold reluApproxBoundaryClip relu
  change |max (raw - penalty) 0 - max (-raw - penalty) 0| <= |raw|
  by_cases hraw : 0 <= raw
  · have hsecond : max (-raw - penalty) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hsecond, sub_zero, abs_of_nonneg (le_max_right _ _), abs_of_nonneg hraw]
    exact max_le (by linarith) hraw
  · have hraw' : raw <= 0 := le_of_not_ge hraw
    have hfirst : max (raw - penalty) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hfirst, zero_sub, abs_neg,
      abs_of_nonneg (le_max_right _ _), abs_of_nonpos hraw']
    exact max_le (by linarith) (by linarith)

private theorem abs_reluApproxBoundaryClip_le
    {B raw check : Real} (hB : 0 <= B) (hcheck : 0 <= check)
    (hraw : |raw| <= B) :
    |reluApproxBoundaryClip B raw check| <= B :=
  le_trans (abs_reluApproxBoundaryClip_le_abs hB hcheck) hraw

/-- Quantitative form of the clipping estimate.  As the checker moves from
zero to one, the surviving signed output is bounded by the complementary gate
mass.  This is the estimate used on the thin boundary shell in the paper. -/
private theorem abs_reluApproxBoundaryClip_le_complement
    {B raw check : Real} (hB : 0 <= B) (hraw : |raw| <= B)
    (hcheck : check ∈ Set.Icc (0 : Real) 1) :
    |reluApproxBoundaryClip B raw check| <= B * (1 - check) := by
  have hpenalty : 0 <= B * check := mul_nonneg hB hcheck.1
  have hcomp : 0 <= B * (1 - check) :=
    mul_nonneg hB (sub_nonneg.mpr hcheck.2)
  unfold reluApproxBoundaryClip relu
  change |max (raw - B * check) 0 - max (-raw - B * check) 0| <=
    B * (1 - check)
  by_cases hraw_nonneg : 0 <= raw
  · have hnegative : max (-raw - B * check) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hnegative, sub_zero, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hraw_le : raw <= B := le_trans (le_abs_self raw) hraw
      linarith
    · exact hcomp
  · have hraw_nonpos : raw <= 0 := le_of_not_ge hraw_nonneg
    have hpositive : max (raw - B * check) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hpositive, zero_sub, abs_neg,
      abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hnegraw_le : -raw <= B := le_trans (neg_le_abs raw) hraw
      linarith
    · exact hcomp

/-- A reliable lower checker controls the clipped output even when the actual
checker is a larger maximum involving another branch whose global range is not
known.  This is the form needed by the coarse/fine paper hierarchy. -/
theorem abs_reluApproxBoundaryClip_le_complement_of_le
    {B raw check gate : Real} (hB : 0 <= B) (hraw : |raw| <= B)
    (hgate : gate ∈ Set.Icc (0 : Real) 1) (hle : gate <= check) :
    |reluApproxBoundaryClip B raw check| <= B * (1 - gate) := by
  have hcheck : 0 <= check := le_trans hgate.1 hle
  have hpenalty : 0 <= B * check := mul_nonneg hB hcheck
  have hcomp : 0 <= B * (1 - gate) :=
    mul_nonneg hB (sub_nonneg.mpr hgate.2)
  unfold reluApproxBoundaryClip relu
  change |max (raw - B * check) 0 - max (-raw - B * check) 0| <=
    B * (1 - gate)
  by_cases hraw_nonneg : 0 <= raw
  · have hnegative : max (-raw - B * check) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hnegative, sub_zero, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hraw_le : raw <= B := le_trans (le_abs_self raw) hraw
      have hBcheck : B * gate <= B * check :=
        mul_le_mul_of_nonneg_left hle hB
      linarith
    · exact hcomp
  · have hraw_nonpos : raw <= 0 := le_of_not_ge hraw_nonneg
    have hpositive : max (raw - B * check) 0 = 0 :=
      max_eq_right (by linarith)
    rw [hpositive, zero_sub, abs_neg,
      abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hnegraw_le : -raw <= B := le_trans (neg_le_abs raw) hraw
      have hBcheck : B * gate <= B * check :=
        mul_le_mul_of_nonneg_left hle hB
      linarith
    · exact hcomp

/-- With a zero checker the robustified output is the raw output. -/
theorem reluApproxBoundaryClip_eq_raw (B raw : Real) :
    reluApproxBoundaryClip B raw 0 = raw := by
  unfold reluApproxBoundaryClip
  simp only [mul_zero, sub_zero]
  exact reluApproxSignedEncode_sub raw

/-- With a unit checker, a raw value bounded by `B` is suppressed exactly. -/
private theorem reluApproxBoundaryClip_eq_zero
    {B raw : Real} (_hB : 0 <= B) (hraw : |raw| <= B) :
    reluApproxBoundaryClip B raw 1 = 0 := by
  have hpos : raw - B <= 0 := by
    exact sub_nonpos.mpr (le_trans (le_abs_self raw) hraw)
  have hneg : -raw - B <= 0 := by
    exact sub_nonpos.mpr (le_trans (neg_le_abs raw) hraw)
  simp [reluApproxBoundaryClip, relu, hpos, hneg]

/-- One hidden layer realizes the boundary clipping map on the pair
`(raw, check)`. -/
noncomputable def reluApproxBoundaryClipNet (B : Real) :
    FullyConnectedReLUNet 2 where
  depth := 1
  width := 2
  input :=
    { weight := fun o i =>
        if o = 0 then
          if i = 0 then 1 else -B
        else if i = 0 then -1 else -B
      bias := fun _ => 0 }
  hidden := fun i => Fin.elim0 i
  outputWeight := fun o => if o = 0 then 1 else -1
  outputBias := 0

private theorem reluApproxBoundaryClipNet_realize (B : Real) (y : Fin 2 -> Real) :
    (reluApproxBoundaryClipNet B).realize y =
      reluApproxBoundaryClip B (y 0) (y 1) := by
  simp [FullyConnectedReLUNet.realize, FullyConnectedReLUNet.hiddenState,
    reluApproxBoundaryClipNet, DenseLayer.reluApply, reluVec,
    DenseLayer.apply, reluApproxBoundaryClip]
  ring

/-- A one-hidden-layer ReLU network realizing the maximum of two signed
inputs.  The second input is carried through its positive and negative parts. -/
noncomputable def reluApproxBinaryMaxNet : FullyConnectedReLUNet 2 where
  depth := 1
  width := 3
  input :=
    { weight := fun o i =>
        if o = 0 then
          if i = 0 then 1 else -1
        else if o = 1 then
          if i = 1 then 1 else 0
        else if i = 1 then -1 else 0
      bias := fun _ => 0 }
  hidden := fun i => Fin.elim0 i
  outputWeight := fun o => if o = 2 then -1 else 1
  outputBias := 0

private theorem reluApproxBinaryMaxNet_realize (y : Fin 2 -> Real) :
    reluApproxBinaryMaxNet.realize y = max (y 0) (y 1) := by
  simp [FullyConnectedReLUNet.realize, FullyConnectedReLUNet.hiddenState,
    reluApproxBinaryMaxNet, DenseLayer.reluApply, reluVec, DenseLayer.apply,
    Fin.sum_univ_succ]
  rw [show y 0 + -y 1 = y 0 - y 1 by ring]
  have hsigned := reluApproxSignedEncode_sub (y 1)
  rw [show relu (y 1) + -relu (-y 1) = y 1 by linarith]
  unfold relu
  by_cases h : y 0 <= y 1
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h' : y 1 <= y 0 := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (sub_nonneg.mpr h')]
    ring

/-- Serial macro program which retains three scalar subnetworks, takes the
maximum of the last two, and clips the first by that boundary signal. -/
noncomputable def reluApproxThreeBranchBoundaryClipProgram
    {d : Nat} (Bclip : Real)
    (Nraw Ncoarse Nfine : FullyConnectedReLUNet d) :
    ReLUApproxMacroProgram d :=
  let P0 := reluApproxInputRegisterProgram d 3
  let input0 : Fin d -> Fin P0.stateSize := fun q => Fin.castAdd 3 q
  let raw0 : Fin P0.stateSize := Fin.natAdd d ⟨0, by omega⟩
  let coarse0 : Fin P0.stateSize := Fin.natAdd d ⟨1, by omega⟩
  let fine0 : Fin P0.stateSize := Fin.natAdd d ⟨2, by omega⟩
  let P1 := P0.appendNetwork Nraw raw0
    (reluApproxRegisterReadMatrix Nraw.width input0) (fun _ => 0)
  let lift1 : Fin P0.stateSize -> Fin P1.stateSize := Fin.castAdd Nraw.width
  let P2 := P1.appendNetwork Ncoarse (lift1 coarse0)
    (reluApproxRegisterReadMatrix Ncoarse.width (fun q => lift1 (input0 q)))
    (fun _ => 0)
  let lift2 : Fin P1.stateSize -> Fin P2.stateSize := Fin.castAdd Ncoarse.width
  let P3 := P2.appendNetwork Nfine (lift2 (lift1 fine0))
    (reluApproxRegisterReadMatrix Nfine.width
      (fun q => lift2 (lift1 (input0 q)))) (fun _ => 0)
  let lift3 : Fin P2.stateSize -> Fin P3.stateSize := Fin.castAdd Nfine.width
  let raw3 : Fin P3.stateSize := lift3 (lift2 (lift1 raw0))
  let coarse3 : Fin P3.stateSize := lift3 (lift2 (lift1 coarse0))
  let fine3 : Fin P3.stateSize := lift3 (lift2 (lift1 fine0))
  let maxSrc : Fin 2 -> Fin P3.stateSize := Fin.cases coarse3 (fun _ => fine3)
  let P4 := P3.appendNetwork reluApproxBinaryMaxNet coarse3
    (reluApproxRegisterReadMatrix reluApproxBinaryMaxNet.width maxSrc)
    (fun _ => 0)
  let lift4 : Fin P3.stateSize -> Fin P4.stateSize :=
    Fin.castAdd reluApproxBinaryMaxNet.width
  let raw4 : Fin P4.stateSize := lift4 raw3
  let coarse4 : Fin P4.stateSize := lift4 coarse3
  let clipSrc : Fin 2 -> Fin P4.stateSize := Fin.cases raw4 (fun _ => coarse4)
  P4.appendNetwork (reluApproxBoundaryClipNet Bclip) raw4
    (reluApproxRegisterReadMatrix (reluApproxBoundaryClipNet Bclip).width clipSrc)
    (fun _ => 0)

/-- Exact output identity for the serial three-branch boundary-clipping
program.  The proof uses only persistent-register append laws, so resource
accounting remains definitionally visible from the concrete program. -/
private theorem exists_reluApproxThreeBranchBoundaryClipProgram_output
    {d : Nat} (Bclip : Real)
    (Nraw Ncoarse Nfine : FullyConnectedReLUNet d) :
    exists out : Fin (reluApproxThreeBranchBoundaryClipProgram Bclip
      Nraw Ncoarse Nfine).stateSize,
      forall x : Fin d -> Real,
        (reluApproxThreeBranchBoundaryClipProgram Bclip
          Nraw Ncoarse Nfine).run x out =
          reluApproxBoundaryClip Bclip (Nraw.realize x)
            (max (Ncoarse.realize x) (Nfine.realize x)) := by
  let P0 := reluApproxInputRegisterProgram d 3
  let input0 : Fin d -> Fin P0.stateSize := fun q => Fin.castAdd 3 q
  let raw0 : Fin P0.stateSize := Fin.natAdd d ⟨0, by omega⟩
  let coarse0 : Fin P0.stateSize := Fin.natAdd d ⟨1, by omega⟩
  let fine0 : Fin P0.stateSize := Fin.natAdd d ⟨2, by omega⟩
  let P1 := P0.appendNetwork Nraw raw0
    (reluApproxRegisterReadMatrix Nraw.width input0) (fun _ => 0)
  let lift1 : Fin P0.stateSize -> Fin P1.stateSize := Fin.castAdd Nraw.width
  let P2 := P1.appendNetwork Ncoarse (lift1 coarse0)
    (reluApproxRegisterReadMatrix Ncoarse.width (fun q => lift1 (input0 q)))
    (fun _ => 0)
  let lift2 : Fin P1.stateSize -> Fin P2.stateSize := Fin.castAdd Ncoarse.width
  let P3 := P2.appendNetwork Nfine (lift2 (lift1 fine0))
    (reluApproxRegisterReadMatrix Nfine.width
      (fun q => lift2 (lift1 (input0 q)))) (fun _ => 0)
  let lift3 : Fin P2.stateSize -> Fin P3.stateSize := Fin.castAdd Nfine.width
  let raw3 : Fin P3.stateSize := lift3 (lift2 (lift1 raw0))
  let coarse3 : Fin P3.stateSize := lift3 (lift2 (lift1 coarse0))
  let fine3 : Fin P3.stateSize := lift3 (lift2 (lift1 fine0))
  let maxSrc : Fin 2 -> Fin P3.stateSize := Fin.cases coarse3 (fun _ => fine3)
  let P4 := P3.appendNetwork reluApproxBinaryMaxNet coarse3
    (reluApproxRegisterReadMatrix reluApproxBinaryMaxNet.width maxSrc)
    (fun _ => 0)
  let lift4 : Fin P3.stateSize -> Fin P4.stateSize :=
    Fin.castAdd reluApproxBinaryMaxNet.width
  let raw4 : Fin P4.stateSize := lift4 raw3
  let coarse4 : Fin P4.stateSize := lift4 coarse3
  let clipSrc : Fin 2 -> Fin P4.stateSize := Fin.cases raw4 (fun _ => coarse4)
  let P5 := P4.appendNetwork (reluApproxBoundaryClipNet Bclip) raw4
    (reluApproxRegisterReadMatrix
      (reluApproxBoundaryClipNet Bclip).width clipSrc) (fun _ => 0)
  let out : Fin P5.stateSize :=
    Fin.castAdd (reluApproxBoundaryClipNet Bclip).width raw4
  change exists out : Fin P5.stateSize, forall x : Fin d -> Real,
    P5.run x out = reluApproxBoundaryClip Bclip (Nraw.realize x)
      (max (Ncoarse.realize x) (Nfine.realize x))
  refine ⟨out, ?_⟩
  intro x
  rw [show P5.run x out =
      (P4.appendNetwork (reluApproxBoundaryClipNet Bclip) raw4
        (reluApproxRegisterReadMatrix
          (reluApproxBoundaryClipNet Bclip).width clipSrc)
        (fun _ => 0)).run x
          (Fin.castAdd (reluApproxBoundaryClipNet Bclip).width raw4) by rfl]
  rw [ReLUApproxMacroProgram.run_appendNetwork_registerRead]
  simp only [Fin.addCases_left, if_pos]
  rw [reluApproxBoundaryClipNet_realize]
  have hP4raw : P4.run x raw4 = Nraw.realize x := by
    have hraw3 : raw3 ≠ coarse3 := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [raw3, coarse3, lift3, lift2, lift1, raw0, coarse0] at hval
    rw [show P4.run x raw4 = P3.run x raw3 by
      exact P3.run_appendNetwork_registerRead_of_ne
        reluApproxBinaryMaxNet coarse3 raw3 maxSrc x hraw3]
    have hraw2 : lift2 (lift1 raw0) ≠ lift2 (lift1 fine0) := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [lift2, lift1, raw0, fine0] at hval
    rw [show P3.run x raw3 = P2.run x (lift2 (lift1 raw0)) by
      exact P2.run_appendNetwork_registerRead_of_ne Nfine
        (lift2 (lift1 fine0)) (lift2 (lift1 raw0))
        (fun q => lift2 (lift1 (input0 q))) x hraw2]
    have hraw1 : lift1 raw0 ≠ lift1 coarse0 := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [lift1, raw0, coarse0] at hval
    rw [show P2.run x (lift2 (lift1 raw0)) = P1.run x (lift1 raw0) by
      exact P1.run_appendNetwork_registerRead_of_ne Ncoarse
        (lift1 coarse0) (lift1 raw0) (fun q => lift1 (input0 q)) x hraw1]
    rw [show P1.run x (lift1 raw0) = Nraw.realize
        (fun q => P0.run x (input0 q)) by
      exact P0.run_appendNetwork_registerRead_at_dst Nraw raw0 input0 x]
    congr 1
    funext q
    simp [input0, P0, reluApproxInputRegisterProgram_run]
  have hP4coarse : P4.run x coarse4 =
      max (Ncoarse.realize x) (Nfine.realize x) := by
    dsimp only [P4, coarse4, lift4]
    rw [ReLUApproxMacroProgram.run_appendNetwork_registerRead]
    simp only [Fin.addCases_left, if_pos]
    rw [reluApproxBinaryMaxNet_realize]
    congr 1
    · simp only [maxSrc, Fin.cases_zero]
      have hcoarse2 : lift2 (lift1 coarse0) ≠ lift2 (lift1 fine0) := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [lift2, lift1, coarse0, fine0] at hval
      rw [show P3.run x coarse3 = P2.run x (lift2 (lift1 coarse0)) by
        exact P2.run_appendNetwork_registerRead_of_ne Nfine
          (lift2 (lift1 fine0)) (lift2 (lift1 coarse0))
          (fun q => lift2 (lift1 (input0 q))) x hcoarse2]
      rw [show P2.run x (lift2 (lift1 coarse0)) = Ncoarse.realize
          (fun q => P1.run x (lift1 (input0 q))) by
        exact P1.run_appendNetwork_registerRead_at_dst Ncoarse
          (lift1 coarse0) (fun q => lift1 (input0 q)) x]
      congr 1
      funext q
      have hinputRaw : input0 q ≠ raw0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [input0, raw0] at hval
        exact (Nat.ne_of_lt q.isLt) hval
      rw [show P1.run x (lift1 (input0 q)) = P0.run x (input0 q) by
        exact P0.run_appendNetwork_registerRead_of_ne Nraw raw0
          (input0 q) input0 x hinputRaw]
      simp [input0, P0, reluApproxInputRegisterProgram_run]
    · have hmaxSrc1 : maxSrc 1 = fine3 := rfl
      rw [hmaxSrc1]
      rw [show P3.run x fine3 = Nfine.realize
          (fun q => P2.run x (lift2 (lift1 (input0 q)))) by
        exact P2.run_appendNetwork_registerRead_at_dst Nfine
          (lift2 (lift1 fine0)) (fun q => lift2 (lift1 (input0 q))) x]
      congr 1
      funext q
      have hinputCoarse : lift1 (input0 q) ≠ lift1 coarse0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [lift1, input0, coarse0] at hval
        omega
      rw [show P2.run x (lift2 (lift1 (input0 q))) =
          P1.run x (lift1 (input0 q)) by
        exact P1.run_appendNetwork_registerRead_of_ne Ncoarse
          (lift1 coarse0) (lift1 (input0 q))
          (fun q => lift1 (input0 q)) x hinputCoarse]
      have hinputRaw : input0 q ≠ raw0 := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [input0, raw0] at hval
        exact (Nat.ne_of_lt q.isLt) hval
      rw [show P1.run x (lift1 (input0 q)) = P0.run x (input0 q) by
        exact P0.run_appendNetwork_registerRead_of_ne Nraw raw0
          (input0 q) input0 x hinputRaw]
      simp [input0, P0, reluApproxInputRegisterProgram_run]
  have hclipSrc0 : clipSrc 0 = raw4 := rfl
  have hclipSrc1 : clipSrc 1 = coarse4 := rfl
  rw [hclipSrc0, hclipSrc1]
  rw [hP4raw, hP4coarse]

/-- Compile the three-branch robustifier to an exact-depth fully connected
network.  The resource hypotheses expose the concrete serial macro program,
while the realization theorem hides all persistent-register bookkeeping. -/
theorem exists_reluApproxThreeBranchBoundaryClipNet_exactDepth
    {d D W : Nat} (Bclip : Real)
    (Nraw Ncoarse Nfine : FullyConnectedReLUNet d)
    (hdepth : 2 * (reluApproxThreeBranchBoundaryClipProgram Bclip
      Nraw Ncoarse Nfine).stepCount + 1 <= D)
    (hwidth :
      let P := reluApproxThreeBranchBoundaryClipProgram Bclip
        Nraw Ncoarse Nfine
      (P.stateSize + P.stateSize) + P.featureSize <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall x : Fin d -> Real,
          N.realize x = reluApproxBoundaryClip Bclip (Nraw.realize x)
            (max (Ncoarse.realize x) (Nfine.realize x)) := by
  obtain ⟨out, hout⟩ := exists_reluApproxThreeBranchBoundaryClipProgram_output
    Bclip Nraw Ncoarse Nfine
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_fullyConnectedReLUNet_of_macroProgram_register
      (reluApproxThreeBranchBoundaryClipProgram Bclip Nraw Ncoarse Nfine)
      out hdepth hwidth
  exact ⟨N, hNdepth, hNwidth, hNparam, fun x => (hNrealize x).trans (hout x)⟩

/-! ## Terminal Taylor evaluation after the two-pass machine -/

/-- The state size shared by the coarse scan and all fine Taylor rounds. -/
abbrev ReLUApproxCoarseFineStateSize (d r : Nat) : Nat :=
  reluApproxVectorBoxScanStateSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))

/-- The feature size shared by the concatenated coarse and fine schedules. -/
abbrev ReLUApproxCoarseFineFeatureSize (d r B : Nat) : Nat :=
  let hscan := reluApproxVectorBoxScanFeatureSize d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  hscan + (hscan + fineTaylorFeatureSize d r B)

/-- Number of signed-state macros in one coarse-scan/fine-round program. -/
abbrev ReLUApproxCoarseFineStepCount (coarse T : Nat) : Nat :=
  coarse * 2 + T * 3

/-- Concrete feature schedule of the complete two-pass machine. -/
private noncomputable def reluApproxCoarseFineFeatureSchedule
    {coarse T d r B : Nat} (Rscan Rselect Rfloor radius base : Real) :=
  reluApproxConcatFeatureSchedule
    (reluApproxVectorBoxScanFeatureSchedule
      (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
      (T := coarse) Rscan)
    (reluApproxFineRoundsFeatureSchedule T d r B
      Rselect Rfloor radius base)

/-- Bias schedule accompanying `reluApproxCoarseFineFeatureSchedule`. -/
private noncomputable def reluApproxCoarseFineFeatureBiasSchedule
    {coarse T d r B : Nat} (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real) :=
  reluApproxConcatFeatureBiasSchedule
    (reluApproxVectorBoxScanFeatureBiasSchedule Rscan lower upper
      (fun i k => payload i
        ((reluApproxFineAccumulatorEquivFin d r).symm k)))
    (reluApproxFineRoundsFeatureBiasSchedule T d r B
      Rselect Rfloor radius)

/-- Update schedule accompanying `reluApproxCoarseFineFeatureSchedule`. -/
private noncomputable def reluApproxCoarseFineUpdateSchedule
    {coarse T d r B : Nat} (Rfloor base : Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (scale : TaylorMultiindex r d -> Real) :=
  reluApproxConcatUpdateSchedule
    (reluApproxVectorBoxScanUpdateSchedule
      (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
      (T := coarse))
    (reluApproxFineRoundsUpdateSchedule T d r B Rfloor base trans scale)

/-- Update-bias schedule accompanying `reluApproxCoarseFineFeatureSchedule`. -/
private noncomputable def reluApproxCoarseFineUpdateBiasSchedule
    {coarse T d r : Nat}
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real) :=
  reluApproxConcatUpdateBiasSchedule
    (reluApproxVectorBoxScanUpdateBiasSchedule
      (d := d) (m := Fintype.card (ReLUApproxFineAccumulator d r))
      (T := coarse))
    (reluApproxFineRoundsUpdateBiasSchedule T d r step shift scale)

/-- The complete coarse/fine state machine as a composable macro program. -/
noncomputable def reluApproxCoarseFineProgram
    {coarse T d r B : Nat} (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real) :
    ReLUApproxMacroProgram d where
  stateSize := ReLUApproxCoarseFineStateSize d r
  featureSize := ReLUApproxCoarseFineFeatureSize d r B
  stepCount := ReLUApproxCoarseFineStepCount coarse T
  inputMatrix := reluApproxVectorBoxScanInputMatrix d
    (Fintype.card (ReLUApproxFineAccumulator d r))
  inputBias := fun _ => 0
  featureMatrix := reluApproxCoarseFineFeatureSchedule
    Rscan Rselect Rfloor radius base
  featureBias := reluApproxCoarseFineFeatureBiasSchedule
    Rscan Rselect Rfloor radius base lower upper payload
  updateMatrix := reluApproxCoarseFineUpdateSchedule Rfloor base trans scale
  updateBias := reluApproxCoarseFineUpdateBiasSchedule step shift scale

/-- State-level correctness of the packaged coarse/fine program. -/
private theorem reluApproxCoarseFineProgram_run_eq_of_unique
    {coarse T d r B : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (active : Fin coarse) (hRscan : 0 < Rscan)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (x : Fin d -> Real)
    (hactive : forall q,
      lower active q + Rscan⁻¹ <= x q /\ x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i, i ≠ active -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a, (digit k a : Int) = correction k a + (shift : Int))
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (selectedCenter0 : Fin d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (hpayload_active : payload active =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real)) :
    (reluApproxCoarseFineProgram (B := B) Rscan Rselect Rfloor radius base
      lower upper payload step shift scale trans).run x =
      fun i => reluApproxFineMachineStateValue x
        (reluApproxTaylorCenterRecursion step center0 T)
        (reluApproxTaylorCoefficientRecursion
          scale trans correction coefficient0 T)
        (reluApproxTaylorTailRecursion base digit tail0 T)
        (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0) selectedCenter0 T)
        (reluApproxFineSelectedCoefficientRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
          selectedCoefficient0 T)
        ((reluApproxFineMachineEquivFin d r).symm i) := by
  simpa [ReLUApproxMacroProgram.run, reluApproxCoarseFineProgram,
    ReLUApproxCoarseFineStepCount, ReLUApproxCoarseFineFeatureSize,
    ReLUApproxCoarseFineStateSize] using
    (reluApproxCoarseScan_then_fineRounds_digit_exact
      Rscan Rselect Rfloor radius base lower upper payload active hRscan hpayload
      x hactive hinactive step shift scale trans digit correction hdigit center0
      coefficient0 tail0 selectedCenter0 selectedCoefficient0 hpayload_active hfloor)

/-- A coarse/fine program whose distinguished Taylor channel stays equal to
one realizes the fine-boundary checker by a single terminal linear readout.
The coarse scan keeps the construction linear in `coarse + T`, rather than in
the number of coarse/fine pairs. -/
private theorem reluApproxCoarseFineProgram_boundaryCheck_readout_of_unique
    {coarse T d r B : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (active : Fin coarse) (hRscan : 0 < Rscan)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (x : Fin d -> Real)
    (hactive : forall q,
      lower active q + Rscan⁻¹ <= x q /\ x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i, i ≠ active -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (hdigit : forall k a, (digit k a : Int) = correction k a + (shift : Int))
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (hpayload_active : payload active =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState (fun _ => 0) (fun _ => 0)))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real))
    (hunit : forall k : Fin T,
      reluApproxTaylorCoefficientRecursion scale trans correction coefficient0
          k.val (reluApproxZeroTaylorMultiindex r d) = 1) :
    (Finset.univ.sum fun i : Fin (ReLUApproxCoarseFineStateSize d r) =>
        reluApproxFineBoundaryCheckOutputWeight d r i *
          (reluApproxCoarseFineProgram (B := B)
            Rscan Rselect Rfloor radius base lower upper payload step shift scale trans).run x i) + 1 =
      reluApproxBoundaryCheck Rselect
        (fun (k : Fin T) q =>
          reluApproxTaylorCenterRecursion step center0 k.val q - radius)
        (fun (k : Fin T) q =>
          reluApproxTaylorCenterRecursion step center0 k.val q + radius) x := by
  rw [reluApproxCoarseFineProgram_run_eq_of_unique
    Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
    active hRscan hpayload x hactive hinactive digit correction hdigit center0
    coefficient0 tail0 (fun _ => 0) (fun _ => 0) hpayload_active hfloor]
  rw [reluApproxFineBoundaryCheckOutputWeight_stateValue]
  unfold reluApproxBoundaryCheck
  rw [reluApproxFineSelectedCoefficientRecursion_eq_sum
    Rselect radius x (reluApproxTaylorCenterRecursion step center0)
    (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
    (fun _ => 0) T le_rfl, zero_add, <- Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hunit k]

/-- The zero-code instance of the coarse/fine machine compiles a hierarchical
fine-boundary checker.  Its coarse scan loads the path belonging to the active
coarse block, while a distinguished Taylor register remains identically one;
the terminal readout is therefore the complement of the accumulated fine-box
gate mass. -/
theorem exists_reluApproxHierarchicalFineBoundaryCheckNet_exactDepth
    {coarse T d r D W : Nat}
    (Rscan Rselect radius : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (path : Fin coarse -> Nat -> Fin d -> Real)
    (step : Fin T -> Fin d -> Real)
    (hRscan : 0 < Rscan)
    (hpayload : forall b (p : ReLUApproxFineAccumulator d r),
      |(Sum.elim
          (reluApproxTaylorPayloadState (r := r) (path b 0)
            (fun _ : TaylorMultiindex r d => 1)
            (fun _ : TaylorMultiindex r d => 0))
          (reluApproxSelectedTaylorState (r := r)
            (fun _ : Fin d => 0)
            (fun _ : TaylorMultiindex r d => 0))) p| <= Rscan)
    (hpath : forall b k, forall hk : k < T,
      path b (k + 1) - path b k = step ⟨k, hk⟩)
    (hdepth : 2 * (coarse * 2 + T * 3) + 1 <= D)
    (hwidth :
      let s := reluApproxVectorBoxScanStateSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let hscan := reluApproxVectorBoxScanFeatureSize d
        (Fintype.card (ReLUApproxFineAccumulator d r))
      let h := hscan + (hscan + fineTaylorFeatureSize d r 0)
      (s + s) + h <= W) :
    exists N : FullyConnectedReLUNet d,
      N.depth = D /\ N.width <= W /\
        N.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (active : Fin coarse),
          (forall q,
            lower active q + Rscan⁻¹ <= x q /\
              x q <= upper active q - Rscan⁻¹) ->
          (forall i, i ≠ active -> exists q,
            x q <= lower i q \/ upper i q <= x q) ->
          N.realize x =
            reluApproxBoundaryCheck Rselect
              (fun (k : Fin T) q => path active k.val q - radius)
              (fun (k : Fin T) q => path active k.val q + radius) x := by
  classical
  let payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real := fun b =>
    Sum.elim
      (reluApproxTaylorPayloadState (path b 0) (fun _ => 1) (fun _ => 0))
      (reluApproxSelectedTaylorState (fun _ => 0) (fun _ => 0))
  let trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real :=
    fun _ a b => if b = a then 1 else 0
  obtain ⟨N, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxCoarseScan_then_fineRoundsNet_exactDepth
      (B := 0) Rscan Rselect 1 radius 1 lower upper payload step 0
        (fun _ => 0) trans (reluApproxFineBoundaryCheckOutputWeight d r) 1
        hdepth hwidth
  refine ⟨N, hNdepth, hNwidth, hNparam, ?_⟩
  intro x active hactive hinactive
  have hfloor : forall k : Fin T, forall a : TaylorMultiindex r d,
      truncatedFloorReLUFunction 1 0
          (1 * reluApproxTaylorTailRecursion (T := T) 1
            (fun _ _ => 0) (fun _ => 0) k.val a) = (0 : Nat) := by
    intro k a
    rw [reluApproxTaylorTailRecursion_zero]
    simp [truncatedFloorReLUFunction]
  rw [hNrealize x active hRscan (by simpa [payload] using hpayload)
    hactive hinactive (fun _ _ => 0) (fun _ _ => 0) (path active 0)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by simp) (by rfl) hfloor]
  rw [reluApproxFineBoundaryCheckOutputWeight_stateValue]
  have hcenter : forall n, n <= T ->
      reluApproxTaylorCenterRecursion step (path active 0) n = path active n :=
    reluApproxTaylorCenterRecursion_eq_path step (path active 0) (path active)
      rfl (hpath active)
  have hcoeff :
      reluApproxTaylorCoefficientRecursion (r := r) (d := d) (T := T)
          (fun _ => 0) trans (fun _ _ => 0) (fun _ => 1) =
        fun _ _ => 1 := by
    funext n
    simpa [trans] using
      (reluApproxTaylorCoefficientRecursion_identity_one
        (r := r) (d := d) (T := T) n)
  rw [hcoeff]
  rw [one_sub_reluApproxFineSelectedUnitMass_eq_boundaryCheck]
  congr 1
  · funext k q
    rw [hcenter k.val k.isLt.le]
  · funext k q
    rw [hcenter k.val k.isLt.le]

/-- Appending the dynamic Taylor-polynomial evaluator to the exact two-pass
machine evaluates the polynomial at the center and coefficient registers
selected during the fine scan.  This is an exact compiler identity; all
approximation error remains confined to the supplied evaluator network. -/
private theorem reluApproxCoarseScan_then_fineRounds_appendTaylorEvaluator_realize
    {coarse T d r B : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
    (dst : Fin (ReLUApproxCoarseFineStateSize d r))
    (x : Fin d -> Real) (active : Fin coarse)
    (hRscan : 0 < Rscan)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (hactive : forall q,
      lower active q + Rscan⁻¹ <= x q /\
        x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i, i ≠ active -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (selectedCenter0 : Fin d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (hpayload_active : payload active =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real)) :
    let inputMatrix := reluApproxInputMatrixWithZeroSuffix (w := N.width)
      (reluApproxVectorBoxScanInputMatrix d
        (Fintype.card (ReLUApproxFineAccumulator d r)))
    let inputBias := reluApproxInputBiasWithZeroSuffix (w := N.width)
      (fun _ : Fin (ReLUApproxCoarseFineStateSize d r) => 0)
    let featureMatrix := reluApproxConcatFeatureSchedule
        (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix (p := N.width)
        (reluApproxCoarseFineFeatureSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rscan Rselect Rfloor radius base))
      (reluApproxPersistentNetworkInstructionFeatureSchedule N
        (reluApproxTaylorEvaluationReadMatrix d r N.width) (fun _ => 0))
    let featureBias := reluApproxConcatFeatureBiasSchedule
        (reluApproxMacroScheduleWithPersistentSuffixFeatureBias (p := N.width)
        (reluApproxCoarseFineFeatureBiasSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rscan Rselect Rfloor radius base lower upper payload))
      (reluApproxPersistentNetworkInstructionFeatureBiasSchedule N
        (reluApproxTaylorEvaluationReadMatrix d r N.width) (fun _ => 0))
    let updateMatrix := reluApproxConcatUpdateSchedule
        (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix (p := N.width)
        (reluApproxCoarseFineUpdateSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rfloor base trans scale))
      (reluApproxPersistentNetworkInstructionUpdateSchedule N dst)
    let updateBias := reluApproxConcatUpdateBiasSchedule
        (reluApproxMacroScheduleWithPersistentSuffixUpdateBias (p := N.width)
        (reluApproxCoarseFineUpdateBiasSchedule
          (coarse := coarse) (T := T) (d := d) (r := r)
          step shift scale))
      (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst)
    let outputWeight : Fin (ReLUApproxCoarseFineStateSize d r + N.width) -> Real :=
      fun i => if i = Fin.castAdd N.width dst then 1 else 0
    (Finset.univ.sum fun i => outputWeight i *
      reluApproxSignedMacroRecursion inputMatrix inputBias featureMatrix
        featureBias updateMatrix updateBias x
        (ReLUApproxCoarseFineStepCount coarse T +
          (((N.depth - 1) + 1) + 1)) i) =
      N.realize (reluApproxTaylorEvaluationInputValue x
        (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0) selectedCenter0 T)
        (reluApproxFineSelectedCoefficientRecursion (T := T)
          Rselect radius x (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion
            scale trans correction coefficient0)
          selectedCoefficient0 T)) := by
  classical
  dsimp only
  rw [reluApproxSignedMacroRecursion_appendNetworkInstruction_realize]
  simp only [reluApproxCoarseFineFeatureSchedule,
    reluApproxCoarseFineFeatureBiasSchedule,
    reluApproxCoarseFineUpdateSchedule,
    reluApproxCoarseFineUpdateBiasSchedule]
  have hmachine := reluApproxCoarseScan_then_fineRounds_digit_exact
    Rscan Rselect Rfloor radius base lower upper payload active hRscan hpayload
    x hactive hinactive step shift scale trans digit correction hdigit center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hpayload_active hfloor
  rw [hmachine]
  rw [reluApproxTaylorEvaluationReadMatrix_exact]

/-- Appending the dynamic Taylor evaluator through the factorial-normalized
read matrix evaluates the Taylor polynomial with the coefficients required by
the multivariate Taylor formula. -/
private theorem reluApproxCoarseFineProgram_appendNormalizedTaylorEvaluator_run
    {coarse T d r B : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
    (dst : Fin (ReLUApproxCoarseFineStateSize d r))
    (x : Fin d -> Real) (active : Fin coarse)
    (hRscan : 0 < Rscan)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (hactive : forall q,
      lower active q + Rscan⁻¹ <= x q /\
        x q <= upper active q - Rscan⁻¹)
    (hinactive : forall i, i ≠ active -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (selectedCenter0 : Fin d -> Real)
    (selectedCoefficient0 : TaylorMultiindex r d -> Real)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (hpayload_active : payload active =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real)) :
    let P := reluApproxCoarseFineProgram (B := B)
      Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
    (P.appendNetwork N dst
      (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
      (fun _ => 0)).run x (Fin.castAdd N.width dst) =
      N.realize (reluApproxNormalizedTaylorEvaluationInputValue x
        (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
          (reluApproxTaylorCenterRecursion step center0) selectedCenter0 T)
        (reluApproxFineSelectedCoefficientRecursion (T := T)
          Rselect radius x (reluApproxTaylorCenterRecursion step center0)
          (reluApproxTaylorCoefficientRecursion
            scale trans correction coefficient0)
          selectedCoefficient0 T)) := by
  dsimp only
  rw [ReLUApproxMacroProgram.run_appendNetwork]
  simp only [Fin.addCases_left, if_pos]
  rw [reluApproxCoarseFineProgram_run_eq_of_unique
    Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
    active hRscan hpayload x hactive hinactive digit correction hdigit center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hpayload_active hfloor]
  apply congrArg N.realize
  simpa only using
    (reluApproxNormalizedTaylorEvaluationReadMatrix_exact
      (work := N.width) x
      (reluApproxTaylorCenterRecursion step center0 T)
      (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0 T)
      (reluApproxTaylorTailRecursion base digit tail0 T)
      (reluApproxFineSelectedCenterRecursion (T := T) Rselect radius x
        (reluApproxTaylorCenterRecursion step center0) selectedCenter0 T)
      (reluApproxFineSelectedCoefficientRecursion (T := T)
        Rselect radius x (reluApproxTaylorCenterRecursion step center0)
        (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
        selectedCoefficient0 T))

/-- Compile the complete coarse/fine state machine together with its
factorial-normalized Taylor evaluator.  The resulting scalar network retains
the exact selected-state semantics; approximation enters only through the
supplied evaluator network. -/
theorem exists_reluApproxCoarseFineNormalizedEvaluatorNet_exactDepth
    {coarse T d r B D W : Nat}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
    (dst : Fin (ReLUApproxCoarseFineStateSize d r))
    (hdepth :
      let P := reluApproxCoarseFineProgram (B := B)
        Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
      let Q := P.appendNetwork N dst
        (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
        (fun _ => 0)
      2 * Q.stepCount + 1 <= D)
    (hwidth :
      let P := reluApproxCoarseFineProgram (B := B)
        Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
      let Q := P.appendNetwork N dst
        (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
        (fun _ => 0)
      (Q.stateSize + Q.stateSize) + Q.featureSize <= W) :
    exists Nout : FullyConnectedReLUNet d,
      Nout.depth = D /\ Nout.width <= W /\
        Nout.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (active : Fin coarse),
          0 < Rscan ->
          (forall i p, |payload i p| <= Rscan) ->
          (forall q,
            lower active q + Rscan⁻¹ <= x q /\
              x q <= upper active q - Rscan⁻¹) ->
          (forall i, i ≠ active -> exists q,
            x q <= lower i q \/ upper i q <= x q) ->
          forall (digit : Fin T -> TaylorMultiindex r d -> Nat)
            (correction : Fin T -> TaylorMultiindex r d -> Int)
            (center0 : Fin d -> Real)
            (coefficient0 tail0 : TaylorMultiindex r d -> Real)
            (selectedCenter0 : Fin d -> Real)
            (selectedCoefficient0 : TaylorMultiindex r d -> Real),
          (forall k a,
            (digit k a : Int) = correction k a + (shift : Int)) ->
          payload active =
            Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
              (reluApproxSelectedTaylorState selectedCenter0 selectedCoefficient0) ->
          (forall k a,
            truncatedFloorReLUFunction Rfloor B
                (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
              (digit k a : Real)) ->
          Nout.realize x =
            N.realize (reluApproxNormalizedTaylorEvaluationInputValue x
              (reluApproxFineSelectedCenterRecursion (T := T)
                Rselect radius x
                (reluApproxTaylorCenterRecursion step center0)
                selectedCenter0 T)
              (reluApproxFineSelectedCoefficientRecursion (T := T)
                Rselect radius x
                (reluApproxTaylorCenterRecursion step center0)
                (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
                selectedCoefficient0 T)) := by
  classical
  let P := reluApproxCoarseFineProgram (B := B)
    Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
  let Q := P.appendNetwork N dst
    (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
    (fun _ => 0)
  let out : Fin Q.stateSize := Fin.castAdd N.width dst
  obtain ⟨Nout, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_fullyConnectedReLUNet_of_macroProgram_register Q out hdepth hwidth
  refine ⟨Nout, hNdepth, hNwidth, hNparam, ?_⟩
  intro x active hRscan hpayload hactive hinactive digit correction center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hdigit
    hpayloadActive hfloor
  rw [hNrealize x]
  change Q.run x out = _
  dsimp only [Q, out]
  exact reluApproxCoarseFineProgram_appendNormalizedTaylorEvaluator_run
    Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
    N dst x active hRscan hpayload hactive hinactive digit correction center0
    coefficient0 tail0 selectedCenter0 selectedCoefficient0 hdigit
    hpayloadActive hfloor

/-- Safe-cell error form of the compiled normalized coarse/fine evaluator.
The two selector recursions are resolved to the unique active fine cell before
the evaluator estimate is applied. -/
private theorem exists_reluApproxCoarseFineNormalizedEvaluatorNet_error_of_unique
    {coarse T d r B D W : Nat} {eps : Real}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (scale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
    (dst : Fin (ReLUApproxCoarseFineStateSize d r))
    (hdepth :
      let P := reluApproxCoarseFineProgram (B := B)
        Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
      let Q := P.appendNetwork N dst
        (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
        (fun _ => 0)
      2 * Q.stepCount + 1 <= D)
    (hwidth :
      let P := reluApproxCoarseFineProgram (B := B)
        Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
      let Q := P.appendNetwork N dst
        (reluApproxNormalizedTaylorEvaluationReadMatrix d r N.width)
        (fun _ => 0)
      (Q.stateSize + Q.stateSize) + Q.featureSize <= W) :
    exists Nout : FullyConnectedReLUNet d,
      Nout.depth = D /\ Nout.width <= W /\
        Nout.parameterCount <= fullyConnectedReLUParameterCount d D W /\
        forall (x : Fin d -> Real) (activeCoarse : Fin coarse)
          (activeFine : Fin T),
          0 < Rscan -> 0 < Rselect ->
          (forall i p, |payload i p| <= Rscan) ->
          (forall q,
            lower activeCoarse q + Rscan⁻¹ <= x q /\
              x q <= upper activeCoarse q - Rscan⁻¹) ->
          (forall i, i ≠ activeCoarse -> exists q,
            x q <= lower i q \/ upper i q <= x q) ->
          forall (digit : Fin T -> TaylorMultiindex r d -> Nat)
            (correction : Fin T -> TaylorMultiindex r d -> Int)
            (center0 : Fin d -> Real)
            (coefficient0 tail0 : TaylorMultiindex r d -> Real),
          (forall k a,
            (digit k a : Int) = correction k a + (shift : Int)) ->
          payload activeCoarse =
            Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
              (reluApproxSelectedTaylorState (fun _ => 0) (fun _ => 0)) ->
          (forall k a,
            truncatedFloorReLUFunction Rfloor B
                (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
              (digit k a : Real)) ->
          (forall k : Fin T, forall q,
            |reluApproxTaylorCenterRecursion step center0 k.val q| <= Rselect) ->
          (forall k : Fin T, forall a,
            |reluApproxTaylorCoefficientRecursion scale trans correction
                coefficient0 k.val a| <= Rselect) ->
          (forall q,
            reluApproxTaylorCenterRecursion step center0 activeFine.val q - radius +
                  Rselect⁻¹ <= x q /\
              x q <=
                reluApproxTaylorCenterRecursion step center0 activeFine.val q + radius -
                  Rselect⁻¹) ->
          (forall k : Fin T, k ≠ activeFine -> exists q,
            x q <= reluApproxTaylorCenterRecursion step center0 k.val q - radius \/
              reluApproxTaylorCenterRecursion step center0 k.val q + radius <= x q) ->
          (|N.realize (reluApproxNormalizedTaylorEvaluationInputValue x
                (reluApproxTaylorCenterRecursion step center0 activeFine.val)
                (reluApproxTaylorCoefficientRecursion scale trans correction
                  coefficient0 activeFine.val)) -
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                  reluApproxTaylorCoefficientRecursion scale trans correction
                    coefficient0 activeFine.val a)
                (fun a y => Finset.univ.prod fun q : Fin a.1.val =>
                  y (a.2 q) -
                    reluApproxTaylorCenterRecursion step center0 activeFine.val
                      (a.2 q)) x| <= eps) ->
          |Nout.realize x -
              finiteLinearCombination
                (Finset.univ : Finset (TaylorMultiindex r d))
                (fun a => ((Nat.factorial a.1.val : Real)⁻¹) *
                  reluApproxTaylorCoefficientRecursion scale trans correction
                    coefficient0 activeFine.val a)
                (fun a y => Finset.univ.prod fun q : Fin a.1.val =>
                  y (a.2 q) -
                    reluApproxTaylorCenterRecursion step center0 activeFine.val
                      (a.2 q)) x| <= eps := by
  obtain ⟨Nout, hNdepth, hNwidth, hNparam, hNrealize⟩ :=
    exists_reluApproxCoarseFineNormalizedEvaluatorNet_exactDepth
      Rscan Rselect Rfloor radius base lower upper payload step shift scale trans
      N dst hdepth hwidth
  refine ⟨Nout, hNdepth, hNwidth, hNparam, ?_⟩
  intro x activeCoarse activeFine hRscan hRselect hpayload hactiveCoarse
    hinactiveCoarse digit correction center0 coefficient0 tail0 hdigit
    hpayloadActive hfloor hcenterBound hcoefficientBound hactiveFine
    hinactiveFine hEvaluator
  rw [hNrealize x activeCoarse hRscan hpayload hactiveCoarse hinactiveCoarse
    digit correction center0 coefficient0 tail0 (fun _ => 0) (fun _ => 0)
    hdigit hpayloadActive hfloor]
  have hselected := reluApproxFineSelectedRecursions_eq_of_unique
    hRselect x (reluApproxTaylorCenterRecursion step center0)
    (reluApproxTaylorCoefficientRecursion scale trans correction coefficient0)
    activeFine hcenterBound hcoefficientBound hactiveFine hinactiveFine
  rw [hselected.1, hselected.2]
  exact hEvaluator

/-- On unique safe coarse and fine cells, the complete compiled program followed
by the dynamic Taylor evaluator has exactly the evaluator's approximation error
against the selected Taylor polynomial. -/
private theorem reluApproxCoarseScan_then_fineRounds_appendTaylorEvaluator_error_of_unique
    {coarse T d r B : Nat} {eps : Real}
    (Rscan Rselect Rfloor radius base : Real)
    (lower upper : Fin coarse -> Fin d -> Real)
    (payload : Fin coarse -> ReLUApproxFineAccumulator d r -> Real)
    (step : Fin T -> Fin d -> Real) (shift : Nat)
    (coefficientScale : TaylorMultiindex r d -> Real)
    (trans : Fin T -> TaylorMultiindex r d -> TaylorMultiindex r d -> Real)
    (N : FullyConnectedReLUNet
      (Fintype.card (ReLUApproxTaylorEvaluationInput d r)))
    (dst : Fin (ReLUApproxCoarseFineStateSize d r))
    (x : Fin d -> Real) (activeCoarse : Fin coarse) (activeFine : Fin T)
    (hRscan : 0 < Rscan) (hRselect : 0 < Rselect)
    (hpayload : forall i p, |payload i p| <= Rscan)
    (hactiveCoarse : forall q,
      lower activeCoarse q + Rscan⁻¹ <= x q /\
        x q <= upper activeCoarse q - Rscan⁻¹)
    (hinactiveCoarse : forall i, i ≠ activeCoarse -> exists q,
      x q <= lower i q \/ upper i q <= x q)
    (digit : Fin T -> TaylorMultiindex r d -> Nat)
    (correction : Fin T -> TaylorMultiindex r d -> Int)
    (center0 : Fin d -> Real)
    (coefficient0 tail0 : TaylorMultiindex r d -> Real)
    (hdigit : forall k a,
      (digit k a : Int) = correction k a + (shift : Int))
    (hpayload_active : payload activeCoarse =
      Sum.elim (reluApproxTaylorPayloadState center0 coefficient0 tail0)
        (reluApproxSelectedTaylorState (fun _ => 0) (fun _ => 0)))
    (hfloor : forall k a,
      truncatedFloorReLUFunction Rfloor B
          (base * reluApproxTaylorTailRecursion base digit tail0 k.val a) =
        (digit k a : Real))
    (hcenterBound : forall k : Fin T, forall q,
      |reluApproxTaylorCenterRecursion step center0 k.val q| <= Rselect)
    (hcoefficientBound : forall k : Fin T, forall a,
      |reluApproxTaylorCoefficientRecursion coefficientScale trans correction
          coefficient0 k.val a| <= Rselect)
    (hactiveFine : forall q,
      reluApproxTaylorCenterRecursion step center0 activeFine.val q - radius +
            Rselect⁻¹ <= x q /\
        x q <= reluApproxTaylorCenterRecursion step center0 activeFine.val q +
            radius - Rselect⁻¹)
    (hinactiveFine : forall k : Fin T, k ≠ activeFine -> exists q,
      x q <= reluApproxTaylorCenterRecursion step center0 k.val q - radius \/
        reluApproxTaylorCenterRecursion step center0 k.val q + radius <= x q)
    (hEvaluator :
      |N.realize (reluApproxTaylorEvaluationInputValue x
          (reluApproxTaylorCenterRecursion step center0 activeFine.val)
          (reluApproxTaylorCoefficientRecursion coefficientScale trans correction
            coefficient0 activeFine.val)) -
        (Finset.univ.sum fun a : TaylorMultiindex r d =>
          reluApproxTaylorCoefficientRecursion coefficientScale trans correction
              coefficient0 activeFine.val a *
            Finset.univ.prod (fun q : Fin a.1.val =>
              x (a.2 q) -
                reluApproxTaylorCenterRecursion step center0 activeFine.val
                  (a.2 q)))| <= eps) :
    let inputMatrix := reluApproxInputMatrixWithZeroSuffix (w := N.width)
      (reluApproxVectorBoxScanInputMatrix d
        (Fintype.card (ReLUApproxFineAccumulator d r)))
    let inputBias := reluApproxInputBiasWithZeroSuffix (w := N.width)
      (fun _ : Fin (ReLUApproxCoarseFineStateSize d r) => 0)
    let featureMatrix := reluApproxConcatFeatureSchedule
      (reluApproxMacroScheduleWithPersistentSuffixFeatureMatrix (p := N.width)
        (reluApproxCoarseFineFeatureSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rscan Rselect Rfloor radius base))
      (reluApproxPersistentNetworkInstructionFeatureSchedule N
        (reluApproxTaylorEvaluationReadMatrix d r N.width) (fun _ => 0))
    let featureBias := reluApproxConcatFeatureBiasSchedule
      (reluApproxMacroScheduleWithPersistentSuffixFeatureBias (p := N.width)
        (reluApproxCoarseFineFeatureBiasSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rscan Rselect Rfloor radius base lower upper payload))
      (reluApproxPersistentNetworkInstructionFeatureBiasSchedule N
        (reluApproxTaylorEvaluationReadMatrix d r N.width) (fun _ => 0))
    let updateMatrix := reluApproxConcatUpdateSchedule
      (reluApproxMacroScheduleWithPersistentSuffixUpdateMatrix (p := N.width)
        (reluApproxCoarseFineUpdateSchedule
          (coarse := coarse) (T := T) (d := d) (r := r) (B := B)
          Rfloor base trans coefficientScale))
      (reluApproxPersistentNetworkInstructionUpdateSchedule N dst)
    let updateBias := reluApproxConcatUpdateBiasSchedule
      (reluApproxMacroScheduleWithPersistentSuffixUpdateBias (p := N.width)
        (reluApproxCoarseFineUpdateBiasSchedule
          (coarse := coarse) (T := T) (d := d) (r := r)
          step shift coefficientScale))
      (reluApproxPersistentNetworkInstructionUpdateBiasSchedule N dst)
    let outputWeight : Fin (ReLUApproxCoarseFineStateSize d r + N.width) -> Real :=
      fun i => if i = Fin.castAdd N.width dst then 1 else 0
    |(Finset.univ.sum fun i => outputWeight i *
        reluApproxSignedMacroRecursion inputMatrix inputBias featureMatrix
          featureBias updateMatrix updateBias x
          (ReLUApproxCoarseFineStepCount coarse T +
            (((N.depth - 1) + 1) + 1)) i) -
      (Finset.univ.sum fun a : TaylorMultiindex r d =>
        reluApproxTaylorCoefficientRecursion coefficientScale trans correction
            coefficient0 activeFine.val a *
          Finset.univ.prod (fun q : Fin a.1.val =>
            x (a.2 q) -
              reluApproxTaylorCenterRecursion step center0 activeFine.val
                (a.2 q)))| <= eps := by
  classical
  dsimp only
  rw [reluApproxCoarseScan_then_fineRounds_appendTaylorEvaluator_realize
    Rscan Rselect Rfloor radius base lower upper payload step shift
    coefficientScale trans N dst x activeCoarse hRscan hpayload hactiveCoarse
    hinactiveCoarse digit correction center0 coefficient0 tail0 (fun _ => 0)
    (fun _ => 0) hdigit hpayload_active hfloor]
  have hselected := reluApproxFineSelectedRecursions_eq_of_unique
    hRselect x (reluApproxTaylorCenterRecursion step center0)
    (reluApproxTaylorCoefficientRecursion coefficientScale trans correction
      coefficient0) activeFine hcenterBound hcoefficientBound hactiveFine hinactiveFine
  rw [hselected.1, hselected.2]
  exact hEvaluator

/-- Every prescribed-digit Taylor recursion preserves the persistent suffix. -/
private theorem reluApproxParallelFloorDigitRecursionFrom_withPersistentWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    [DecidableEq W] {T : Nat}
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real)
    (digit : Fin T -> A -> Nat) (u : S -> Real) (work : W -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorDigitRecursionFrom
      (fun k => reluApproxAffineMapWithPersistentWork (W := W) (P k))
      (fun k => reluApproxBiasWithPersistentWork (W := W) (bias k))
      (fun k => reluApproxDigitCoeffWithPersistentWork (W := W) (digitCoeff k))
      digit (Sum.elim u work) t =
        Sum.elim
          (reluApproxParallelFloorDigitRecursionFrom
            P bias digitCoeff digit u t)
          work := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      rw [reluApproxParallelFloorDigitRecursionFrom,
        reluApproxParallelFloorDigitRecursionFrom]
      simp only [dif_pos htlt]
      rw [ih (Nat.le_of_succ_le ht)]
      exact reluApproxParallelFloorDigitState_withPersistentWork
        (P ⟨t, htlt⟩) (bias ⟨t, htlt⟩)
        (digitCoeff ⟨t, htlt⟩) (digit ⟨t, htlt⟩)
        (reluApproxParallelFloorDigitRecursionFrom
          P bias digitCoeff digit u t) work

/-- One concrete truncated-floor update preserves every persistent register. -/
private theorem reluApproxParallelFloorState_withPersistentWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    [DecidableEq W]
    (R : Real) (B : Nat) (base : Real) (tail : A -> S)
    (P : S -> S -> Real) (bias : S -> Real)
    (digitCoeff : S -> A -> Real) (u : S -> Real) (work : W -> Real) :
    reluApproxParallelFloorState R B base (fun a => Sum.inl (tail a))
      (reluApproxAffineMapWithPersistentWork (W := W) P)
      (reluApproxBiasWithPersistentWork (W := W) bias)
      (reluApproxDigitCoeffWithPersistentWork (W := W) digitCoeff)
      (Sum.elim u work) =
        Sum.elim
          (reluApproxParallelFloorState R B base tail P bias digitCoeff u)
          work := by
  funext z
  rcases z with i | w
  · simp [reluApproxParallelFloorState,
      reluApproxTypedAffineMap,
      reluApproxAffineMapWithPersistentWork,
      reluApproxBiasWithPersistentWork,
      reluApproxDigitCoeffWithPersistentWork,
      Fintype.sum_sum_type]
  · simp [reluApproxParallelFloorState,
      reluApproxTypedAffineMap,
      reluApproxAffineMapWithPersistentWork,
      reluApproxBiasWithPersistentWork,
      reluApproxDigitCoeffWithPersistentWork,
      Fintype.sum_sum_type]

/-- A concrete parallel floor schedule transports its active prefix and keeps
the selected-register suffix unchanged at every time. -/
private theorem reluApproxParallelFloorMacroRecursionFrom_withPersistentWork
    {S W A : Type*} [Fintype S] [Fintype W] [Fintype A]
    [DecidableEq S] [DecidableEq W] {T : Nat}
    (R : Real) (B : Nat) (base : Real) (tail : Fin T -> A -> S)
    (P : Fin T -> S -> S -> Real) (bias : Fin T -> S -> Real)
    (digitCoeff : Fin T -> S -> A -> Real)
    (u : S -> Real) (work : W -> Real)
    (t : Nat) (ht : t <= T) :
    reluApproxParallelFloorMacroRecursionFrom R B base
      (fun k a => Sum.inl (tail k a))
      (fun k => reluApproxAffineMapWithPersistentWork (W := W) (P k))
      (fun k => reluApproxBiasWithPersistentWork (W := W) (bias k))
      (fun k => reluApproxDigitCoeffWithPersistentWork (W := W) (digitCoeff k))
      (Sum.elim u work) t =
        Sum.elim
          (reluApproxParallelFloorMacroRecursionFrom
            R B base tail P bias digitCoeff u t)
          work := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      have iht := ih (Nat.le_of_succ_le ht)
      change reluApproxTypedMacroRecursionFrom _ _ _ _ _ t =
        Sum.elim (reluApproxTypedMacroRecursionFrom _ _ _ _ _ t)
          work at iht
      simp only [reluApproxParallelFloorMacroRecursionFrom,
        reluApproxTypedMacroRecursionFrom, dif_pos htlt]
      rw [iht]
      rw [reluApproxParallelFloorMacro_exact,
        reluApproxParallelFloorMacro_exact]
      exact reluApproxParallelFloorState_withPersistentWork
        R B base (tail ⟨t, htlt⟩) (P ⟨t, htlt⟩)
        (bias ⟨t, htlt⟩) (digitCoeff ⟨t, htlt⟩)
        (reluApproxParallelFloorMacroRecursionFrom
          R B base tail P bias digitCoeff u t) work

end Statlib.Nonparametric.Approximation.NeuralNetworkAlgebra
