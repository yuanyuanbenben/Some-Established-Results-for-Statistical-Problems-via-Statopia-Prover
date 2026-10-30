import Mathlib
import Statlib.Nonparametric.Vocabulary.FunctionClasses
import Statlib.Nonparametric.Vocabulary.Risk

/-! # Nonparametric/Vocabulary/NeuralNetwork

Vocabulary for fully connected ReLU networks.
-/

open scoped BigOperators

namespace Statlib.Nonparametric.Vocabulary

/-- ReLU activation `x ↦ max x 0`. -/
def relu (x : ℝ) : ℝ :=
  max x 0

/-- Coordinatewise ReLU. -/
def reluVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => relu (x i)

/-- A fully connected affine layer from `ℝ^m` to `ℝ^n`. -/
structure DenseLayer (m n : ℕ) where
  weight : Matrix (Fin n) (Fin m) ℝ
  bias : Fin n → ℝ

namespace DenseLayer

/-- Apply a dense affine layer. -/
noncomputable def apply {m n : ℕ} (L : DenseLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun i => (∑ j : Fin m, L.weight i j * x j) + L.bias i

/-- Apply a dense affine layer followed by coordinatewise ReLU. -/
noncomputable def reluApply {m n : ℕ} (L : DenseLayer m n) (x : Fin m → ℝ) :
    Fin n → ℝ :=
  reluVec (L.apply x)

/-- Number of trainable scalar parameters in a dense affine layer. -/
def parameterCount {m n : ℕ} (_L : DenseLayer m n) : ℕ :=
  (m + 1) * n

end DenseLayer

/-- One-hidden-layer fully connected ReLU network. This is the first concrete
network carrier; deeper networks can be layered on the same `DenseLayer`
vocabulary. -/
structure OneHiddenReLUNet (d width : ℕ) where
  hidden : DenseLayer d width
  outputWeight : Fin width → ℝ
  outputBias : ℝ

namespace OneHiddenReLUNet

/-- Realization of a one-hidden-layer ReLU network. -/
noncomputable def realize {d width : ℕ} (N : OneHiddenReLUNet d width)
    (x : Fin d → ℝ) : ℝ :=
  (∑ j : Fin width, N.outputWeight j * relu (N.hidden.apply x j)) + N.outputBias

/-- Number of trainable scalar parameters in a one-hidden-layer ReLU network. -/
def parameterCount {d width : ℕ} (_N : OneHiddenReLUNet d width) : ℕ :=
  (d + 1) * width + (width + 1)

end OneHiddenReLUNet

/-- Parameter count for a fixed-width fully connected ReLU architecture.

Here `depth` is the number of hidden layers and `width` is the common hidden
width.  The count is: input-to-hidden affine parameters, hidden-to-hidden affine
parameters, and the final affine output layer. -/
def fullyConnectedReLUParameterCount (d depth width : ℕ) : ℕ :=
  (d + 1) * width + (depth - 1) * ((width + 1) * width) + (width + 1)

/-- Uniform-resolution error budget for recursively approximating a centered
coordinate monomial on a coordinatewise box of radius `R`.

The degree-zero and degree-one monomials are represented exactly.  At each
higher degree, the bound records one multiplication approximation at resolution
`n` and the propagated prefix-monomial approximation error. -/
noncomputable def centeredMonomialApproxError (R : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | m + 2 =>
      let B : ℝ := R ^ (m + 1) + centeredMonomialApproxError R n (m + 1) + R + 1
      2 * B ^ 2 / (n : ℝ) ^ 2 + B * centeredMonomialApproxError R n (m + 1)

/-- Uniform-resolution error budget for recursively approximating a centered
coordinate monomial with a fixed-width multiplication gadget.

The degree-zero and degree-one monomials are represented exactly.  In each
higher-degree step, the prefix monomial approximation is multiplied by one more
centered coordinate using a multiplication gadget whose error constant is
`cMulErr`; the width is allowed to depend on the degree but not on the
resolution `n`. -/
noncomputable def centeredMonomialFixedWidthApproxError (cMulErr R : ℝ) (n : ℕ) :
    ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | m + 2 =>
      let B : ℝ :=
        R ^ (m + 1) + centeredMonomialFixedWidthApproxError cMulErr R n (m + 1) +
          R + 1
      cMulErr * B ^ 2 * (n : ℝ).rpow (-2 : ℝ) +
        B * centeredMonomialFixedWidthApproxError cMulErr R n (m + 1)

/-- Width budget for the uniform-resolution recursive centered-monomial network
construction. -/
def centeredMonomialWidthBound (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | m + 2 => centeredMonomialWidthBound n (m + 1) + 2 + 2 * n

/-- Fixed-width budget for a centered coordinate monomial built recursively from
a fixed-width multiplication gadget.  The bound depends on the monomial degree
and the multiplication-gadget width, but not on the approximation resolution. -/
def centeredMonomialFixedWidthBound (Wmul : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | m + 2 => centeredMonomialFixedWidthBound Wmul (m + 1) + 2 + Wmul

/-- Fixed-width budget for a finite centered coordinate-monomial polynomial
assembled from fixed-width monomial approximants.  The bound depends on the
finite index set, degrees, and multiplication-gadget width, but not on the
approximation resolution. -/
def finiteCenteredMonomialPolynomialFixedWidthBound {ι : Type*} (Wmul : ℕ)
    (s : Finset ι) (degree : ι → ℕ) : ℕ :=
  max 1 (s.sum (fun r => centeredMonomialFixedWidthBound Wmul (degree r)))

/-- Uniform-resolution approximation error for a finite centered coordinate-
monomial polynomial assembled from fixed-width monomial approximants. -/
noncomputable def finiteCenteredMonomialPolynomialFixedWidthApproxError {ι : Type*}
    (cMulErr R : ℝ) (n : ℕ) (s : Finset ι) (coeff : ι → ℝ)
    (degree : ι → ℕ) : ℝ :=
  s.sum (fun r => |coeff r| * centeredMonomialFixedWidthApproxError cMulErr R n (degree r))

/-- Depth budget for a finite centered coordinate-monomial polynomial assembled
from per-monomial networks. -/
def finiteCenteredMonomialPolynomialDepthBound {ι : Type*} (s : Finset ι)
    (degree : ι → ℕ) : ℕ :=
  s.sum (fun r => degree r + 1) + 1

/-- Width budget for a finite centered coordinate-monomial polynomial assembled
from uniform-resolution per-monomial networks. -/
def finiteCenteredMonomialPolynomialWidthBound {ι : Type*} (n : ℕ) (s : Finset ι)
    (degree : ι → ℕ) : ℕ :=
  s.sum (fun r => centeredMonomialWidthBound n (degree r))

/-- Scalar-parameter budget induced by the fixed-width fully connected ReLU
architecture used for a finite centered coordinate-monomial polynomial. -/
def finiteCenteredMonomialPolynomialParameterBound {ι : Type*} (d n : ℕ) (s : Finset ι)
    (degree : ι → ℕ) : ℕ :=
  fullyConnectedReLUParameterCount d
    (finiteCenteredMonomialPolynomialDepthBound s degree)
    (finiteCenteredMonomialPolynomialWidthBound n s degree)

/-- Uniform-resolution approximation error for a finite centered coordinate-
monomial polynomial. -/
noncomputable def finiteCenteredMonomialPolynomialApproxError {ι : Type*}
    (R : ℝ) (n : ℕ) (s : Finset ι) (coeff : ι → ℝ) (degree : ι → ℕ) : ℝ :=
  s.sum (fun r => |coeff r| * centeredMonomialApproxError R n (degree r))

/-- A fully connected ReLU network with concrete weights.

The network has `depth` hidden layers of common `width`.  The `input` layer maps
from `ℝ^d` to the first hidden layer; `hidden` contains the `depth - 1`
hidden-to-hidden affine layers; the scalar output layer is affine without a
final ReLU. -/
structure FullyConnectedReLUNet (d : ℕ) where
  depth : ℕ
  width : ℕ
  input : DenseLayer d width
  hidden : Fin (depth - 1) → DenseLayer width width
  outputWeight : Fin width → ℝ
  outputBias : ℝ

namespace FullyConnectedReLUNet

/-- Hidden state after the input layer and the first `t` hidden-to-hidden layers.

For `t ≥ depth - 1`, this stays at the final hidden state.  The intended
architecture has `0 < depth`; the saturated definition keeps the realization
total for all natural-valued metadata. -/
noncomputable def hiddenState {d : ℕ} (N : FullyConnectedReLUNet d)
    (x : Fin d → ℝ) : ℕ → Fin N.width → ℝ
  | 0 => N.input.reluApply x
  | t + 1 =>
      if ht : t < N.depth - 1 then
        (N.hidden ⟨t, ht⟩).reluApply (hiddenState N x t)
      else
        hiddenState N x t

/-- Realization of a fixed-width fully connected ReLU network. -/
noncomputable def realize {d : ℕ} (N : FullyConnectedReLUNet d)
    (x : Fin d → ℝ) : ℝ :=
  (∑ j : Fin N.width, N.outputWeight j * N.hiddenState x (N.depth - 1) j) +
    N.outputBias

/-- Number of trainable scalar parameters in a fully connected ReLU network. -/
def parameterCount {d : ℕ} (N : FullyConnectedReLUNet d) : ℕ :=
  fullyConnectedReLUParameterCount d N.depth N.width

end FullyConnectedReLUNet

namespace OneHiddenReLUNet

/-- Embed a one-hidden-layer ReLU network into the fixed-width fully connected
carrier with one hidden layer. -/
noncomputable def toFullyConnected {d width : ℕ} (N : OneHiddenReLUNet d width) :
    FullyConnectedReLUNet d where
  depth := 1
  width := width
  input := N.hidden
  hidden := fun i => Fin.elim0 i
  outputWeight := N.outputWeight
  outputBias := N.outputBias

end OneHiddenReLUNet

/-- ReLU network class with bounded depth, width, and parameter count. -/
def reluNetworkClass (d depth width parameterCount : ℕ) : FunctionClass (Fin d → ℝ) :=
  {f | ∃ N : FullyConnectedReLUNet d,
    0 < N.depth ∧ N.depth ≤ depth ∧ N.width ≤ width ∧ N.parameterCount ≤ parameterCount ∧
      ∀ x, f x = N.realize x}

/-- ReLU network class with exactly the specified depth and width. -/
def fixedDepthWidthReLUNetClass (d depth width : ℕ) : FunctionClass (Fin d → ℝ) :=
  {f | ∃ N : FullyConnectedReLUNet d,
    0 < N.depth ∧ N.depth = depth ∧ N.width = width ∧ ∀ x, f x = N.realize x}

/-- ReLU network class controlled only by the true scalar-parameter count. -/
def reluNetworkClassOfParameterCount (d parameterCount : ℕ) :
    FunctionClass (Fin d → ℝ) :=
  {f | ∃ N : FullyConnectedReLUNet d,
    0 < N.depth ∧ N.parameterCount ≤ parameterCount ∧ ∀ x, f x = N.realize x}

/-- ReLU ramp approximation to the unit step at threshold `t`.

For positive `R`, this is `0` to the left of `t`, rises linearly on
`[t, t + R^{-1}]`, and is `1` to the right of `t + R^{-1}`. -/
noncomputable def reluStepFunctionApprox (R t z : ℝ) : ℝ :=
  R * relu (z - t) - R * relu (z - t - R⁻¹)

/-- Truncated finite ReLU sum representing the floor map away from integer
breakpoints.  The sum has one ramp at each integer threshold `1, ..., B`. -/
noncomputable def truncatedFloorReLUFunction (R : ℝ) (B : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 B, reluStepFunctionApprox R (j : ℝ) z

/-- A scalar point is separated from the integer breakpoints `1, ..., B` by at
least `R^{-1}`. -/
def awayFromFiniteIntegerGrid (R : ℝ) (B : ℕ) (z : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 B, R⁻¹ ≤ |z - (j : ℝ)|

/-- ReLU ramp that equals one on an axis-aligned box and vanishes once a point
is outside the box by margin `R^{-1}` in at least one coordinate. -/
noncomputable def axisAlignedBoxIndicatorRamp {d : ℕ} (R : ℝ)
    (lower upper : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  relu (1 - R *
    ∑ q : Fin d, (relu (lower q - x q) + relu (x q - upper q)))

/-- Secant interpolation of the square map on an interval `[a, b]`. -/
noncomputable def squareSecantInterpolant (a b x : ℝ) : ℝ :=
  (a + b) * x - a * b

/-- Secant interpolation of the square map on the `k`-th interval of the
uniform grid with mesh `1 / n`. -/
noncomputable def squareCellInterpolant (n k : ℕ) (x : ℝ) : ℝ :=
  squareSecantInterpolant ((k : ℝ) / (n : ℝ)) (((k + 1 : ℕ) : ℝ) / (n : ℝ)) x

/-- The standard one-dimensional ReLU hinge interpolant for the square map on
`[0, 1]`, using knots `0, 1/n, ..., (n-1)/n`. -/
noncomputable def squareReLUHingeInterpolant (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (n : ℝ)) * relu x +
    ∑ i ∈ Finset.range (n - 1),
      (2 / (n : ℝ)) * relu (x - ((i + 1 : ℕ) : ℝ) / (n : ℝ))

/-- A one-hidden-layer ReLU network realizing the square hinge interpolant on
the unit interval. -/
noncomputable def unitIntervalSquareReLUHingeNet (n : ℕ) : OneHiddenReLUNet 1 n where
  hidden :=
    { weight := fun _ _ => 1
      bias := fun j => -((j : ℕ) : ℝ) / (n : ℝ) }
  outputWeight := fun j => if (j : ℕ) = 0 then (1 / (n : ℝ)) else (2 / (n : ℝ))
  outputBias := 0

/-- Scaled square hinge interpolant on an interval `[a, b]`, using the affine
coordinate `t = (x - a) / (b - a)`. -/
noncomputable def intervalSquareReLUHingeInterpolant (n : ℕ) (a b x : ℝ) : ℝ :=
  a ^ 2 + 2 * a * (b - a) * relu ((x - a) / (b - a)) +
    (b - a) ^ 2 * squareReLUHingeInterpolant n ((x - a) / (b - a))

/-- A one-hidden-layer ReLU network realizing the scaled square hinge
interpolant on an interval `[a, b]`. -/
noncomputable def intervalSquareReLUHingeNet (n : ℕ) (a b : ℝ) :
    OneHiddenReLUNet 1 n where
  hidden :=
    { weight := fun _ _ => 1 / (b - a)
      bias := fun j => -a / (b - a) - ((j : ℕ) : ℝ) / (n : ℝ) }
  outputWeight := fun j =>
    if (j : ℕ) = 0 then
      2 * a * (b - a) + (b - a) ^ 2 * (1 / (n : ℝ))
    else
      (b - a) ^ 2 * (2 / (n : ℝ))
  outputBias := a ^ 2

/-- Multiplication approximation obtained from a square approximation by
polarization. -/
noncomputable def squarePolarizationMulApprox (S : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (S (x + y) - S (x - y)) / 4

/-- One-hidden-layer ReLU network obtained by applying the interval square
hinge net to `x₀ + x₁` and `x₀ - x₁`, then taking the polarization
difference.  The square nets use the interval `[-2R, 2R]`. -/
noncomputable def mulPolarizationReLUHingeNet (n : ℕ) (R : ℝ) :
    OneHiddenReLUNet 2 (n + n) where
  hidden :=
    { weight :=
        Fin.addCases
          (fun j _ =>
            (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).hidden.weight j 0)
          (fun j i =>
            if (i : ℕ) = 0 then
              (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).hidden.weight j 0
            else
              - (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).hidden.weight j 0)
      bias :=
        Fin.addCases
          (fun j => (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).hidden.bias j)
          (fun j => (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).hidden.bias j) }
  outputWeight :=
    Fin.addCases
      (fun j => (1 / 4 : ℝ) *
        (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).outputWeight j)
      (fun j => - (1 / 4 : ℝ) *
        (intervalSquareReLUHingeNet n (-(2 * R)) (2 * R)).outputWeight j)
  outputBias := 0

/-- The one-dimensional tent/hat profile on one selected coordinate, written as
a ReLU expression.  The parameter `scale` is typically the reciprocal of a
cell half-width. -/
noncomputable def coordinateTentReLUFunction {d : ℕ} (coord : Fin d)
    (center scale : ℝ) (x : Fin d → ℝ) : ℝ :=
  relu (1 - scale * (relu (x coord - center) + relu (center - x coord)))

/-- A depth-two fully connected ReLU network realizing
`coordinateTentReLUFunction`.  The first hidden layer stores the two one-sided
hinges and the second hidden layer forms the tent. -/
noncomputable def coordinateTentReLUNet {d : ℕ} (coord : Fin d)
    (center scale : ℝ) : FullyConnectedReLUNet d where
  depth := 2
  width := 2
  input :=
    { weight := fun j q =>
        if (j : ℕ) = 0 then
          if q = coord then 1 else 0
        else if (j : ℕ) = 1 then
          if q = coord then -1 else 0
        else
          0
      bias := fun j =>
        if (j : ℕ) = 0 then -center
        else if (j : ℕ) = 1 then center
        else 0 }
  hidden := fun _ =>
    { weight := fun j k =>
        if (j : ℕ) = 0 then
          if (k : ℕ) = 0 then -scale
          else if (k : ℕ) = 1 then -scale
          else 0
        else
          0
      bias := fun j => if (j : ℕ) = 0 then 1 else 0 }
  outputWeight := fun j => if (j : ℕ) = 0 then 1 else 0
  outputBias := 0

/-- True scalar-parameter budget for the coordinate tent network. -/
def coordinateTentReLUParameterBound (d : ℕ) : ℕ :=
  fullyConnectedReLUParameterCount d 2 2

/-- Tensor-product tent weight for an axis-aligned box/partition cell. -/
noncomputable def axisAlignedBoxTentWeight {d : ℕ}
    (center scale : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ q : Fin d, coordinateTentReLUFunction q (center q) (scale q) x

/-- A Taylor multiindex represented by its degree and ordered coordinate directions. -/
abbrev TaylorMultiindex (r d : ℕ) :=
  (k : Fin (r + 1)) × (Fin k.val → Fin d)

/-- A boundary-inclusive two-scale grid with a partition of unity and a
serpentine traversal of the fine cells inside every coarse block. -/
abbrev IsTwoScaleSerpentineLayout
    (d M : ℕ)
    (center scale : Fin (M ^ d) → Fin (M ^ d) → Fin d → ℝ) : Prop :=
  (∀ b t q, scale b t q = ((M ^ 2 - 1 : ℕ) : ℝ)) ∧
  (∀ b t q, center b t q ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ x : Fin d → ℝ, x ∈ unitCubeSet d →
    (∑ b : Fin (M ^ d), ∑ t : Fin (M ^ d),
      axisAlignedBoxTentWeight (center b t) (scale b t) x) = 1) ∧
  (∀ b t (x : Fin d → ℝ), x ∈ unitCubeSet d →
    (∀ q,
      scale b t q *
        (relu (x q - center b t q) + relu (center b t q - x q)) < 1) →
      ∀ q, |x q - center b t q| ≤ ((M ^ 2 - 1 : ℕ) : ℝ)⁻¹) ∧
  (∀ b : Fin (M ^ d), ∀ k : ℕ, ∀ hk : k + 1 < M ^ d,
    ∃ q : Fin d,
      (center b ⟨k + 1, hk⟩ q =
          center b ⟨k, Nat.lt_of_succ_lt hk⟩ q + ((M ^ 2 - 1 : ℕ) : ℝ)⁻¹ ∨
        center b ⟨k + 1, hk⟩ q =
          center b ⟨k, Nat.lt_of_succ_lt hk⟩ q - ((M ^ 2 - 1 : ℕ) : ℝ)⁻¹) ∧
      ∀ u : Fin d, u != q →
        center b ⟨k + 1, hk⟩ u = center b ⟨k, Nat.lt_of_succ_lt hk⟩ u)

/-- A signed Hamilton order on the `d`-dimensional grid with side length `M`. -/
abbrev IsSerpentineGridOrder
    (d M : ℕ) (order : Fin (M ^ d) ≃ (Fin d → Fin M)) : Prop :=
  (∀ hM : 0 < M, order ⟨0, pow_pos hM d⟩ = (fun _ => ⟨0, hM⟩)) ∧
  (∀ (k : ℕ) (hk : k + 1 < M ^ d),
    ∃ q : Fin d,
      Int.natAbs
          (((order ⟨k + 1, hk⟩ q).val : Int) -
            ((order ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ q).val : Int)) = 1 ∧
      ∀ u : Fin d, u != q →
        order ⟨k + 1, hk⟩ u =
          order ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩ u)

/-- The canonical coarse/fine factorization of a two-scale serpentine grid. -/
abbrev IsCanonicalTwoScaleLayout
    (d M : ℕ)
    (coarseOrder fineOrder : Fin (M ^ d) ≃ (Fin d → Fin M))
    (center scale : Fin (M ^ d) → Fin (M ^ d) → Fin d → ℝ) : Prop :=
  IsSerpentineGridOrder d M coarseOrder ∧
  IsSerpentineGridOrder d M fineOrder ∧
  (∀ b t q,
    center b t q =
      (((coarseOrder b q).val * M + (fineOrder t q).val : ℕ) : ℝ) /
        ((M ^ 2 - 1 : ℕ) : ℝ)) ∧
  IsTwoScaleSerpentineLayout d M center scale

/-- Finite linear combination of real-valued approximation atoms. -/
noncomputable def finiteLinearCombination {ι X : Type*} (s : Finset ι) (coeff : ι → ℝ)
    (term : ι → X → ℝ) : X → ℝ :=
  fun x => ∑ i ∈ s, coeff i * term i x

/-- Empirical square-loss objective for a one-hidden-layer ReLU network. -/
noncomputable def oneHiddenReLUEmpiricalRisk {d width n : ℕ}
    (N : OneHiddenReLUNet d width) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ) : ℝ :=
  empiricalRisk n X Y squaredLoss N.realize

end Statlib.Nonparametric.Vocabulary
