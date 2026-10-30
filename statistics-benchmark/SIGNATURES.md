# Statistics signatures

Extracted from the original input skeletons, including the complete theorem type. Namespaces, definitions and instances are in the linked input. Static text preservation does not establish mathematical equivalence to the natural-language question.

## clipping_dominates_squared_loss

[Full input](clipping_dominates_squared_loss/input.lean)

```lean
theorem clipping_dominates_squared_loss
    {Ω : Type*}
    [MeasurableSpace Ω]
    (a b : ℝ)
    (hab : a ≤ b)
    (P : ℝ → Measure Ω)
    (hP : ∀ θ ∈ Set.Icc a b, IsProbabilityMeasure (P θ))
    (δ : Ω → ℝ)
    (hδmeas : Measurable δ)
    (hδ2 : ∀ θ ∈ Set.Icc a b, Integrable (fun ω ↦ (δ ω) ^ 2) (P θ)) :
    let δclip : Ω → ℝ := fun ω ↦ max a (min (δ ω) b)
    ∀ θ ∈ Set.Icc a b, ∀ ω,
      (δclip ω - θ) ^ 2 ≤ (δ ω - θ) ^ 2
```

## least_squares_residual_sum

[Full input](least_squares_residual_sum/input.lean)

```lean
theorem least_squares_residual_sum
    (n : ℕ) (hn : n ≥ 1) (x y : Fin n → ℝ)
    (Q : ℝ → ℝ → ℝ)
    (hQ : ∀ a b : ℝ, Q a b = ∑ i : Fin n, (y i - a - b * x i) ^ 2)
    (ahat bhat : ℝ)
    (hmin : ∀ a b : ℝ, Q ahat bhat ≤ Q a b)
    (e : Fin n → ℝ)
    (he : ∀ i, e i = y i - ahat - bhat * x i) :
    (∑ i : Fin n, e i) = 0
```

## average_jackknife_pseudo_value_sample_variance

[Full input](average_jackknife_pseudo_value_sample_variance/input.lean)

```lean
theorem average_jackknife_pseudo_value_sample_variance
    (n : ℕ) (hn : 2 ≤ n)
    (x : Fin n → ℝ) :
    let mean : ℝ := (n : ℝ)⁻¹ * ∑ j, x j
    let V : ℝ := (n : ℝ)⁻¹ * ∑ j, (x j - mean) ^ 2
    let meanMinus : Fin n → ℝ := fun i ↦
      (((n - 1 : ℕ) : ℝ))⁻¹ * ∑ j ∈ Finset.univ.erase i, x j
    let VMinus : Fin n → ℝ := fun i ↦
      (((n - 1 : ℕ) : ℝ))⁻¹ *
        ∑ j ∈ Finset.univ.erase i, (x j - meanMinus i) ^ 2
    let pseudo : Fin n → ℝ := fun i ↦
      (n : ℝ) * V - ((n - 1 : ℕ) : ℝ) * VMinus i
    (n : ℝ)⁻¹ * ∑ i, pseudo i =
      (((n - 1 : ℕ) : ℝ))⁻¹ * ∑ i, (x i - mean) ^ 2
```

## bounded_random_sum_mean

[Full input](bounded_random_sum_mean/input.lean)

```lean
theorem bounded_random_sum_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 1 ≤ m)
    (N : Ω → ℕ) (hN_meas : Measurable N)
    (hN_bound : ∀ ω, N ω ≤ m)
    (X : Fin m → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : ∀ i, Integrable (X i) P)
    (μ : ℝ) (hX_mean : ∀ i, ∫ ω, X i ω ∂P = μ)
    (h_indep : IndepFun N (fun ω i ↦ X i ω) P) :
    let S : Ω → ℝ := fun ω ↦
      ∑ i : Fin m, if i.1 + 1 ≤ N ω then X i ω else 0
    let NReal : Ω → ℝ := fun ω ↦ N ω
    ∫ ω, S ω ∂P = μ * ∫ ω, NReal ω ∂P
```

## complete_case_mean_conditionally_unbiased_under_mcar

[Full input](complete_case_mean_conditionally_unbiased_under_mcar/input.lean)

```lean
theorem complete_case_mean_conditionally_unbiased_under_mcar
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ)
    (hn : 1 ≤ n)
    (μ : ℝ)
    (Y : Fin n → Ω → ℝ)
    (R : Fin n → Ω → Bool)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYint : ∀ i, Integrable (Y i) P)
    (hYmean : ∀ i, ∫ ω, Y i ω ∂P = μ)
    (hRmeas : ∀ i, Measurable (R i))
    (hIndep :
      IndepFun (fun ω i ↦ R i ω) (fun ω i ↦ Y i ω) P) :
    let K : Ω → ℕ := fun ω ↦ ∑ i, if R i ω then 1 else 0
    let μhat : Ω → ℝ := fun ω ↦
      if 0 < K ω then
        (∑ i, if R i ω then Y i ω else 0) / (K ω : ℝ)
      else 0
    0 < P {ω | 0 < K ω} →
      (∫ ω, if 0 < K ω then μhat ω else 0 ∂P) /
          (P {ω | 0 < K ω}).toReal = μ
```

## extrinsic_sample_mean_on_unit_sphere

[Full input](extrinsic_sample_mean_on_unit_sphere/input.lean)

```lean
theorem extrinsic_sample_mean_on_unit_sphere
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1) :
    let xBar : Fin d → ℝ := (n : ℝ)⁻¹ • ∑ i, x i
    xBar ≠ 0 →
      let objective : (Fin d → ℝ) → ℝ := fun p ↦
        (n : ℝ)⁻¹ *
          ∑ i, dotProduct (x i - p) (x i - p)
      {p : Fin d → ℝ |
        dotProduct p p = 1 ∧
          ∀ q, dotProduct q q = 1 → objective p ≤ objective q} =
        {((Real.sqrt (dotProduct xBar xBar))⁻¹ : ℝ) • xBar}
```

## finite_front_door_adjustment

[Full input](finite_front_door_adjustment/input.lean)

```lean
theorem finite_front_door_adjustment
    (U X Z Y : Type*)
    [Fintype U] [Nonempty U]
    [Fintype X] [Nonempty X]
    [Fintype Z] [Nonempty Z]
    [Fintype Y] [Nonempty Y]
    (pU : U → ℝ)
    (pXgivenU : X → U → ℝ)
    (pZgivenX : Z → X → ℝ)
    (pYgivenZU : Y → Z → U → ℝ)
    (hpUpos : ∀ u, 0 < pU u)
    (hpXUpos : ∀ x u, 0 < pXgivenU x u)
    (hpZXpos : ∀ z x, 0 < pZgivenX z x)
    (hpYZUpos : ∀ y z u, 0 < pYgivenZU y z u)
    (hpUsum : ∑ u, pU u = 1)
    (hpXUsum : ∀ u, ∑ x, pXgivenU x u = 1)
    (hpZXsum : ∀ x, ∑ z, pZgivenX z x = 1)
    (hpYZUsum : ∀ z u, ∑ y, pYgivenZU y z u = 1) :
    let pX : X → ℝ := fun x ↦ ∑ u, pU u * pXgivenU x u
    let pYgivenXZ : Y → X → Z → ℝ := fun y x z ↦
      (∑ u, pU u * pXgivenU x u * pYgivenZU y z u) / pX x
    let pDo : X → Y → ℝ := fun x y ↦
      ∑ z, ∑ u, pU u * pZgivenX z x * pYgivenZU y z u
    ∀ x y,
      pDo x y =
        ∑ z, pZgivenX z x * ∑ x', pYgivenXZ y x' z * pX x'
```

## finite_weighted_bayes_rule

[Full input](finite_weighted_bayes_rule/input.lean)

```lean
theorem finite_weighted_bayes_rule
    (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (π : Fin m → ℝ)
    (hπ_mem : ∀ j, π j ∈ Icc 0 1)
    (hπ_sum : ∑ j, π j = 1)
    (p : Fin m → Fin N → ℝ)
    (hp_mem : ∀ j x, p j x ∈ Icc 0 1)
    (hp_sum : ∀ j, ∑ x, p j x = 1)
    (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j)
    (g : Fin m → ℝ) :
    let D : Fin N → ℝ := fun x ↦ ∑ j, π j * p j x * w j
    (∀ x, 0 < D x) →
    let δstar : Fin N → ℝ := fun x ↦
      (∑ j, π j * p j x * w j * g j) / D x
    let risk : (Fin N → ℝ) → ℝ := fun δ ↦
      ∑ j, π j * ∑ x, p j x * w j * (g j - δ x) ^ 2
    ∀ δ : Fin N → ℝ, risk δstar ≤ risk δ
```

## fisher_linear_discriminant_optimality

[Full input](fisher_linear_discriminant_optimality/input.lean)

```lean
theorem fisher_linear_discriminant_optimality
    (d : ℕ) (hd : 1 ≤ d)
    (mu₀ mu₁ : Fin d → ℝ) (hmu : mu₀ ≠ mu₁)
    (W : Matrix (Fin d) (Fin d) ℝ)
    (hWsymm : W.IsSymm) (hWpos : W.PosDef) :
    ∀ a : Fin d → ℝ, a ≠ 0 →
      (dotProduct a (mu₁ - mu₀)) ^ 2 /
          dotProduct a (W *ᵥ a) ≤
        dotProduct (mu₁ - mu₀) (W⁻¹ *ᵥ (mu₁ - mu₀))
```

## gumbel_approximation_to_exponential_maximum

[Full input](gumbel_approximation_to_exponential_maximum/input.lean)

```lean
theorem gumbel_approximation_to_exponential_maximum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i, IdentDistrib (X i) id P (expMeasure 1)) :
    let i₀ : Fin n := ⟨0, hn⟩
    let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨i₀, Finset.mem_univ i₀⟩
    let M : Ω → ℝ :=
      fun ω ↦ Finset.univ.sup' hne (fun i ↦ X i ω)
    sSup
        (Set.range fun x : ℝ ↦
          |ENNReal.toReal (P {ω | M ω - Real.log (n : ℝ) ≤ x}) -
            Real.exp (-Real.exp (-x))|)
      ≤ 1 / (n : ℝ)
```

## inverse_probability_weighting_identity

[Full input](inverse_probability_weighting_identity/input.lean)

```lean
theorem inverse_probability_weighting_identity
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (hTmeas : Measurable T)
    (hZmeas : Measurable Z)
    (a : Bool)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hepos :
      ∀ z, 0 <
        (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) :
    let e : 𝒵 → ℝ := fun z ↦
      (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    ∀ h : 𝒵 → ℝ,
      ∫ ω, (if T ω = a then (1 : ℝ) else 0) * h (Z ω) / e (Z ω) ∂P =
        ∫ ω, h (Z ω) ∂P
```

## isotonic_cumulative_residual_certificate

[Full input](isotonic_cumulative_residual_certificate/input.lean)

```lean
theorem isotonic_cumulative_residual_certificate
    (n : ℕ) (hn : 1 ≤ n)
    (y thetaHat : Fin n → ℝ) :
    let R : ℕ → ℝ := fun k ↦
      ∑ j : Fin n, if j.1 < k then y j - thetaHat j else 0
    (∀ i : ℕ, (hi : i + 1 < n) →
      thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
        thetaHat ⟨i + 1, hi⟩) →
    (∀ i : ℕ, (hi : i + 1 < n) → 0 ≤ R (i + 1)) →
    R n = 0 →
    (∀ i : ℕ, (hi : i + 1 < n) →
      R (i + 1) *
        (thetaHat ⟨i + 1, hi⟩ -
          thetaHat ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩) = 0) →
    ∀ theta : Fin n → ℝ,
      (∀ i : ℕ, (hi : i + 1 < n) →
        theta ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ ≤
          theta ⟨i + 1, hi⟩) →
      ∑ i, (y i - theta i) ^ 2 ≥
        ∑ i, (y i - thetaHat i) ^ 2 +
          ∑ i, (theta i - thetaHat i) ^ 2
```

## kernel_density_normalization

[Full input](kernel_density_normalization/input.lean)

```lean
theorem kernel_density_normalization
    (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → ℝ)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (h : ℝ) (hh : 0 < h) :
    let estimate : ℝ → ℝ := fun z ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((x i - z) / h)
    ∫ z, estimate z = 1
```

## least_squares_pythagorean_identity

[Full input](least_squares_pythagorean_identity/input.lean)

```lean
theorem least_squares_pythagorean_identity
    (n p : ℕ) (hnp : p ≤ n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (hX : Function.Injective X.mulVec) :
    let betaHat := (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y)
    ∀ beta : Fin p → ℝ,
      dotProduct (y - X *ᵥ beta) (y - X *ᵥ beta) =
        dotProduct (y - X *ᵥ betaHat) (y - X *ᵥ betaHat) +
          dotProduct (X *ᵥ (beta - betaHat)) (X *ᵥ (beta - betaHat))
```

## ma1_autocovariance

[Full input](ma1_autocovariance/input.lean)

```lean
theorem ma1_autocovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (theta sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (eps : ℤ → Ω → ℝ)
    (heps_meas : ∀ t, Measurable (eps t))
    (heps_memLp : ∀ t, MemLp (eps t) 2 P)
    (heps_mean : ∀ t, (∫ ω, eps t ω ∂P) = 0)
    (heps_var : ∀ t, ProbabilityTheory.variance (eps t) P = sigma2)
    (heps_cov_zero : ∀ s t, s ≠ t →
      ProbabilityTheory.covariance (eps s) (eps t) P = 0) :
    let X : ℤ → Ω → ℝ :=
      fun t ω => eps t ω + theta * eps (t - 1) ω
    (∀ h : ℕ, ∀ t1 t2 : ℤ,
      ProbabilityTheory.covariance (X t1) (X (t1 + (h : ℤ))) P =
        ProbabilityTheory.covariance (X t2) (X (t2 + (h : ℤ))) P) ∧
    (∀ t : ℤ, ProbabilityTheory.covariance (X t) (X (t + (0 : ℤ))) P =
      (1 + theta ^ 2) * sigma2) ∧
    (∀ t : ℤ, ProbabilityTheory.covariance (X t) (X (t + (1 : ℤ))) P =
      theta * sigma2) ∧
    (∀ h : ℕ, 2 ≤ h → ∀ t : ℤ,
      ProbabilityTheory.covariance (X t) (X (t + (h : ℤ))) P = 0)
```

## mse_decomposition_linear_combination

[Full input](mse_decomposition_linear_combination/input.lean)

```lean
theorem mse_decomposition_linear_combination
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T₁ T₂ : Ω → ℝ)
    (theta v₁ v₂ w : ℝ)
    (hT₁_meas : Measurable T₁)
    (hT₂_meas : Measurable T₂)
    (hT_indep : IndepFun T₁ T₂ P)
    (hT₁_second : MemLp T₁ 2 P)
    (hT₂_second : MemLp T₂ 2 P)
    (hT₁_mean : ∫ ω, T₁ ω ∂P = theta)
    (hT₂_mean : ∫ ω, T₂ ω ∂P = theta)
    (hT₁_var : variance T₁ P = v₁)
    (hT₂_var : variance T₂ P = v₂)
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    (∫ ω, (w * T₁ ω + (1 - w) * T₂ ω - theta) ^ 2 ∂P)
      =
      v₁ * v₂ / (v₁ + v₂) +
        (v₁ + v₂) * (w - v₂ / (v₁ + v₂)) ^ 2
```

## no_logistic_mle_under_complete_separation

[Full input](no_logistic_mle_under_complete_separation/input.lean)

```lean
theorem no_logistic_mle_under_complete_separation
    (n p : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p)
    (x : Fin n → Fin p → ℝ)
    (y : Fin n → Bool)
    (v : Fin p → ℝ)
    (hsep : ∀ i,
      ((2 : ℝ) * (if y i then 1 else 0 : ℝ) - 1) *
        dotProduct (x i) v > 0) :
    let ell : (Fin p → ℝ) → ℝ := fun beta ↦
      ∑ i, ((if y i then 1 else 0 : ℝ) * dotProduct (x i) beta -
        Real.log (1 + Real.exp (dotProduct (x i) beta)))
    ¬ ∃ betaHat : Fin p → ℝ, ∀ beta : Fin p → ℝ,
      ell betaHat ≥ ell beta
```

## observed_failure_mass_under_independent_right_censoring

[Full input](observed_failure_mass_under_independent_right_censoring/input.lean)

```lean
theorem observed_failure_mass_under_independent_right_censoring
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 1 ≤ m)
    (T C : Ω → ℕ)
    (hTmeas : Measurable T)
    (hCmeas : Measurable C)
    (hT : ∀ ω, 1 ≤ T ω ∧ T ω ≤ m)
    (hC : ∀ ω, 1 ≤ C ω ∧ C ω ≤ m)
    (hindep : IndepFun T C P) :
    ∀ u : ℕ, 1 ≤ u → u ≤ m →
      P {ω | min (T ω) (C ω) = u ∧ T ω ≤ C ω} =
        P {ω | T ω = u} * P {ω | u ≤ C ω}
```

## permutation_p_value_validity

[Full input](permutation_p_value_validity/input.lean)

```lean
theorem permutation_p_value_validity
    (N : ℕ) (hN : 1 ≤ N) (T : Fin N → ℝ) :
    let tailCount : Fin N → ℕ :=
      fun i => (Finset.univ.filter (fun j : Fin N => T i ≤ T j)).card
    let pValue : Fin N → ℝ := fun i => (tailCount i : ℝ) / (N : ℝ)
    (∀ k : ℕ, k ≤ N →
      (Finset.univ.filter (fun i : Fin N => tailCount i ≤ k)).card ≤ k) ∧
    (∀ k : ℕ, k ≤ N →
      (1 / (N : ℝ)) *
        ((Finset.univ.filter
          (fun i : Fin N => pValue i ≤ (k : ℝ) / (N : ℝ))).card : ℝ) ≤
        (k : ℝ) / (N : ℝ))
```

## poisson_binomial_probability_generating_function

[Full input](poisson_binomial_probability_generating_function/input.lean)

```lean
theorem poisson_binomial_probability_generating_function
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (n : ℕ)
    (hn : 1 ≤ n)
    (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1)
    (X : Fin n → Ω → Bool)
    (hXmeas : ∀ i, Measurable (X i))
    (hXone : ∀ i, P {ω | X i ω = true} = ENNReal.ofReal (p i))
    (hXzero : ∀ i, P {ω | X i ω = false} = ENNReal.ofReal (1 - p i))
    (hXindep : iIndepFun X P) :
    ∀ z : ℝ,
      ∫ ω, z ^ (∑ i, if X i ω then 1 else 0) ∂P =
        ∏ i, ((1 - p i) + p i * z)
```

## sample_maximum_sufficient

[Full input](sample_maximum_sufficient/input.lean)

```lean
theorem sample_maximum_sufficient
    (n : ℕ)
    (hn : 1 ≤ n) :
    let Θ := Set.Ioi (0 : ℝ)
    let ν : Measure (Fin n → ℝ) :=
      Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))
    let f : Θ → (Fin n → ℝ) → ℝ≥0∞ := fun θ x ↦
      ∏ i, if x i ∈ Set.Ioo (0 : ℝ) θ.1 then
        (ENNReal.ofReal θ.1)⁻¹
      else 0
    let P : Θ → Measure (Fin n → ℝ) := fun θ ↦
      ν.withDensity (f θ)
    let M : (Fin n → ℝ) → ℝ := fun x ↦
      sSup (Set.range x)
    let h : (Fin n → ℝ) → ℝ≥0∞ := fun x ↦
      if ∀ i, 0 < x i then 1 else 0
    let g : Θ → ℝ → ℝ≥0∞ := fun θ m ↦
      if m < θ.1 then ((ENNReal.ofReal θ.1)⁻¹) ^ n else 0
    Measurable M ∧
      (∀ θ, Measurable (f θ) ∧ IsProbabilityMeasure (P θ)) ∧
      ∀ θ x, f θ x = h x * g θ (M x)
```

## unbiased_estimation_of_squared_mean

[Full input](unbiased_estimation_of_squared_mean/input.lean)

```lean
theorem unbiased_estimation_of_squared_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (X : Fin n → Ω → ℝ)
    (mean : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i j, IdentDistrib (X i) (X j) P P)
    (hX_second : ∀ i, MemLp (X i) 2 P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = mean) :
    let U : Ω → ℝ :=
      fun ω ↦
        (((n : ℝ) * ((n - 1 : ℕ) : ℝ))⁻¹) *
          ∑ i : Fin n,
            ∑ j ∈ (Finset.univ.filter fun j : Fin n ↦ j ≠ i),
              X i ω * X j ω
    ∫ ω, U ω ∂P = mean ^ 2
```

## arma11_mean_recursion

[Full input](arma11_mean_recursion/input.lean)

```lean
theorem arma11_mean_recursion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c phi theta m0 : ℝ)
    (eps X : ℕ → Ω → ℝ)
    (heps_meas : ∀ t, Measurable (eps t))
    (heps_integrable : ∀ t, Integrable (eps t) P)
    (hX_meas : ∀ t, Measurable (X t))
    (hX_integrable : ∀ t, Integrable (X t) P)
    (heps_mean_zero : ∀ t, (∫ ω, eps t ω ∂P) = 0)
    (hX0_mean : (∫ ω, X 0 ω ∂P) = m0)
    (hX_rec : ∀ t ω,
      X (t + 1) ω = c + phi * X t ω + eps (t + 1) ω + theta * eps t ω) :
    ∀ t : ℕ,
      (∫ ω, X t ω ∂P) =
        phi ^ t * m0 + c * (Finset.range t).sum (fun j => phi ^ j)
```

## bernoulli_sum_sufficient

[Full input](bernoulli_sum_sufficient/input.lean)

```lean
theorem bernoulli_sum_sufficient
    (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let Ω : Type := Fin n → Bool
    let count : Ω → ℕ :=
      fun z => ∑ i : Fin n, if z i then (1 : ℕ) else 0
    let prob : ℝ → Ω → ℝ :=
      fun q z => q ^ count z * (1 - q) ^ (n - count z)
    let condProb : ℝ → ℕ → Ω → ℝ :=
      fun q k z =>
        if count z = k then
          prob q z / (∑ y : Ω, if count y = k then prob q y else 0)
        else 0
    (∀ k : ℕ, k ≤ n → ∀ x : Ω, count x = k →
      condProb p k x = 1 / (Nat.choose n k : ℝ)) ∧
    (∀ k : ℕ, k ≤ n →
      ∀ p1 : ℝ, 0 < p1 → p1 < 1 →
      ∀ p2 : ℝ, 0 < p2 → p2 < 1 →
        condProb p1 k = condProb p2 k)
```

## binary_mean_nonidentification

[Full input](binary_mean_nonidentification/input.lean)

```lean
theorem binary_mean_nonidentification
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 < c)
    (hsum : a + b + c = 1)
    (P : ℝ → Measure (Bool × Bool))
    (hPprob : ∀ q ∈ Set.Icc (0 : ℝ) 1, IsProbabilityMeasure (P q))
    (hP11 : ∀ q ∈ Set.Icc (0 : ℝ) 1, P q {(true, true)} = ENNReal.ofReal a)
    (hP10 : ∀ q ∈ Set.Icc (0 : ℝ) 1, P q {(true, false)} = ENNReal.ofReal b)
    (hP01 : ∀ q ∈ Set.Icc (0 : ℝ) 1, P q {(false, true)} = ENNReal.ofReal (c * q))
    (hP00 :
      ∀ q ∈ Set.Icc (0 : ℝ) 1, P q {(false, false)} = ENNReal.ofReal (c * (1 - q))) :
    let O : Bool × Bool → Bool × Bool := fun s ↦ (s.1, s.1 && s.2)
    ∀ q ∈ Set.Icc (0 : ℝ) 1,
      P q (O ⁻¹' {(true, true)}) = ENNReal.ofReal a ∧
      P q (O ⁻¹' {(true, false)}) = ENNReal.ofReal b ∧
      P q (O ⁻¹' {(false, false)}) = ENNReal.ofReal c ∧
      (∫ s, if s.2 then (1 : ℝ) else 0 ∂P q) = a + c * q
```

## derandomization_under_convex_loss

[Full input](derandomization_under_convex_loss/input.lean)

```lean
theorem derandomization_under_convex_loss
    (m N k : ℕ)
    (hm : 1 ≤ m)
    (hN : 1 ≤ N)
    (hk : 1 ≤ k)
    (p : Fin m → Fin N → ℝ)
    (hp0 : ∀ j x, 0 ≤ p j x)
    (hp1 : ∀ j x, p j x ≤ 1)
    (hpsum : ∀ j, ∑ x, p j x = 1)
    (a : Fin k → ℝ)
    (q : Fin N → Fin k → ℝ)
    (hq0 : ∀ x r, 0 ≤ q x r)
    (hq1 : ∀ x r, q x r ≤ 1)
    (hqsum : ∀ x, ∑ r, q x r = 1)
    (ell : Fin m → ℝ → ℝ)
    (hell0 : ∀ j t, 0 ≤ ell j t)
    (hellconv : ∀ j, ConvexOn ℝ Set.univ (ell j)) :
    ∀ j,
      ∑ x, p j x * ell j (∑ r, q x r * a r) ≤
        ∑ x, p j x * ∑ r, q x r * ell j (a r)
```

## difference_in_means_unbiased_random_assignment

[Full input](difference_in_means_unbiased_random_assignment/input.lean)

```lean
theorem difference_in_means_unbiased_random_assignment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n1 n0 : ℕ) (hn1 : n1 ≥ 1) (hn0 : n0 ≥ 1)
    (N : ℕ) (hN : N = n1 + n0)
    (Y1 Y0 : Fin N → ℝ)
    (W : Fin N → Ω → ℝ)
    (hW_meas : ∀ i, Measurable (W i))
    (hW_int : ∀ i, Integrable (W i) P)
    (hWc_int : ∀ i, Integrable (fun ω => 1 - W i ω) P)
    (hW_mean :
      ∀ i, (∫ ω, W i ω ∂P) = (n1 : ℝ) / (N : ℝ))
    (hWc_mean :
      ∀ i, (∫ ω, (1 - W i ω) ∂P) = (n0 : ℝ) / (N : ℝ)) :
    let tauHat : Ω → ℝ :=
      fun ω =>
        (1 / (n1 : ℝ)) * ∑ i : Fin N, W i ω * Y1 i -
          (1 / (n0 : ℝ)) * ∑ i : Fin N, (1 - W i ω) * Y0 i;
    let tau : ℝ :=
      (1 / (N : ℝ)) * ∑ i : Fin N, (Y1 i - Y0 i);
    (∫ ω, tauHat ω ∂P) = tau
```

## finite_two_point_minimax_lower_bound

[Full input](finite_two_point_minimax_lower_bound/input.lean)

```lean
theorem finite_two_point_minimax_lower_bound
    {Θ : Type*}
    [MetricSpace Θ]
    (N : ℕ)
    (hN : 1 ≤ N)
    (p0 p1 : Fin N → ℝ)
    (hp0_nonneg : ∀ x, 0 ≤ p0 x)
    (hp0_le_one : ∀ x, p0 x ≤ 1)
    (hp1_nonneg : ∀ x, 0 ≤ p1 x)
    (hp1_le_one : ∀ x, p1 x ≤ 1)
    (hp0_sum : ∑ x, p0 x = 1)
    (hp1_sum : ∑ x, p1 x = 1)
    (θ0 θ1 : Θ)
    (hθ : 0 < dist θ0 θ1)
    (T : Fin N → Θ) :
    let V : ℝ := (2 : ℝ)⁻¹ * ∑ x, |p0 x - p1 x|
    let R0 : ℝ := ∑ x, p0 x * dist (T x) θ0 ^ 2
    let R1 : ℝ := ∑ x, p1 x * dist (T x) θ1 ^ 2
    max R0 R1 ≥ dist θ0 θ1 ^ 2 / 8 * (1 - V)
```

## kaplan_meier_jump_mass_identity

[Full input](kaplan_meier_jump_mass_identity/input.lean)

```lean
theorem kaplan_meier_jump_mass_identity
    (m : ℕ) (hm : 1 ≤ m)
    (r d : ℕ → ℕ)
    (hr : ∀ j, 1 ≤ j → j ≤ m → 0 < r j)
    (hd : ∀ j, 1 ≤ j → j ≤ m → d j ≤ r j) :
    let S : ℕ → ℝ := fun k ↦
      ∏ j ∈ Finset.Icc 1 k, (1 - (d j : ℝ) / (r j : ℝ))
    let mass : ℕ → ℝ := fun j ↦
      S (j - 1) * (d j : ℝ) / (r j : ℝ)
    ∀ k, 1 ≤ k → k ≤ m →
      S k + ∑ j ∈ Finset.Icc 1 k, mass j = 1
```

## map_zero_one_optimal

[Full input](map_zero_one_optimal/input.lean)

```lean
theorem map_zero_one_optimal
    (Θ : Type*) [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
    (q : Θ → ℝ)
    (hq_mem : ∀ θ, q θ ∈ Icc 0 1)
    (hq_sum : ∑ θ, q θ = 1)
    (θmap : Θ)
    (hθmap : ∀ θ, q θ ≤ q θmap) :
    let loss : Θ → Θ → ℝ := fun θ a ↦ if θ ≠ a then 1 else 0
    let risk : Θ → ℝ := fun a ↦ ∑ θ, q θ * loss θ a
    ∀ a, risk θmap ≤ risk a
```

## median_minimizes_absolute_deviation

[Full input](median_minimizes_absolute_deviation/input.lean)

```lean
theorem median_minimizes_absolute_deviation
    (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (m : ℝ)
    (h_left : n ≤
      2 * (Finset.univ.filter (fun i : Fin n => x i ≤ m)).card)
    (h_right : n ≤
      2 * (Finset.univ.filter (fun i : Fin n => m ≤ x i)).card) :
    let L : ℝ → ℝ := fun a => ∑ i : Fin n, |x i - a|
    ∀ a : ℝ, L m ≤ L a
```

## negative_binomial_waiting_time_pmf

[Full input](negative_binomial_waiting_time_pmf/input.lean)

```lean
theorem negative_binomial_waiting_time_pmf
    (r m : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let countBefore : (Fin (m - 1) → Bool) → ℕ :=
      fun x => ∑ i : Fin (m - 1), if x i then (1 : ℕ) else 0
    let prefixProb : (Fin (m - 1) → Bool) → ℝ :=
      fun x => p ^ countBefore x * (1 - p) ^ ((m - 1) - countBefore x)
    (∑ x : Fin (m - 1) → Bool,
      if countBefore x = r - 1 then prefixProb x * p else 0) =
        (Nat.choose (m - 1) (r - 1) : ℝ) * p ^ r * (1 - p) ^ (m - r)
```

## paired_block_randomization_unbiased

[Full input](paired_block_randomization_unbiased/input.lean)

```lean
theorem paired_block_randomization_unbiased
    (b : ℕ) (hb : 1 ≤ b)
    (Y1 Y0 : Fin b → Fin 2 → ℝ) :
    let blockDiff : (Fin b → Bool) → Fin b → ℝ :=
      fun assign j =>
        if assign j then
          Y1 j (0 : Fin 2) - Y0 j (1 : Fin 2)
        else
          Y1 j (1 : Fin 2) - Y0 j (0 : Fin 2)
    let dbar : (Fin b → Bool) → ℝ :=
      fun assign => (1 / (b : ℝ)) * ∑ j : Fin b, blockDiff assign j
    let target : ℝ :=
      (1 / (b : ℝ)) *
        ∑ j : Fin b,
          ((Y1 j (0 : Fin 2) - Y0 j (0 : Fin 2)) +
            (Y1 j (1 : Fin 2) - Y0 j (1 : Fin 2))) / 2
    (1 / (Fintype.card (Fin b → Bool) : ℝ)) *
        ∑ assign : Fin b → Bool, dbar assign =
      target
```

## randomized_response_unbiased_prevalence

[Full input](randomized_response_unbiased_prevalence/input.lean)

```lean
theorem randomized_response_unbiased_prevalence
    (n : ℕ) (hn : 1 ≤ n)
    (q : ℝ) (hq_half : (1 : ℝ) / 2 < q) (hq_le_one : q ≤ 1)
    (x : Fin n → Bool) :
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let prevalence : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, bit (x i)
    let reportProb : (Fin n → Bool) → ℝ :=
      fun y => ∏ i : Fin n, if y i = x i then q else 1 - q
    let reportedMean : (Fin n → Bool) → ℝ :=
      fun y => (1 / (n : ℝ)) * ∑ i : Fin n, bit (y i)
    let debiased : (Fin n → Bool) → ℝ :=
      fun y => (reportedMean y - (1 - q)) / (2 * q - 1)
    (∑ y : Fin n → Bool, reportProb y * debiased y) = prevalence
```

## unbiasedness_of_empirical_distribution_function

[Full input](unbiasedness_of_empirical_distribution_function/input.lean)

```lean
theorem unbiasedness_of_empirical_distribution_function
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≥ 1) (X : Fin n → Ω → ℝ) (F : ℝ → ℝ) (t : ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (h_identically_distributed :
      ∀ i x, (P {ω | X i ω ≤ x}).toReal = F x) :
    let F_n_t : Ω → ℝ :=
      fun ω => (1 / (n : ℝ)) *
        ∑ i : Fin n, Set.indicator {ω' : Ω | X i ω' ≤ t} (fun _ => (1 : ℝ)) ω;
    (∫ ω, F_n_t ω ∂P) = F t
```

## arcsine_bernoulli_mean_clt

[Full input](arcsine_bernoulli_mean_clt/input.lean)

```lean
theorem arcsine_bernoulli_mean_clt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (X : ℕ → Ω → Bool)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      HasLaw (X i)
        (PMF.bernoulli ⟨θ, hθ₀.le⟩ (by exact_mod_cast hθ₁.le)).toMeasure P)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (hZ_law : HasLaw Z (gaussianReal 0 1) P) :
    let mean : ℕ → Ω → ℝ := fun r ω ↦
      ((r + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (r + 1), if X i ω then 1 else 0
    TendstoInDistribution
      (fun (r : ℕ) ω ↦ 2 * Real.sqrt (((r + 1 : ℕ) : ℝ)) *
        (Real.arcsin (Real.sqrt (mean r ω)) -
          Real.arcsin (Real.sqrt θ)))
      atTop Z P
```

## asymptotic_normality_of_sample_variance

[Full input](asymptotic_normality_of_sample_variance/input.lean)

```lean
theorem asymptotic_normality_of_sample_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean varianceSq fourthMoment : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfourth_integrable : Integrable (fun ω ↦ |X 0 ω| ^ 4) P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvariance :
      ∫ ω, (X 0 ω - mean) ^ 2 ∂P = varianceSq)
    (hfourth :
      ∫ ω, (X 0 ω - mean) ^ 4 ∂P = fourthMoment)
    (hgap : varianceSq ^ 2 < fourthMoment)
    (hG_meas : Measurable G)
    (hG_law :
      IdentDistrib G id P
        (gaussianReal 0
          ⟨fourthMoment - varianceSq ^ 2, sub_nonneg.mpr hgap.le⟩)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let V : ℕ → Ω → ℝ :=
      fun n ω ↦
        (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ Real.sqrt (n : ℝ) * (V n ω - varianceSq))
      atTop G P
```

## axial_extrinsic_mean_leading_eigenvector

[Full input](axial_extrinsic_mean_leading_eigenvector/input.lean)

```lean
theorem axial_extrinsic_mean_leading_eigenvector
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin n → Fin d → ℝ)
    (hx : ∀ i, dotProduct (x i) (x i) = 1)
    (v : Fin d → ℝ) (hv : dotProduct v v = 1)
    (lambda : ℝ) :
    let A : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    A *ᵥ v = lambda • v →
    (∀ u, dotProduct u u = 1 →
      dotProduct u (A *ᵥ u) ≤ lambda) →
    (∀ u, A *ᵥ u = lambda • u →
      ∃ c : ℝ, u = c • v) →
      let objective : (Fin d → ℝ) → ℝ := fun u ↦
        (n : ℝ)⁻¹ *
          ∑ i, ∑ j, ∑ k,
            (u j * u k - x i j * x i k) ^ 2
      {u : Fin d → ℝ |
        dotProduct u u = 1 ∧
          ∀ w, dotProduct w w = 1 → objective u ≤ objective w} =
        {v, -v}
```

## beta_bernoulli_marginal_likelihood

[Full input](beta_bernoulli_marginal_likelihood/input.lean)

```lean
theorem beta_bernoulli_marginal_likelihood
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → Bool) :
    let s : ℕ := ∑ i, if x i then 1 else 0
    let prior : ℝ → ℝ := fun t ↦
      t ^ (α - 1) * (1 - t) ^ (β - 1) / beta α β
    let likelihood : ℝ → ℝ := fun t ↦
      t ^ s * (1 - t) ^ (n - s)
    let marginal : ℝ :=
      ∫ t in Set.Icc (0 : ℝ) 1, likelihood t * prior t
    marginal = beta (α + s) (β + (n - s)) / beta α β
```

## binomial_clt_vanishing_probability

[Full input](binomial_clt_vanishing_probability/input.lean)

```lean
theorem binomial_clt_vanishing_probability
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℕ)
    (hY_meas : ∀ n, 1 ≤ n → AEMeasurable (Y n) μ)
    (Z : Ω → ℝ)
    (hZ_meas : Measurable Z)
    (hZ_law : Measure.map Z μ = gaussianReal 0 1) :
    let p : ℕ → ℝ :=
      fun n => 1 / Real.sqrt (n : ℝ)
    let W : ℕ → Ω → ℝ :=
      fun n ω =>
        if 1 ≤ n then
          (n : ℝ) ^ (3 / 4 : ℝ) *
            (((Y n ω : ℝ) / (n : ℝ)) - p n)
        else
          0
    ∀ hY_dist : ∀ (n : ℕ) (hn : 1 ≤ n),
      Measure.map (Y n) μ =
        binomialMeasure n
          (Real.toNNReal (p n))
          (toNNReal_one_div_sqrt_n_le_one n hn),
      TendstoInDistribution W atTop Z μ
```

## bootstrap_sample_variance_conditional_mean

[Full input](bootstrap_sample_variance_conditional_mean/input.lean)

```lean
theorem bootstrap_sample_variance_conditional_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i,
      IdentDistrib (X i) (X ⟨0, Nat.zero_lt_of_lt hn⟩) P P)
    (hX_sq : Integrable
      (fun ω ↦ (X ⟨0, Nat.zero_lt_of_lt hn⟩ ω) ^ 2) P)
    (I : Fin n → Ω → Fin n)
    (hI_meas : ∀ j, Measurable (I j))
    (hI_indep : iIndepFun I P)
    (hI_uniform : ∀ i j, P {ω | I j ω = i} = (n : ENNReal)⁻¹)
    (hIX_indep :
      IndepFun (fun ω j ↦ I j ω) (fun ω i ↦ X i ω) P) :
    let Xstar : Fin n → Ω → ℝ := fun j ω ↦ X (I j ω) ω
    let mean : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * ∑ i, X i ω
    let meanStar : Ω → ℝ := fun ω ↦ (n : ℝ)⁻¹ * ∑ j, Xstar j ω
    let V : Ω → ℝ := fun ω ↦
      (n : ℝ)⁻¹ * ∑ i, (X i ω - mean ω) ^ 2
    let Vstar : Ω → ℝ := fun ω ↦
      (n : ℝ)⁻¹ * ∑ j, (Xstar j ω - meanStar ω) ^ 2
    let G : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω i ↦ X i ω)
        (inferInstance : MeasurableSpace (Fin n → ℝ))
    condExp G P Vstar =ᵐ[P]
      fun ω ↦ (((n - 1 : ℕ) : ℝ) / (n : ℝ)) * V ω
```

## brier_score_calibration_decomposition

[Full input](brier_score_calibration_decomposition/input.lean)

```lean
theorem brier_score_calibration_decomposition
    (N H : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (group : Fin N → Fin H)
    (forecast : Fin H → ℝ)
    (h_forecast_prob : ∀ g : Fin H, 0 ≤ forecast g ∧ forecast g ≤ 1)
    (outcome : Fin N → Bool)
    (h_nonempty :
      ∀ g : Fin H,
        0 < (Finset.univ.filter (fun i : Fin N => group i = g)).card) :
    let bit : Bool → ℝ := fun b => if b then 1 else 0
    let bin : Fin H → Finset (Fin N) :=
      fun g => Finset.univ.filter (fun i : Fin N => group i = g)
    let binSize : Fin H → ℝ := fun g => ((bin g).card : ℝ)
    let ybar : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, bit (outcome i)
    let ybarBin : Fin H → ℝ :=
      fun g => (1 / binSize g) * (bin g).sum (fun i => bit (outcome i))
    let weight : Fin H → ℝ := fun g => binSize g / (N : ℝ)
    let brier : ℝ :=
      (1 / (N : ℝ)) *
        ∑ i : Fin N, (forecast (group i) - bit (outcome i)) ^ 2
    let reliability : ℝ :=
      ∑ g : Fin H, weight g * (forecast g - ybarBin g) ^ 2
    let resolution : ℝ :=
      ∑ g : Fin H, weight g * (ybarBin g - ybar) ^ 2
    let uncertainty : ℝ := ybar * (1 - ybar)
    brier = reliability - resolution + uncertainty
```

## chebyshev_sample_mean_bound

[Full input](chebyshev_sample_mean_bound/input.lean)

```lean
theorem chebyshev_sample_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_memLp : ∀ i, MemLp (X i) 2 P)
    (hX_mean : ∀ i, (∫ ω, X i ω ∂P) = mu)
    (hX_var : ∀ i, ProbabilityTheory.variance (X i) P = sigma2)
    (hX_indep : ProbabilityTheory.iIndepFun (β := fun _ : ℕ => ℝ) X P)
    (hX_ident : ∀ i j, ProbabilityTheory.IdentDistrib (X i) (X j) P P) :
    let barX : (n : ℕ) → Ω → ℝ :=
      fun n ω => (∑ i : Fin n, X (i : ℕ) ω) / (n : ℝ)
    (∀ n : ℕ, 1 ≤ n →
      ProbabilityTheory.variance (barX n) P =
        sigma2 / (n : ℝ)) ∧
    (∀ (n : ℕ) (epsilon : ℝ), 1 ≤ n → 0 < epsilon →
      (P {ω | epsilon ≤ |barX n ω - mu|}).toReal ≤
        sigma2 / ((n : ℝ) * epsilon ^ 2)) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n : ℕ => (P {ω | epsilon ≤ |barX n ω - mu|}).toReal)
        atTop (nhds 0))
```

## cox_risk_set_probability_for_exponential_times

[Full input](cox_risk_set_probability_for_exponential_times/input.lean)

```lean
theorem cox_risk_set_probability_for_exponential_times
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda₀ beta : ℝ) (hlambda : 0 < lambda₀)
    (z : Fin n → ℝ)
    (T : Fin n → Ω → ℝ)
    (hTmeas : ∀ i, Measurable (T i))
    (hTnonneg : ∀ i ω, 0 ≤ T i ω)
    (hindep : iIndepFun T P)
    (hsurvival : ∀ i t, 0 ≤ t →
      P {ω | t < T i ω} =
        ENNReal.ofReal (Real.exp (-lambda₀ * Real.exp (beta * z i) * t))) :
    ∀ i,
      P {ω | ∀ j, j ≠ i → T i ω < T j ω} =
        ENNReal.ofReal
          (Real.exp (beta * z i) /
            ∑ j, Real.exp (beta * z j))
```

## doubly_robust_mean_identification_under_mar

[Full input](doubly_robust_mean_identification_under_mar/input.lean)

```lean
theorem doubly_robust_mean_identification_under_mar
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (R : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y : Ω → ℝ)
    (hRmeas : Measurable R)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hYint : Integrable Y P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hMAR :
      ∀ (B : Set ℝ), MeasurableSet B → ∀ r z,
        P {ω | Y ω ∈ B ∧ R ω = r ∧ Z ω = z} * P {ω | Z ω = z} =
          P {ω | Y ω ∈ B ∧ Z ω = z} * P {ω | R ω = r ∧ Z ω = z})
    (m : 𝒵 → ℝ)
    (π : 𝒵 → ℝ)
    (hπpos : ∀ z, 0 < π z)
    (hπle : ∀ z, π z ≤ 1) :
    let m0 : 𝒵 → ℝ := fun z ↦
      (∫ ω in {ω | Z ω = z}, Y ω ∂P) / (P {ω | Z ω = z}).toReal
    let π0 : 𝒵 → ℝ := fun z ↦
      (P {ω | R ω = true ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    (∀ z, 0 < π0 z) →
      (m = m0 ∨ π = π0) →
      ∫ ω,
          m (Z ω) +
            (if R ω then (1 : ℝ) else 0) / π (Z ω) * (Y ω - m (Z ω))
        ∂P =
        ∫ ω, Y ω ∂P
```

## eventual_recovery_unique_frechet_mean_finite_space

[Full input](eventual_recovery_unique_frechet_mean_finite_space/input.lean)

```lean
theorem eventual_recovery_unique_frechet_mean_finite_space
    {Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]
    [Fintype 𝓧] [LinearOrder 𝓧] [MetricSpace 𝓧] [Nonempty 𝓧]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → 𝓧)
    (hXmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (mu : 𝓧)
    (hunique : ∀ z, z ≠ mu →
      (∑ x, (P {ω | X 0 ω = x}).toReal * dist mu x ^ 2) <
        ∑ x, (P {ω | X 0 ω = x}).toReal * dist z x ^ 2)
    (muHat : ℕ → Ω → 𝓧)
    (hmuHatmeas : ∀ n, Measurable (muHat n))
    (hmin : ∀ n, 1 ≤ n → ∀ ω z,
      (∑ i ∈ Finset.range n, dist (muHat n ω) (X i ω) ^ 2) ≤
        ∑ i ∈ Finset.range n, dist z (X i ω) ^ 2)
    (hsmallest : ∀ n, 1 ≤ n → ∀ ω z,
      (∑ i ∈ Finset.range n, dist z (X i ω) ^ 2) =
          ∑ i ∈ Finset.range n, dist (muHat n ω) (X i ω) ^ 2 →
        muHat n ω ≤ z) :
    P {ω | ∃ N ≥ 1, ∀ n ≥ N, muHat n ω = mu} = 1
```

## exact_student_t_distribution_ols_contrast

[Full input](exact_student_t_distribution_ols_contrast/input.lean)

```lean
theorem exact_student_t_distribution_ols_contrast
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hnp : p < n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (betaStar : Fin p → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ b : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct b (epsilon ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct b b))) P)
    (a : Fin p → ℝ) (ha : a ≠ 0)
    (c : ℝ) (hnull : dotProduct a betaStar = c) :
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin p → ℝ := fun ω ↦
      (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    let sigmaHatSq : Ω → ℝ := fun ω ↦
      dotProduct (y ω - X *ᵥ betaHat ω)
          (y ω - X *ᵥ betaHat ω) / ((n - p : ℕ) : ℝ)
    let statistic : Ω → ℝ := fun ω ↦
      (dotProduct a (betaHat ω) - c) /
        (Real.sqrt (sigmaHatSq ω) *
          Real.sqrt (dotProduct a ((X.transpose * X)⁻¹ *ᵥ a)))
    let nu : ℝ := ((n - p : ℕ) : ℝ)
    let density : ℝ → ℝ := fun z ↦
      Real.Gamma ((nu + 1) / 2) /
          (Real.sqrt (nu * Real.pi) * Real.Gamma (nu / 2)) *
        Real.rpow (1 + z ^ 2 / nu) (-(nu + 1) / 2)
    let studentT : Measure ℝ :=
      volume.withDensity (fun z ↦ ENNReal.ofReal (density z))
    HasLaw statistic studentT P
```

## finite_class_empirical_concentration

[Full input](finite_class_empirical_concentration/input.lean)

```lean
theorem finite_class_empirical_concentration
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (sample : Fin n → Omega → X)
    (h_sample_meas : ∀ i, Measurable (sample i))
    (h_sample_iid : ∀ i j, IdentDistrib (sample i) (sample j) P P)
    (h_sample_indep : iIndepFun (β := fun _ : Fin n => X) sample P)
    (f : Fin N → X → ℝ)
    (h_f_meas : ∀ j, Measurable (f j))
    (h_f_range : ∀ j x, f j x ∈ Set.Icc (0 : ℝ) 1) :
    let empirical (j : Fin N) (omega : Omega) : ℝ :=
      (∑ i : Fin n, f j (sample i omega)) / (n : ℝ)
    let population (j : Fin N) : ℝ :=
      ∫ omega, f j (sample ⟨0, Nat.pos_of_ne_zero (by omega)⟩ omega) ∂P
    ∀ delta : ℝ, 0 < delta → delta < 1 →
      (P {omega |
        (Finset.univ.sup'
          ⟨⟨0, hN⟩, Finset.mem_univ _⟩
          (fun j : Fin N =>
            |empirical j omega - population j|)) ≤
          Real.sqrt (Real.log (2 * (N : ℝ) / delta) / (2 * (n : ℝ))) }).toReal
        ≥ 1 - delta
```

## finite_population_correction_srs

[Full input](finite_population_correction_srs/input.lean)

```lean
theorem finite_population_correction_srs
    (N n : ℕ) (hN : 2 ≤ N) (hn_pos : 1 ≤ n) (hn_le : n ≤ N)
    (y : Fin N → ℝ) :
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = n)
    let mu : ℝ := (1 / (N : ℝ)) * ∑ i : Fin N, y i
    let sampleMean : Finset (Fin N) → ℝ :=
      fun S => (1 / (n : ℝ)) * S.sum (fun i => y i)
    let popVar : ℝ :=
      (1 / ((N - 1 : ℕ) : ℝ)) * ∑ i : Fin N, (y i - mu) ^ 2
    let varSampleMean : ℝ :=
      (1 / (samples.card : ℝ)) *
        samples.sum (fun S => (sampleMean S - mu) ^ 2)
    varSampleMean =
      (1 - (n : ℝ) / (N : ℝ)) * popVar / (n : ℝ)
```

## frisch_waugh_lovell_identity

[Full input](frisch_waugh_lovell_identity/input.lean)

```lean
theorem frisch_waugh_lovell_identity
    (n p q : ℕ) (hn : p + q ≤ n) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (X₁ : Matrix (Fin n) (Fin p) ℝ)
    (X₂ : Matrix (Fin n) (Fin q) ℝ)
    (y : Fin n → ℝ)
    (hfull : ∀ beta : Fin p → ℝ, ∀ gamma : Fin q → ℝ,
      X₁ *ᵥ beta + X₂ *ᵥ gamma = 0 → beta = 0 ∧ gamma = 0)
    (betaHat : Fin p → ℝ)
    (gammaHat : Fin q → ℝ)
    (hmin : ∀ beta : Fin p → ℝ, ∀ gamma : Fin q → ℝ,
      dotProduct (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat)
          (y - X₁ *ᵥ betaHat - X₂ *ᵥ gammaHat) ≤
        dotProduct (y - X₁ *ᵥ beta - X₂ *ᵥ gamma)
          (y - X₁ *ᵥ beta - X₂ *ᵥ gamma)) :
    let M₁ : Matrix (Fin n) (Fin n) ℝ :=
      1 - X₁ * (X₁.transpose * X₁)⁻¹ * X₁.transpose
    gammaHat =
      (X₂.transpose * M₁ * X₂)⁻¹ *ᵥ
        (X₂.transpose *ᵥ (M₁ *ᵥ y))
```

## functional_pca_reconstruction_mean_squared_error

[Full input](functional_pca_reconstruction_mean_squared_error/input.lean)

```lean
theorem functional_pca_reconstruction_mean_squared_error
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (C : H →L[ℝ] H)
    (phi : ℕ → H) (lambda : ℕ → ℝ)
    (horth : Orthonormal ℝ phi)
    (hcomplete : Dense (Submodule.span ℝ (Set.range phi) : Set H))
    (heigen : ∀ k, C (phi k) = lambda k • phi k)
    (hlambda : Antitone lambda)
    (hlambda_nonneg : ∀ k, 0 ≤ lambda k)
    (hC : ∀ h,
      C h =
        ∫ ω, (inner ℝ (X ω - ∫ z, X z ∂P) h) •
          (X ω - ∫ z, X z ∂P) ∂P) :
    ∀ r : ℕ, 1 ≤ r →
      let mu : H := ∫ ω, X ω ∂P
      let Xr : Ω → H := fun ω ↦
        mu + ∑ k ∈ Finset.range r,
          (inner ℝ (X ω - mu) (phi k)) • phi k
      ∫ ω, ‖X ω - Xr ω‖ ^ 2 ∂P =
        ∑' k : ℕ, if r ≤ k then lambda k else 0
```

## german_tank_estimator_unbiased

[Full input](german_tank_estimator_unbiased/input.lean)

```lean
theorem german_tank_estimator_unbiased
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (M : Ω → ℕ) (hM_meas : Measurable M)
    (hM_range : ∀ ω, n ≤ M ω ∧ M ω ≤ N)
    (hM_pmf : ∀ r, n ≤ r → r ≤ N →
      P {ω | M ω = r} =
        ENNReal.ofReal ((Nat.choose (r - 1) (n - 1) : ℝ) / Nat.choose N n)) :
    ∫ ω, (((n + 1 : ℕ) : ℝ) / (n : ℝ)) * (M ω : ℝ) - 1 ∂P = (N : ℝ)
```

## ipw_identification_under_ignorability

[Full input](ipw_identification_under_ignorability/input.lean)

```lean
theorem ipw_identification_under_ignorability
    {Ω 𝒵 : Type*}
    [MeasurableSpace Ω]
    [Fintype 𝒵]
    [MeasurableSpace 𝒵]
    [MeasurableSingletonClass 𝒵]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (T : Ω → Bool)
    (Z : Ω → 𝒵)
    (Y Y0 Y1 : Ω → ℝ)
    (hTmeas : Measurable T)
    (hZmeas : Measurable Z)
    (hYmeas : Measurable Y)
    (hY0meas : Measurable Y0)
    (hY1meas : Measurable Y1)
    (hYint : Integrable Y P)
    (hY0int : Integrable Y0 P)
    (hY1int : Integrable Y1 P)
    (hZpos : ∀ z, 0 < P {ω | Z ω = z})
    (hObserved : Y =ᵐ[P] fun ω ↦ if T ω then Y1 ω else Y0 ω)
    (hIgnorable :
      ∀ (a : Bool) (B : Set ℝ), MeasurableSet B → ∀ t z,
        P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ T ω = t ∧ Z ω = z} *
            P {ω | Z ω = z} =
          P {ω | (if a then Y1 ω else Y0 ω) ∈ B ∧ Z ω = z} *
            P {ω | T ω = t ∧ Z ω = z})
    (hPositive :
      ∀ a z, 0 <
        (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal) :
    let e : Bool → 𝒵 → ℝ := fun a z ↦
      (P {ω | T ω = a ∧ Z ω = z}).toReal / (P {ω | Z ω = z}).toReal
    ∀ a : Bool,
      ∫ ω, (if a then Y1 ω else Y0 ω) ∂P =
        ∫ ω, (if T ω = a then (1 : ℝ) else 0) * Y ω / e a (Z ω) ∂P
```

## kernel_density_concentration

[Full input](kernel_density_concentration/input.lean)

```lean
theorem kernel_density_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hX_law : ∀ i,
      HasLaw (X i) (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) P)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (h : ℝ) (hh : 0 < h) :
    let estimate : Ω → ℝ → ℝ := fun ω x ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((x - X i ω) / h)
    ∀ δ : ℝ, 0 ≤ δ →
      (P {ω |
        (∫ x, |estimate ω x - f x|) ≥
          (∫ z, ∫ x, |estimate z x - f x| ∂volume ∂P) + δ}).toReal ≤
        Real.exp (-(n : ℝ) * δ ^ 2 / 8)
```

## kernel_density_mean_variance

[Full input](kernel_density_mean_variance/input.lean)

```lean
theorem kernel_density_mean_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (p : ℝ → ℝ) (hp_meas : Measurable p)
    (hX_law : ∀ i,
      HasLaw (X i) (volume.withDensity (fun x ↦ ENNReal.ofReal (p x))) P)
    (pmax : ℝ) (hpmax : 0 ≤ pmax)
    (hp_nonneg : ∀ᵐ x ∂volume, 0 ≤ p x)
    (hp_bound : ∀ᵐ x ∂volume, p x ≤ pmax)
    (K : ℝ → ℝ) (hK_meas : Measurable K)
    (hK_nonneg : ∀ u, 0 ≤ K u)
    (hK_int : Integrable K)
    (hK_one : ∫ u, K u = 1)
    (hK_sq_int : Integrable (fun u ↦ (K u) ^ 2))
    (x h : ℝ) (hh : 0 < h) :
    let estimate : Ω → ℝ := fun ω ↦
      ((n : ℝ) * h)⁻¹ * ∑ i, K ((X i ω - x) / h)
    (∫ ω, estimate ω ∂P = ∫ u, K u * p (x + h * u)) ∧
      variance estimate P =
        ((n : ℝ) * h)⁻¹ * (∫ u, (K u) ^ 2 * p (x + h * u)) -
          (n : ℝ)⁻¹ * (∫ u, K u * p (x + h * u)) ^ 2
```

## kernel_regression_interior_imse_rate

[Full input](kernel_regression_interior_imse_rate/input.lean)

```lean
theorem kernel_regression_interior_imse_rate
    (d : ℕ) (hd : 1 ≤ d)
    (alpha : ℝ) (halpha : 0 < alpha)
    (nu b : ℝ) (hnu : 0 < nu) (hb : 0 < b)
    (L0 MK LK gamma MAlpha Cv : ℝ)
    (hL0 : 0 ≤ L0) (hMK : 0 ≤ MK) (hLK : 0 ≤ LK)
    (hgamma : 0 < gamma) (hMAlpha : 0 ≤ MAlpha) (hCv : 0 ≤ Cv) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f0 : Cube d → ℝ)
        (K : ℝ → Cube d → Cube d → ℝ)
        (muU : Measure (Cube d)) [IsProbabilityMeasure muU]
        (h_uniform : IsUniformOnUnitCube muU)
        {Omega : Type*} [MeasurableSpace Omega]
        (P : Measure Omega) [IsProbabilityMeasure P]
        (n : ℕ) (hn : 1 ≤ n)
        (X : Fin n → Omega → Cube d)
        (Y xi : Fin n → Omega → ℝ)
        (muI : Measure (Cube d)) [IsFiniteMeasure muI]
        (hX_meas : ∀ i, Measurable (X i))
        (hX_cube : ∀ i omega, InUnitCube (X i omega))
        (hX_law : ∀ i, Measure.map (X i) P = muU)
        (hY_meas : ∀ i, Measurable (Y i))
        (hxi_meas : ∀ i, Measurable (xi i))
        (hxi_integrable : ∀ i, Integrable (xi i) P)
        (h_regression_model : ∀ i omega,
          Y i omega = f0 (X i omega) + xi i omega)
        (hxi_centered : ∀ i, ∫ omega, xi i omega ∂P = 0)
        (hxi_exp_integrable : ∀ (i : Fin n) (t : ℝ), |t| < 1 / b →
          Integrable (fun omega => Real.exp (t * xi i omega)) P)
        (hxi_subexponential : ∀ (i : Fin n) (t : ℝ), |t| < 1 / b →
          ∫ omega, Real.exp (t * xi i omega) ∂P ≤
            Real.exp (nu ^ 2 * t ^ 2 / (2 * (1 - b * |t|))))
        (h_package : KernelRiskPackage P d n alpha
          (Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
          f0 K muU muI
          (fun x omega =>
            (1 / (n : ℝ)) * ∑ i : Fin n,
              K (Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ))))
                x (X i omega) * Y i omega)
          L0 MK LK gamma MAlpha Cv),
        let h : ℝ := Real.rpow (n : ℝ) (-1 / (2 * alpha + (d : ℝ)))
        let I_h : Set (Cube d) := {x | InInteriorBand h x}
        let estimator (x : Cube d) (omega : Omega) : ℝ :=
          (1 / (n : ℝ)) * ∑ i : Fin n, K h x (X i omega) * Y i omega
        (∫ x in I_h,
          ∫ omega, (estimator x omega - f0 x) ^ 2 ∂P ∂muI) ≤
          C * Real.rpow (n : ℝ)
            (-2 * alpha / (2 * alpha + (d : ℝ)))
```

## lasso_infinity_norm_error_bound

[Full input](lasso_infinity_norm_error_bound/input.lean)

```lean
theorem lasso_infinity_norm_error_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hcols : ∀ j,
      dotProduct (fun i ↦ X i j) (fun i ↦ X i j) / (n : ℝ) ≤ 1)
    (S : Finset (Fin d))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hRE : ∀ Delta : Fin d → ℝ,
      (∑ j, if j ∈ S then (0 : ℝ) else |Delta j|) ≤
          3 * (∑ j, if j ∈ S then |Delta j| else (0 : ℝ)) →
      (⨆ j, |(((n : ℝ)⁻¹ • (X.transpose * X)) *ᵥ Delta) j|) ≥
        gamma * ⨆ j, |Delta j|)
    (thetaStar : Fin d → ℝ)
    (hsupport : ∀ j, j ∉ S → thetaStar j = 0)
    (w : Ω → Fin n → ℝ)
    (hw : ∀ a : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct a (w ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P) :
    let lambda := 4 * sigma *
      Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ thetaStar + w ω
    let objective : Ω → (Fin d → ℝ) → ℝ := fun ω theta ↦
      dotProduct (y ω - X *ᵥ theta) (y ω - X *ᵥ theta) /
          (2 * (n : ℝ)) +
        lambda * ∑ j, |theta j|
    let minimizers : Ω → Set (Fin d → ℝ) := fun ω ↦
      {theta | ∀ eta, objective ω theta ≤ objective ω eta}
    let good : Set Ω := {ω | ∀ thetaHat ∈ minimizers ω,
      (⨆ j, |(thetaHat - thetaStar) j|) ≤
        6 * sigma / gamma *
          Real.sqrt (Real.log (d : ℝ) / (n : ℝ))}
    NullMeasurableSet good P ∧
      P good ≥ ENNReal.ofReal (1 - 2 / (d : ℝ))
```

## lasso_restricted_eigenvalue_rate

[Full input](lasso_restricted_eigenvalue_rate/input.lean)

```lean
theorem lasso_restricted_eigenvalue_rate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset (Fin n))
    (x : Fin m → Fin n → ℝ)
    (X : Fin m → Fin n → ℝ)
    (hX : ∀ i j, X i j = x i j)
    (sigmaHat : Matrix (Fin n) (Fin n) ℝ)
    (hSigmaHat : ∀ j k,
      sigmaHat j k = (1 / (m : ℝ)) * ∑ i : Fin m, X i j * X i k)
    (kappa Lambda B sigma lambda : ℝ)
    (hkappa : 0 < kappa) (hLambda : 0 < Lambda) (hB : 0 < B)
    (hsigma : 0 < sigma) (hlambda : 0 < lambda)
    (hRE : ∀ v : Fin n → ℝ,
      (∑ j ∈ Finset.univ.filter (fun j => j ∉ S), |v j|) ≤
        3 * (∑ j ∈ S, |v j|) →
      kappa ^ 2 * (∑ j : Fin n, (v j) ^ 2) ≤
        ∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k)
    (hUpper : ∀ v : Fin n → ℝ,
      (∑ j : Fin n, ∑ k : Fin n, v j * sigmaHat j k * v k) ≤
        Lambda * ∑ j : Fin n, (v j) ^ 2)
    (hscale : (m : ℝ) * Lambda ≤ B ^ 2)
    (epsilon : Fin m → Omega → ℝ)
    (h_epsilon_meas : ∀ i, Measurable (epsilon i))
    (h_epsilon_integrable : ∀ i, Integrable (epsilon i) P)
    (h_epsilon_indep : iIndepFun (β := fun _ : Fin m => ℝ) epsilon P)
    (h_epsilon_centered : ∀ i, ∫ omega, epsilon i omega ∂P = 0)
    (h_epsilon_exp_integrable : ∀ (i : Fin m) (t : ℝ),
      Integrable (fun omega => Real.exp (t * epsilon i omega)) P)
    (h_epsilon_subGaussian : ∀ (i : Fin m) (t : ℝ),
      ∫ omega, Real.exp (t * epsilon i omega) ∂P ≤
        Real.exp (sigma * t ^ 2 / 2))
    (betaStar : Fin n → ℝ)
    (h_support : ∀ j, j ∉ S → betaStar j = 0) :
    let score (omega : Omega) : Prop :=
      ∀ j : Fin n, |(1 / (m : ℝ)) * ∑ i : Fin m, X i j * epsilon i omega| ≤ lambda / 2
    let response (omega : Omega) (i : Fin m) : ℝ :=
      (∑ j : Fin n, X i j * betaStar j) + epsilon i omega
    let objective (omega : Omega) (beta : Fin n → ℝ) : ℝ :=
      (1 / (2 * (m : ℝ))) *
          ∑ i : Fin m, (response omega i - ∑ j : Fin n, X i j * beta j) ^ 2 +
        lambda * ∑ j : Fin n, |beta j|
    let lassoSolution (omega : Omega) (beta : Fin n → ℝ) : Prop :=
      ∀ gamma : Fin n → ℝ, objective omega beta ≤ objective omega gamma
    let oracleBounds (betaHat : Fin n → ℝ) : Prop :=
        (1 / (m : ℝ)) * ∑ i : Fin m,
            (∑ j : Fin n, X i j * (betaHat j - betaStar j)) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 2 ∧
        (∑ j : Fin n, |betaHat j - betaStar j|) ≤
              8 * lambda * (S.card : ℝ) / kappa ^ 2 ∧
        ∑ j : Fin n, (betaHat j - betaStar j) ^ 2 ≤
              16 * lambda ^ 2 * (S.card : ℝ) / kappa ^ 4
    (P {omega | score omega}).toReal ≥
        1 - 2 * (n : ℝ) * Real.exp (-((m : ℝ) ^ 2 * (lambda / 2) ^ 2) /
          (2 * sigma * B ^ 2)) ∧
      ∀ omega, score omega → ∀ betaHat : Fin n → ℝ,
        lassoSolution omega betaHat → oracleBounds betaHat
```

## leading_functional_pca_perturbation_bound

[Full input](leading_functional_pca_perturbation_bound/input.lean)

```lean
theorem leading_functional_pca_perturbation_bound
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H)
    (hXmeas : StronglyMeasurable X)
    (hXmean : ∫ ω, X ω ∂P = 0)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (n : ℕ) (hn : 1 ≤ n)
    (x : Fin n → H)
    (C Chat : H →L[ℝ] H)
    (hC : ∀ h, C h =
      ∫ ω, (inner ℝ (X ω) h) • X ω ∂P)
    (hChat : ∀ h, Chat h =
      (n : ℝ)⁻¹ • ∑ i, (inner ℝ (x i) h) • x i)
    (phi phiHat : H)
    (lambda₁ lambda₂ lambdaHat : ℝ)
    (hphi : ‖phi‖ = 1)
    (hphiHat : ‖phiHat‖ = 1)
    (heigen : C phi = lambda₁ • phi)
    (hgap : lambda₂ < lambda₁)
    (hsecond : ∀ h, ‖h‖ = 1 → inner ℝ h phi = 0 →
      inner ℝ (C h) h ≤ lambda₂)
    (hhatEigen : Chat phiHat = lambdaHat • phiHat)
    (hhatMax : ∀ h, ‖h‖ = 1 →
      inner ℝ (Chat h) h ≤ lambdaHat) :
    let delta := lambda₁ - lambda₂
    let epsilon := ‖Chat - C‖
    epsilon ≤ delta / 2 →
      Real.sqrt (1 - (inner ℝ phiHat phi) ^ 2) ≤
        epsilon / (delta - epsilon)
```

## leading_principal_component

[Full input](leading_principal_component/input.lean)

```lean
theorem leading_principal_component
    (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (hcenter : ∑ i, x i = 0)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    let S : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    let first : Fin d := ⟨0, by omega⟩
    (∀ j, S *ᵥ v j = lambda j • v j) →
    Antitone lambda →
    (∀ j, j ≠ first → lambda first > lambda j) →
      let objective : (Fin d → ℝ) → ℝ := fun u ↦
        (n : ℝ)⁻¹ * ∑ i, (dotProduct u (x i)) ^ 2
      {u : Fin d → ℝ |
        dotProduct u u = 1 ∧
          ∀ w, dotProduct w w = 1 → objective w ≤ objective u} =
        {-v first, v first}
```

## linear_smoother_risk

[Full input](linear_smoother_risk/input.lean)

```lean
theorem linear_smoother_risk
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (f : Fin n → ℝ)
    (xi : Ω → Fin n → ℝ)
    (hxi_meas : Measurable xi)
    (hxi_sq_int : Integrable (fun ω ↦ ∑ i, (xi ω i) ^ 2) P)
    (sigma2 : ℝ) (hsigma2 : 0 ≤ sigma2)
    (hxi_mean : ∀ i, ∫ ω, xi ω i ∂P = 0)
    (hxi_cov : ∀ i j,
      ∫ ω, xi ω i * xi ω j ∂P = if i = j then sigma2 else 0)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    let Y : Ω → Fin n → ℝ := fun ω i ↦ f i + xi ω i
    let estimate : Ω → Fin n → ℝ := fun ω ↦ S.mulVec (Y ω)
    let normSq : (Fin n → ℝ) → ℝ := fun v ↦
      (n : ℝ)⁻¹ * ∑ i, (v i) ^ 2
    ∫ ω, normSq (estimate ω - f) ∂P =
      normSq (S.mulVec f - f) +
        sigma2 * (n : ℝ)⁻¹ * Matrix.trace (S.transpose * S)
```

## local_asymptotic_power_of_asymptotically_normal_test

[Full input](local_asymptotic_power_of_asymptotically_normal_test/input.lean)

```lean
theorem local_asymptotic_power_of_asymptotically_normal_test
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℕ → ProbabilityMeasure Ω)
    (thetaHat : ℕ → Ω → ℝ)
    (theta₀ h c sigma : ℝ)
    (hsigma : 0 < sigma)
    (hthetaHat : ∀ n, Measurable (thetaHat n))
    (hasymptotic_normality :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map (P (n + 1))
            (show
              AEMeasurable
                (fun ω ↦
                  Real.sqrt (n + 1 : ℝ) *
                      (thetaHat (n + 1) ω -
                        (theta₀ + h / Real.sqrt (n + 1 : ℝ))) /
                    sigma)
                (P (n + 1)) by
              fun_prop))
        atTop
        (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ :
          ProbabilityMeasure ℝ))) :
    Tendsto
      (fun n ↦
        ENNReal.toReal
          ((P (n + 1) : Measure Ω)
            {ω |
              Real.sqrt (n + 1 : ℝ) *
                  (thetaHat (n + 1) ω - theta₀) /
                sigma >
              c}))
      atTop
      (𝓝
        (1 -
          cdf (gaussianReal 0 1) (c - h / sigma)))
```

## local_polynomial_reproduction

[Full input](local_polynomial_reproduction/input.lean)

```lean
theorem local_polynomial_reproduction
    (n : ℕ) (hn : 1 ≤ n)
    (ell : ℕ)
    (X : Fin n → ℝ)
    (K : ℝ → ℝ) (hK_nonneg : ∀ u, 0 ≤ K u)
    (x h : ℝ) (hh : 0 < h) :
    let U : ℝ → Fin (ell + 1) → ℝ := fun u k ↦
      u ^ k.1 / (Nat.factorial k.1 : ℝ)
    let B : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ := fun a b ↦
      ((n : ℝ) * h)⁻¹ *
        ∑ i, U ((X i - x) / h) a * U ((X i - x) / h) b *
          K ((X i - x) / h)
    IsUnit B.det →
      let W : Fin n → ℝ := fun i ↦
        ((n : ℝ) * h)⁻¹ *
          (∑ a, U 0 a * ∑ b, B⁻¹ a b * U ((X i - x) / h) b) *
          K ((X i - x) / h)
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ ell →
        ∑ i, W i * Q.eval (X i) = Q.eval x
```

## logistic_score_balance_with_intercept

[Full input](logistic_score_balance_with_intercept/input.lean)

```lean
theorem logistic_score_balance_with_intercept
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (x : Fin n → Fin d → ℝ)
    (y : Fin n → Bool)
    (aHat : ℝ) (bHat : Fin d → ℝ)
    (hmax : ∀ a : ℝ, ∀ b : Fin d → ℝ,
      ∑ i, ((if y i then 1 else 0 : ℝ) * (aHat + dotProduct (x i) bHat) -
          Real.log (1 + Real.exp (aHat + dotProduct (x i) bHat))) ≥
        ∑ i, ((if y i then 1 else 0 : ℝ) * (a + dotProduct (x i) b) -
          Real.log (1 + Real.exp (a + dotProduct (x i) b)))) :
    ∑ i, (1 + Real.exp (-aHat - dotProduct (x i) bHat))⁻¹ =
      ∑ i, (if y i then 1 else 0 : ℝ)
```

## mse_gap_two_normal_variance_estimators

[Full input](mse_gap_two_normal_variance_estimators/input.lean)

```lean
theorem mse_gap_two_normal_variance_estimators
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (mean sigma : ℝ) (hsigma : 0 < sigma)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      IdentDistrib (X i) id P
        (gaussianReal mean ⟨sigma ^ 2, sq_nonneg sigma⟩)) :
    let Xbar : Ω → ℝ :=
      fun ω ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω
    let sigmaHatSq : Ω → ℝ :=
      fun ω ↦
        (n : ℝ)⁻¹ *
          ∑ i : Fin n, (X i ω - Xbar ω) ^ 2
    let sampleVar : Ω → ℝ :=
      fun ω ↦
        (((n - 1 : ℕ) : ℝ)⁻¹) *
          ∑ i : Fin n, (X i ω - Xbar ω) ^ 2
    (∫ ω, (sampleVar ω - sigma ^ 2) ^ 2 ∂P) -
        (∫ ω, (sigmaHatSq ω - sigma ^ 2) ^ 2 ∂P)
      =
      (3 * (n : ℝ) - 1) * sigma ^ 4 /
        ((n : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))
```

## multinomial_count_moments

[Full input](multinomial_count_moments/input.lean)

```lean
theorem multinomial_count_moments
    (n k : ℕ) (hk : 1 ≤ k)
    (p : Fin k → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : (∑ a : Fin k, p a) = 1) :
    let count : Fin k → (Fin n → Fin k) → ℕ :=
      fun c x => ∑ t : Fin n, if x t = c then (1 : ℕ) else 0
    let mass : (Fin n → Fin k) → ℝ :=
      fun x => ∏ t : Fin n, p (x t)
    (∀ a : Fin k,
      (∑ x : Fin n → Fin k, mass x * (count a x : ℝ)) =
          (n : ℝ) * p a ∧
      (∑ x : Fin n → Fin k,
        mass x * ((count a x : ℝ) - (n : ℝ) * p a) ^ 2) =
          (n : ℝ) * p a * (1 - p a)) ∧
    (∀ a b : Fin k, a ≠ b →
      (∑ x : Fin n → Fin k,
        mass x *
          (((count a x : ℝ) - (n : ℝ) * p a) *
            ((count b x : ℝ) - (n : ℝ) * p b))) =
          -((n : ℝ) * p a * p b))
```

## ols_estimator_independent_of_residual_variance

[Full input](ols_estimator_independent_of_residual_variance/input.lean)

```lean
theorem ols_estimator_independent_of_residual_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n p : ℕ) (hnp : p < n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (betaStar : Fin p → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (epsilon : Ω → Fin n → ℝ)
    (hgaussian : ∀ a : Fin n → ℝ,
      HasLaw (fun ω ↦ dotProduct a (epsilon ω))
        (gaussianReal 0
          (Real.toNNReal (sigma ^ 2 * dotProduct a a))) P) :
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin p → ℝ := fun ω ↦
      (X.transpose * X)⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    let sigmaHatSq : Ω → ℝ := fun ω ↦
      dotProduct (y ω - X *ᵥ betaHat ω)
          (y ω - X *ᵥ betaHat ω) / ((n - p : ℕ) : ℝ)
    IndepFun betaHat sigmaHatSq P
```

## pca_recovers_isotropic_factor_loading_space

[Full input](pca_recovers_isotropic_factor_loading_space/input.lean)

```lean
theorem pca_recovers_isotropic_factor_loading_space
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d q : ℕ) (hd : 2 ≤ d) (hq₀ : 1 ≤ q) (hqd : q < d)
    (F : Ω → Fin q → ℝ)
    (epsilon : Ω → Fin d → ℝ)
    (hF_L2 : MemLp F 2 P)
    (hε_L2 : MemLp epsilon 2 P)
    (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hFmean : ∫ ω, F ω ∂P = 0)
    (hFcov : ∀ i j, ∫ ω, F ω i * F ω j ∂P =
      if i = j then 1 else 0)
    (hεmean : ∫ ω, epsilon ω ∂P = 0)
    (hεcov : ∀ i j, ∫ ω, epsilon ω i * epsilon ω j ∂P =
      if i = j then sigma ^ 2 else 0)
    (hcross : ∀ i j, ∫ ω, F ω i * epsilon ω j ∂P = 0)
    (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (hLambda : Function.Injective Lambda.mulVec)
    (mu : Fin d → ℝ)
    (u : Fin d → Fin d → ℝ)
    (rho : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (u j) (u k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range u) = ⊤) :
    let X : Ω → Fin d → ℝ := fun ω ↦
      mu + Lambda *ᵥ F ω + epsilon ω
    let Sigma : Matrix (Fin d) (Fin d) ℝ :=
      fun i j ↦ ∫ ω, (X ω - mu) i * (X ω - mu) j ∂P
    (∀ j, Sigma *ᵥ u j = rho j • u j) →
    Antitone rho →
      Submodule.span ℝ
          {w | ∃ j : Fin d, j.val < q ∧ w = u j} =
        Submodule.span ℝ
          (Set.range fun j : Fin q ↦ fun i : Fin d ↦ Lambda i j)
```

## poisson_sum_distribution

[Full input](poisson_sum_distribution/input.lean)

```lean
theorem poisson_sum_distribution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (lambda : Fin n → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (X : Fin n → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_pmf : ∀ i m,
      (P {ω | X i ω = m}).toReal =
        Real.exp (-(lambda i)) * (lambda i) ^ m / (Nat.factorial m : ℝ))
    (k : ℕ) :
    let S : Ω → ℕ := fun ω => ∑ i : Fin n, X i ω
    let Lambda : ℝ := ∑ i : Fin n, lambda i
    (P {ω | S ω = k}).toReal =
      Real.exp (-Lambda) * Lambda ^ k / (Nat.factorial k : ℝ)
```

## power_function_one_sided_gaussian_mean_test

[Full input](power_function_one_sided_gaussian_mean_test/input.lean)

```lean
theorem power_function_one_sided_gaussian_mean_test
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (mean mean₀ c sigma : ℝ) (hsigma : 0 < sigma)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_law : ∀ i,
      IdentDistrib (X i) id P
        (gaussianReal mean ⟨sigma ^ 2, sq_nonneg sigma⟩)) :
    let Xbar : Ω → ℝ :=
      fun ω ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω
    ENNReal.toReal
        (P {ω |
          Real.sqrt (n : ℝ) * (Xbar ω - mean₀) / sigma > c})
      =
      1 -
        cdf (gaussianReal 0 1)
          (c - Real.sqrt (n : ℝ) * (mean - mean₀) / sigma)
```

## ridge_regression_mean_squared_error

[Full input](ridge_regression_mean_squared_error/input.lean)

```lean
theorem ridge_regression_mean_squared_error
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (betaStar : Fin d → ℝ)
    (epsilon : Ω → Fin n → ℝ)
    (hε_L2 : MemLp epsilon 2 P)
    (sigmaSq : ℝ) (hsigma : 0 ≤ sigmaSq)
    (hmean : ∫ ω, epsilon ω ∂P = 0)
    (hcov : ∀ i j, ∫ ω, epsilon ω i * epsilon ω j ∂P =
      if i = j then sigmaSq else 0)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    let A : Matrix (Fin d) (Fin d) ℝ :=
      X.transpose * X + lambda • 1
    let y : Ω → Fin n → ℝ := fun ω ↦ X *ᵥ betaStar + epsilon ω
    let betaHat : Ω → Fin d → ℝ := fun ω ↦
      A⁻¹ *ᵥ (X.transpose *ᵥ y ω)
    ∫ ω, dotProduct (betaHat ω - betaStar)
        (betaHat ω - betaStar) ∂P =
      lambda ^ 2 *
          dotProduct (A⁻¹ *ᵥ betaStar) (A⁻¹ *ᵥ betaStar) +
        sigmaSq * (A⁻¹ * X.transpose * X * A⁻¹).trace
```

## sample_covariance_unbiased

[Full input](sample_covariance_unbiased/input.lean)

```lean
theorem sample_covariance_unbiased
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (X : Fin n → Ω → Fin d → ℝ)
    (hX_meas : ∀ i a, Measurable (fun ω => X i ω a))
    (hX_memLp : ∀ i a, MemLp (fun ω => X i ω a) 2 P)
    (mu : Fin d → ℝ)
    (hmean : ∀ i a, (∫ ω, X i ω a ∂P) = mu a)
    (Sigma : Matrix (Fin d) (Fin d) ℝ)
    (hSigma : ∀ i a b,
      Sigma a b =
        ∫ ω, (X i ω a - mu a) * (X i ω b - mu b) ∂P)
    (h_cross_zero : ∀ i j a b, i ≠ j →
      (∫ ω, (X i ω a - mu a) * (X j ω b - mu b) ∂P) = 0) :
    let barX : Fin d → Ω → ℝ :=
      fun a ω => (1 / (n : ℝ)) * ∑ i : Fin n, X i ω a
    let S : Fin d → Fin d → Ω → ℝ :=
      fun a b ω => (1 / ((n - 1 : ℕ) : ℝ)) *
        ∑ i : Fin n, (X i ω a - barX a ω) * (X i ω b - barX b ω)
    ∀ a b : Fin d,
      (∫ ω, S a b ω ∂P) = Sigma a b
```

## sequential_brier_risk_decomposition

[Full input](sequential_brier_risk_decomposition/input.lean)

```lean
theorem sequential_brier_risk_decomposition
    {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (hT : 1 ≤ T)
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltration : ∀ s t, s ≤ t → t ≤ T →
      filtration s ≤ filtration t)
    (hsub : ∀ t ≤ T, filtration t ≤ m)
    (Y p q : ℕ → Ω → ℝ)
    (hYmeas : ∀ t, 1 ≤ t → t ≤ T →
      StronglyMeasurable[filtration t] (Y t))
    (hYzeroOne : ∀ t, 1 ≤ t → t ≤ T →
      ∀ ω, Y t ω = 0 ∨ Y t ω = 1)
    (hYint : ∀ t, 1 ≤ t → t ≤ T → Integrable (Y t) P)
    (hqmeas : ∀ t, 1 ≤ t → t ≤ T →
      StronglyMeasurable[filtration (t - 1)] (q t))
    (hqint : ∀ t, 1 ≤ t → t ≤ T → Integrable (q t) P)
    (hp : ∀ t, 1 ≤ t → t ≤ T →
      p t =ᵐ[P] condExp (filtration (t - 1)) P (Y t))
    (hqbounds : ∀ t, 1 ≤ t → t ≤ T →
      ∀ᵐ ω ∂P, 0 ≤ q t ω ∧ q t ω ≤ 1) :
    ∫ ω, ∑ t ∈ Finset.Icc 1 T, (Y t ω - q t ω) ^ 2 ∂P =
      ∫ ω, ∑ t ∈ Finset.Icc 1 T, (Y t ω - p t ω) ^ 2 ∂P +
        ∫ ω, ∑ t ∈ Finset.Icc 1 T, (q t ω - p t ω) ^ 2 ∂P
```

## strict_convexity_of_logistic_loss

[Full input](strict_convexity_of_logistic_loss/input.lean)

```lean
theorem strict_convexity_of_logistic_loss
    (n p : ℕ) (hnp : p ≤ n) (hp : 1 ≤ p)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : Function.Injective X.mulVec)
    (y : Fin n → Bool) :
    let L : (Fin p → ℝ) → ℝ := fun beta ↦
      ∑ i, (Real.log (1 + Real.exp (dotProduct (X i) beta)) -
        (if y i then 1 else 0 : ℝ) * dotProduct (X i) beta)
    ∀ beta gamma : Fin p → ℝ, beta ≠ gamma →
      ∀ t : ℝ, 0 < t → t < 1 →
        L (t • beta + (1 - t) • gamma) <
          t * L beta + (1 - t) * L gamma
```

## studentized_central_limit_theorem

[Full input](studentized_central_limit_theorem/input.lean)

```lean
theorem studentized_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (mean sigma : ℝ)
    (G : Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = mean)
    (hvar : variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma)
    (hG_meas : Measurable G)
    (hG_law : IdentDistrib G id P (gaussianReal 0 1)) :
    let Xbar : ℕ → Ω → ℝ :=
      fun n ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω
    let S : ℕ → Ω → ℝ :=
      fun n ω ↦
        Real.sqrt
          ((n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, (X i ω - Xbar n ω) ^ 2)
    let T : ℕ → Ω → ℝ :=
      fun n ω ↦
        if 0 < S n ω then
          Real.sqrt (n : ℝ) * (Xbar n ω - mean) / S n ω
        else 0
    TendstoInDistribution T atTop G P
```

## tikhonov_risk_bound_functional_linear_regression

[Full input](tikhonov_risk_bound_functional_linear_regression/input.lean)

```lean
theorem tikhonov_risk_bound_functional_linear_regression
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → H) (Y : Ω → ℝ)
    (hXmeas : StronglyMeasurable X)
    (hYmeas : StronglyMeasurable Y)
    (hXsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    (hYsq : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    (C : H →L[ℝ] H)
    (hC : ∀ h, C h = ∫ ω, (inner ℝ (X ω) h) • X ω ∂P)
    (alpha : ℝ) (halpha : 0 < alpha)
    (Ainv : H →L[ℝ] H)
    (hleft : Ainv.comp
        (C + alpha • ContinuousLinearMap.id ℝ H) =
      ContinuousLinearMap.id ℝ H)
    (hright : (C + alpha • ContinuousLinearMap.id ℝ H).comp Ainv =
      ContinuousLinearMap.id ℝ H) :
    let g : H := ∫ ω, (Y ω) • X ω ∂P
    let Q : H → ℝ := fun b ↦
      (∫ ω, (Y ω - inner ℝ (X ω) b) ^ 2 ∂P) +
        alpha * ‖b‖ ^ 2
    let bAlpha := Ainv g
    ∀ b, Q b ≥ Q bAlpha + alpha * ‖b - bAlpha‖ ^ 2
```

## two_sample_ks_distribution_freeness

[Full input](two_sample_ks_distribution_freeness/input.lean)

```lean
theorem two_sample_ks_distribution_freeness
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (F : StieltjesFunction ℝ)
    (hF_cont : Continuous F)
    (hF_strict : StrictMono F)
    (hF_bot : Tendsto F Filter.atBot (nhds 0))
    (hF_top : Tendsto F Filter.atTop (nhds 1))
    (X : Fin m → Ω → ℝ) (Y : Fin n → Ω → ℝ)
    (U : Fin m → Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ j, Measurable (Y j))
    (hU_meas : ∀ i, Measurable (U i))
    (hV_meas : ∀ j, Measurable (V j))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hU_indep : iIndepFun U P)
    (hV_indep : iIndepFun V P)
    (hXY_indep : IndepFun
      (fun ω ↦ fun i ↦ X i ω) (fun ω ↦ fun j ↦ Y j ω) P)
    (hUV_indep : IndepFun
      (fun ω ↦ fun i ↦ U i ω) (fun ω ↦ fun j ↦ V j ω) P)
    (hXY_UV_indep : IndepFun
      (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω))
      (fun ω ↦ (fun i ↦ U i ω, fun j ↦ V j ω)) P)
    (hX_cdf : ∀ i t, (P {ω | X i ω ≤ t}).toReal = F t)
    (hY_cdf : ∀ j t, (P {ω | Y j ω ≤ t}).toReal = F t)
    (hU_uniform : ∀ i, MeasureTheory.pdf.IsUniform (U i) (Set.Ioo 0 1) P)
    (hV_uniform : ∀ j, MeasureTheory.pdf.IsUniform (V j) (Set.Ioo 0 1) P) :
    let FX : Ω → ℝ → ℝ := fun ω t ↦
      (m : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then 1 else 0
    let FY : Ω → ℝ → ℝ := fun ω t ↦
      (n : ℝ)⁻¹ * ∑ j, if Y j ω ≤ t then 1 else 0
    let FU : Ω → ℝ → ℝ := fun ω u ↦
      (m : ℝ)⁻¹ * ∑ i, if U i ω ≤ u then 1 else 0
    let FV : Ω → ℝ → ℝ := fun ω u ↦
      (n : ℝ)⁻¹ * ∑ j, if V j ω ≤ u then 1 else 0
    let DXY : Ω → ℝ := fun ω ↦ ⨆ t : ℝ, |FX ω t - FY ω t|
    let DUV : Ω → ℝ := fun ω ↦
      ⨆ u : Set.Icc (0 : ℝ) 1, |FU ω u.1 - FV ω u.1|
    IdentDistrib DXY DUV P P
```

## two_sample_multivariate_central_limit_theorem

[Full input](two_sample_multivariate_central_limit_theorem/input.lean)

```lean
theorem two_sample_multivariate_central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (hd : 1 ≤ d)
    (X Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (G : Ω → EuclideanSpace ℝ (Fin d))
    (cov : Matrix (Fin d) (Fin d) ℝ)
    (m n : ℕ → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_indep : iIndepFun X P)
    (hY_indep : iIndepFun Y P)
    (hXY_indep :
      IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hY_ident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hXY_ident : IdentDistrib (X 0) (Y 0) P P)
    (hX_second : Integrable (fun ω ↦ ‖X 0 ω‖ ^ 2) P)
    (hX_cov : ∀ j k,
      ∫ ω,
          (X 0 ω j - (∫ ω, X 0 ω ∂P) j) *
            (X 0 ω k - (∫ ω, X 0 ω ∂P) k) ∂P =
        cov j k)
    (hG_meas : Measurable G)
    (hG_gaussian : IsGaussian (P.map G))
    (hG_mean : ∫ ω, G ω ∂P = 0)
    (hG_cov : ∀ j k, ∫ ω, G ω j * G ω k ∂P = cov j k)
    (hm_pos : ∀ r, 0 < m r)
    (hn_pos : ∀ r, 0 < n r)
    (hm_lim : Tendsto m atTop atTop)
    (hn_lim : Tendsto n atTop atTop) :
    TendstoInDistribution
      (fun r ω ↦
        Real.sqrt
            (((m r : ℝ) * (n r : ℝ)) /
              ((m r : ℝ) + (n r : ℝ))) •
          (((m r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (m r), X i ω -
            ((n r : ℝ)⁻¹) •
              ∑ i ∈ Finset.range (n r), Y i ω))
      atTop G P
```

## unbiasedness_and_mse_poisson_estimator

[Full input](unbiasedness_and_mse_poisson_estimator/input.lean)

```lean
theorem unbiasedness_and_mse_poisson_estimator
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (theta a : ℝ) (htheta : 0 < theta) (ha : 0 < a)
    (X : ℕ → Ω → ℕ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (n : ℕ) (hn : a < (n : ℝ)) :
    let rate : NNReal := ⟨theta, htheta.le⟩
    (∀ i, IdentDistrib (X i) id P (poissonMeasure rate)) →
    let S : Ω → ℕ :=
      fun ω ↦ ∑ i ∈ Finset.range n, X i ω
    let T : Ω → ℝ :=
      fun ω ↦ (1 - a / (n : ℝ)) ^ S ω
    (∫ ω, T ω ∂P = Real.exp (-a * theta)) ∧
      (∫ ω, (T ω - Real.exp (-a * theta)) ^ 2 ∂P) =
        Real.exp (-2 * a * theta) *
          (Real.exp (a ^ 2 * theta / (n : ℝ)) - 1)
```

## uniform_endpoint_mle_limit

[Full input](uniform_endpoint_mle_limit/input.lean)

```lean
theorem uniform_endpoint_mle_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ℝ) (hθ : 0 < θ)
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_uniform : ∀ i, MeasureTheory.pdf.IsUniform (X i) (Set.Ioo 0 θ) P)
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (hZ_law : HasLaw Z (expMeasure θ⁻¹) P) :
    let M : ℕ → Ω → ℝ := fun r ω ↦
      (Finset.univ : Finset (Fin (r + 1))).sup'
        Finset.univ_nonempty (fun i ↦ X i.1 ω)
    TendstoInDistribution
      (fun r ω ↦ ((r + 1 : ℕ) : ℝ) * (θ - M r ω))
      atTop Z P
```

## uniform_quantile_convergence

[Full input](uniform_quantile_convergence/input.lean)

```lean
theorem uniform_quantile_convergence
    {U : Type*} [Nonempty U]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (F : U → StieltjesFunction ℝ)
    (Fr : ℕ → U → StieltjesFunction ℝ)
    (hF_bot : ∀ u, Tendsto (F u) atBot (nhds 0))
    (hF_top : ∀ u, Tendsto (F u) atTop (nhds 1))
    (hFr_bot : ∀ r u, Tendsto (Fr r u) atBot (nhds 0))
    (hFr_top : ∀ r u, Tendsto (Fr r u) atTop (nhds 1))
    (hunif : Tendsto
      (fun r ↦ ⨆ u : U, ⨆ x : ℝ, |Fr r u x - F u x|)
      atTop (nhds 0)) :
    let q : U → ℝ := fun u ↦ sInf {x : ℝ | p ≤ F u x}
    let qr : ℕ → U → ℝ := fun r u ↦ sInf {x : ℝ | p ≤ Fr r u x}
    (∀ δ : ℝ, 0 < δ → ∃ eta : ℝ, 0 < eta ∧
      ∀ u, F u (q u - δ) ≤ p - eta ∧ p + eta ≤ F u (q u + δ)) →
      Tendsto (fun r ↦ ⨆ u : U, |qr r u - q u|) atTop (nhds 0)
```

## unique_optimal_pca_projection

[Full input](unique_optimal_pca_projection/input.lean)

```lean
theorem unique_optimal_pca_projection
    (n d r : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hr₀ : 1 ≤ r) (hrd : r < d)
    (x : Fin n → Fin d → ℝ)
    (hcenter : ∑ i, x i = 0)
    (v : Fin d → Fin d → ℝ)
    (lambda : Fin d → ℝ)
    (horth : ∀ j k, dotProduct (v j) (v k) = if j = k then 1 else 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    let S : Matrix (Fin d) (Fin d) ℝ :=
      (n : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (x i)
    let Pᵣ : Matrix (Fin d) (Fin d) ℝ :=
      ∑ j with j.val < r, vecMulVec (v j) (v j)
    (∀ j, S *ᵥ v j = lambda j • v j) →
    Antitone lambda →
    (∀ i j, i.val < r → r ≤ j.val → lambda i > lambda j) →
      let projections : Set (Matrix (Fin d) (Fin d) ℝ) :=
        {P | P.transpose = P ∧ P * P = P ∧ P.trace = (r : ℝ)}
      let objective : Matrix (Fin d) (Fin d) ℝ → ℝ := fun P ↦
        (n : ℝ)⁻¹ *
          ∑ i, dotProduct (x i - P *ᵥ x i) (x i - P *ᵥ x i)
      {P | P ∈ projections ∧
        ∀ Q ∈ projections, objective P ≤ objective Q} = {Pᵣ}
```

## wilcoxon_rank_sum_mean_variance

[Full input](wilcoxon_rank_sum_mean_variance/input.lean)

```lean
theorem wilcoxon_rank_sum_mean_variance
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let N : ℕ := m + n
    let samples : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun A => A.card = m)
    let rank : Fin N → ℝ := fun r => ((r.val + 1 : ℕ) : ℝ)
    let W : Finset (Fin N) → ℝ := fun A => A.sum (fun r => rank r)
    let mean : ℝ := (1 / (samples.card : ℝ)) * samples.sum (fun A => W A)
    let variance : ℝ :=
      (1 / (samples.card : ℝ)) * samples.sum (fun A => (W A - mean) ^ 2)
    mean = (m : ℝ) * ((N : ℝ) + 1) / 2 ∧
      variance = (m : ℝ) * (n : ℝ) * ((N : ℝ) + 1) / 12
```
