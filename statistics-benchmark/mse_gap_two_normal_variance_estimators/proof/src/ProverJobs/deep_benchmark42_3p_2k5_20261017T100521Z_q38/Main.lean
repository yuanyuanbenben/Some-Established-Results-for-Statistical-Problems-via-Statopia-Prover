import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q38.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

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
:= by
  /- @proof-region region.root.0b0df355fdd9 begin -/
  dsimp only
  have hn1 : 1 ≤ n := by omega
  have hN0 : (n : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < n := by omega
    exact_mod_cast h.ne'
  have hN1 : (n : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  let Z : Fin n → Ω → ℝ := fun i ω => X i ω - mean
  let A : Fin n → Fin n → ℝ := fun i j => (if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹
  let Q : Ω → ℝ := fun ω => ∑ i : Fin n, ∑ j : Fin n, A i j * Z i ω * Z j ω
  have hXlaw : ∀ i, P.map (X i) = gaussianReal mean ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
    intro i
    simpa using (hX_law i).map_eq
  have hZfacts := statopia_math_node_2382897187_683a51f9 P n mean (sigma ^ 2) (sq_nonneg sigma) X hX_meas hX_indep hXlaw
  have hZmeas : ∀ i, Measurable (Z i) := hZfacts.1
  have hZindep : iIndepFun Z P := hZfacts.2.1
  have hZlaw : ∀ i, P.map (Z i) = gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩ := hZfacts.2.2
  have hAsymm : ∀ i j, A i j = A j i := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · show (if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹ = (if j = i then (1 : ℝ) else 0) - (n : ℝ)⁻¹
      rw [if_neg h, if_neg (fun hji : j = i => h hji.symm)]
  have hQfacts := statopia_math_node_32739689_461a334a P n (sigma ^ 2) (sq_nonneg sigma) Z hZmeas hZindep hZlaw A hAsymm
  have hQ2int : Integrable (fun ω => Q ω ^ 2) P := hQfacts.1
  have hQint : Integrable Q P := hQfacts.2.1
  have hQ1 : (∫ ω, Q ω ∂P) = sigma ^ 2 * ∑ i : Fin n, A i i := hQfacts.2.2.1
  have hQ2 : (∫ ω, Q ω ^ 2 ∂P) =
      (sigma ^ 2) ^ 2 * ((∑ i : Fin n, A i i) ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2) :=
    hQfacts.2.2.2
  have hAii : ∑ i : Fin n, A i i = (n : ℝ) - 1 := by
    have hdiag : ∀ i : Fin n, A i i = 1 - (n : ℝ)⁻¹ := by
      intro i
      show (if i = i then (1 : ℝ) else 0) - (n : ℝ)⁻¹ = 1 - (n : ℝ)⁻¹
      rw [if_pos rfl]
    have hsum : ∑ i : Fin n, (1 - (n : ℝ)⁻¹) = (n : ℝ) * (1 - (n : ℝ)⁻¹) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => hdiag i), hsum, mul_sub, mul_one, mul_inv_cancel₀ hN0]
  have hAij2 : ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 = (n : ℝ) - 1 := by
    have hB : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0
    have hsq : ∀ i j : Fin n, (A i j) ^ 2 = (if i = j then (1 - (n : ℝ)⁻¹) ^ 2 else (n : ℝ)⁻¹ ^ 2) := by
      intro i j
      show ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹) ^ 2 =
        (if i = j then (1 - (n : ℝ)⁻¹) ^ 2 else (n : ℝ)⁻¹ ^ 2)
      by_cases h : i = j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; ring
    have hcs : ∀ i : Fin n, ∑ j : Fin n, (if i = j then ((1 - (n : ℝ)⁻¹) ^ 2 - (n : ℝ)⁻¹ ^ 2) else 0)
        = ((1 - (n : ℝ)⁻¹) ^ 2 - (n : ℝ)⁻¹ ^ 2) := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg (fun hib : i = b => hb hib.symm)]
      · intro hmem
        exact absurd (Finset.mem_univ i) hmem
    have hconst : ∑ j : Fin n, (n : ℝ)⁻¹ ^ 2 = (n : ℝ) * (n : ℝ)⁻¹ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hrow : ∀ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 = 1 - 2 * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ ^ 2 := by
      intro i
      have e1 : ∑ j : Fin n, (A i j) ^ 2
          = ∑ j : Fin n, (if i = j then (1 - (n : ℝ)⁻¹) ^ 2 else (n : ℝ)⁻¹ ^ 2) :=
        Finset.sum_congr rfl (fun j _ => hsq i j)
      have e2 : ∑ j : Fin n, (if i = j then (1 - (n : ℝ)⁻¹) ^ 2 else (n : ℝ)⁻¹ ^ 2)
          = ∑ j : Fin n, ((n : ℝ)⁻¹ ^ 2 + (if i = j then ((1 - (n : ℝ)⁻¹) ^ 2 - (n : ℝ)⁻¹ ^ 2) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      have e3 : ∑ j : Fin n, ((n : ℝ)⁻¹ ^ 2 + (if i = j then ((1 - (n : ℝ)⁻¹) ^ 2 - (n : ℝ)⁻¹ ^ 2) else 0))
          = (n : ℝ) * (n : ℝ)⁻¹ ^ 2 + ((1 - (n : ℝ)⁻¹) ^ 2 - (n : ℝ)⁻¹ ^ 2) := by
        rw [Finset.sum_add_distrib, hconst, hcs i]
      rw [e1, e2, e3]
      ring
    have hfin : ∑ i : Fin n, (1 - 2 * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ ^ 2)
        = (n : ℝ) * (1 - 2 * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), hfin]
    have hcalc : (n : ℝ) * (1 - 2 * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ ^ 2) = (n : ℝ) - 1 := by
      have hk : (n : ℝ) * (1 - 2 * (n : ℝ)⁻¹ + (n : ℝ) * (n : ℝ)⁻¹ ^ 2)
          = (n : ℝ) - 2 * ((n : ℝ) * (n : ℝ)⁻¹) + ((n : ℝ) * (n : ℝ)⁻¹) ^ 2 := by ring
      rw [hk, hB]; ring
    rw [hcalc]
  have hSQ : ∀ ω : Ω, (∑ i : Fin n, (X i ω - (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω) ^ 2) = Q ω := by
    intro ω
    exact (statopia_math_node_1006963914_bdbc5482 n hn1 (fun i => X i ω) mean).2.2.2
  have hm1 : (∫ ω, Q ω ∂P) = ((n : ℝ) - 1) * sigma ^ 2 := by
    rw [hQ1, hAii]
    ring
  have hm2 : (∫ ω, Q ω ^ 2 ∂P) = ((n : ℝ) - 1) * ((n : ℝ) + 1) * sigma ^ 4 := by
    rw [hQ2, hAii, hAij2]
    ring
  have hval : ∀ c : ℝ, (∫ ω, (c * Q ω - sigma ^ 2) ^ 2 ∂P) =
      c ^ 2 * (∫ ω, Q ω ^ 2 ∂P) - 2 * c * sigma ^ 2 * (∫ ω, Q ω ∂P) + sigma ^ 4 := by
    intro c
    have h1 : Integrable (fun ω => c ^ 2 * Q ω ^ 2) P := hQ2int.const_mul _
    have h2 : Integrable (fun ω => (2 * c * sigma ^ 2) * Q ω) P := hQint.const_mul _
    have h3 : Integrable (fun _ : Ω => sigma ^ 4) P := integrable_const (sigma ^ 4)
    have key : (fun ω : Ω => (c * Q ω - sigma ^ 2) ^ 2) =
        fun ω => (c ^ 2 * Q ω ^ 2 - (2 * c * sigma ^ 2) * Q ω) + sigma ^ 4 := by
      funext ω
      ring
    rw [key]
    have e1 : (∫ ω, ((c ^ 2 * Q ω ^ 2 - (2 * c * sigma ^ 2) * Q ω) + sigma ^ 4) ∂P)
        = (∫ ω, (c ^ 2 * Q ω ^ 2 - (2 * c * sigma ^ 2) * Q ω) ∂P) + (∫ _ : Ω, sigma ^ 4 ∂P) :=
      integral_add (h1.sub h2) h3
    rw [e1]
    have e2 : (∫ ω, (c ^ 2 * Q ω ^ 2 - (2 * c * sigma ^ 2) * Q ω) ∂P)
        = (∫ ω, c ^ 2 * Q ω ^ 2 ∂P) - (∫ ω, (2 * c * sigma ^ 2) * Q ω ∂P) :=
      integral_sub h1 h2
    rw [e2]
    rw [integral_const_mul, integral_const_mul]
    have h4 : (∫ _ : Ω, sigma ^ 4 ∂P) = sigma ^ 4 := by simp
    rw [h4]
  have hI1 : (∫ ω, ((((n - 1 : ℕ) : ℝ))⁻¹ * (∑ i : Fin n, (X i ω - (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω) ^ 2) - sigma ^ 2) ^ 2 ∂P)
      = (∫ ω, ((((n - 1 : ℕ) : ℝ))⁻¹ * Q ω - sigma ^ 2) ^ 2 ∂P) := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [hSQ ω]
  have hI2 : (∫ ω, ((n : ℝ)⁻¹ * (∑ i : Fin n, (X i ω - (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω) ^ 2) - sigma ^ 2) ^ 2 ∂P)
      = (∫ ω, ((n : ℝ)⁻¹ * Q ω - sigma ^ 2) ^ 2 ∂P) := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [hSQ ω]
  rw [hI1, hI2, hval, hval, hm1, hm2, hcast]
  field_simp
  ring
  /- @proof-region region.root.0b0df355fdd9 end -/
