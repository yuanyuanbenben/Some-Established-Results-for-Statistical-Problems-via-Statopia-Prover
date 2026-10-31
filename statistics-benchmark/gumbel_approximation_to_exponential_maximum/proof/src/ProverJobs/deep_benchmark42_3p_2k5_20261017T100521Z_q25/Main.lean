import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q25.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators

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
:= by
  /- @proof-region region.root.c0860c9fd2fa begin -/
  dsimp only
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hposn : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have key : ∀ x : ℝ,
      |ENNReal.toReal
          (P {ω | Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => X i ω)
                - Real.log (n : ℝ) ≤ x})
        - Real.exp (-Real.exp (-x))| ≤ 1 / (n : ℝ) := by
    intro x
    have hx := statopia_math_node_976089888_701980f3 P n hn X hX_meas hX_indep hX_law x
    rw [hx]
    set a : ℝ := Real.exp (-x) with ha
    have ha_nn : 0 ≤ a := le_of_lt (Real.exp_pos (-x))
    by_cases hle : a ≤ (n : ℝ)
    · have h1 : 0 ≤ 1 - a / (n : ℝ) := by
        rw [sub_nonneg, div_le_one hn_pos]
        exact hle
      have hmax : max 0 (1 - a / (n : ℝ)) = 1 - a / (n : ℝ) :=
        le_antisymm (by simp [h1]) (by simp)
      rw [hmax]
      have hlow : (1 - a / (n : ℝ)) ^ n ≤ Real.exp (-a) := by
        have hstep : 1 - a / (n : ℝ) ≤ Real.exp (-(a / (n : ℝ))) := by
          have hh := Real.add_one_le_exp (-(a / (n : ℝ)))
          linarith
        have hpow := pow_le_pow_left₀ h1 hstep n
        have hexp : (Real.exp (-(a / (n : ℝ)))) ^ n = Real.exp (-a) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
        rw [hexp] at hpow
        exact hpow
      have hup : Real.exp (-a) - (1 - a / (n : ℝ)) ^ n ≤ 1 / (n : ℝ) :=
        statopia_math_node_493757669_8e9c5e2f n hn a ha_nn hle
      rw [abs_le]
      constructor <;> linarith [hposn]
    · have h1 : 1 - a / (n : ℝ) ≤ 0 := by
        rw [sub_nonpos, one_le_div hn_pos]
        exact le_of_lt (not_le.mp hle)
      have hmax : max 0 (1 - a / (n : ℝ)) = 0 :=
        le_antisymm (by simp [h1]) (by simp)
      rw [hmax, zero_pow (by omega : n ≠ 0)]
      have hgn : Real.exp (-a) ≤ 1 / (n : ℝ) := by
        have h1a : Real.exp (-a) ≤ Real.exp (-(n : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp (-(n : ℝ)) ≤ 1 / (n : ℝ) := by
          rw [Real.exp_neg, ← one_div]
          exact one_div_le_one_div_of_le hn_pos (by linarith [Real.add_one_le_exp (n : ℝ)])
        linarith
      have hep : 0 < Real.exp (-a) := Real.exp_pos (-a)
      rw [abs_le]
      constructor <;> linarith
  refine csSup_le ⟨_, Set.mem_range_self (0 : ℝ)⟩ ?_
  rintro y ⟨x, hx⟩
  rw [← hx]
  exact key x
  /- @proof-region region.root.c0860c9fd2fa end -/
