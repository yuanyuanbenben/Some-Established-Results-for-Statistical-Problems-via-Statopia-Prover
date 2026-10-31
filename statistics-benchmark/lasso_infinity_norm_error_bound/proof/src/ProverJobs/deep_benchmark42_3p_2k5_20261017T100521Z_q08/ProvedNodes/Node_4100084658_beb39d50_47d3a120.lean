import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q08.Base

open MeasureTheory Matrix ProbabilityTheory

open MeasureTheory Matrix ProbabilityTheory

set_option autoImplicit false in
theorem statopia_math_node_4100084658_beb39d50 : ∀ (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (sigma gamma : ℝ) (hsigma : 0 < sigma) (hgamma : 0 < gamma)
    (X : Matrix (Fin n) (Fin d) ℝ) (thetaStar : Fin d → ℝ),
    let lam := 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let cc := 6 * sigma / gamma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    let F : (Fin n → ℝ) → (Fin d → ℝ) → ℝ := fun z theta =>
      (∑ i, (X *ᵥ thetaStar + z - X *ᵥ theta) i ^ 2) / (2 * (n : ℝ)) +
        lam * ∑ j, |theta j|
    let phi := TopologicalSpace.denseSeq (Fin d → ℝ)
    let M : (Fin n → ℝ) → ℝ := fun z => ⨅ m : ℕ, F z (phi m)
    {z : Fin n → ℝ |
        ∀ theta : Fin d → ℝ,
          (∀ eta : Fin d → ℝ, F z theta ≤ F z eta) →
            (⨆ j, |(theta - thetaStar) j|) ≤ cc}
      = (⋃ (ε : ℚ), ⋂ k : ℕ, ⋃ m : ℕ,
          {z : Fin n → ℝ |
            (0 : ℝ) < (ε : ℝ) ∧
              cc + (ε : ℝ) ≤ (⨆ j, |(phi m - thetaStar) j|) ∧
                F z (phi m) < M z + 1 / ((k : ℝ) + 1)})ᶜ := by
  /- @proof-region region.target-node.session.9cb3d4683df6aef2 begin -/
  intro n d hn hd sigma gamma hsigma hgamma X thetaStar lam cc F phi M
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdgt : (1 : ℝ) < (d : ℝ) := by linarith
  have hlog : 0 < Real.log (d : ℝ) / (n : ℝ) := div_pos (Real.log_pos hdgt) hnpos
  have hsqrt : 0 < Real.sqrt (Real.log (d : ℝ) / (n : ℝ)) := Real.sqrt_pos.2 hlog
  have hlam : 0 < lam := by
    show 0 < 4 * sigma * Real.sqrt (Real.log (d : ℝ) / (n : ℝ))
    exact mul_pos (by positivity) hsqrt
  have hphi_dense : DenseRange phi := TopologicalSpace.denseRange_denseSeq (Fin d → ℝ)
  have hFcont : ∀ z : Fin n → ℝ, Continuous (fun theta : Fin d → ℝ => F z theta) := by
    intro z
    fun_prop
  have hcoer : ∀ (z : Fin n → ℝ) (theta : Fin d → ℝ), lam * (∑ j, |theta j|) ≤ F z theta := by
    intro z theta
    show lam * (∑ j, |theta j|) ≤
      (∑ i, (X *ᵥ thetaStar + z - X *ᵥ theta) i ^ 2) / (2 * (n : ℝ)) + lam * ∑ j, |theta j|
    have hden : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have hq : 0 ≤ (∑ i, (X *ᵥ thetaStar + z - X *ᵥ theta) i ^ 2) / (2 * (n : ℝ)) := by
      exact div_nonneg (by positivity) hden.le
    linarith
  have hFnn : ∀ (z : Fin n → ℝ) (theta : Fin d → ℝ), 0 ≤ F z theta := by
    intro z theta
    have h2 : (0 : ℝ) ≤ ∑ j, |theta j| := by positivity
    have h1 : 0 ≤ lam * (∑ j, |theta j|) := mul_nonneg hlam.le h2
    linarith [hcoer z theta]
  have hbdd : ∀ z : Fin n → ℝ, BddBelow (Set.range (fun m : ℕ => F z (phi m))) := by
    intro z
    exact ⟨0, by rintro _ ⟨m, rfl⟩; exact hFnn z (phi m)⟩
  have hMle : ∀ (z : Fin n → ℝ) (theta : Fin d → ℝ), M z ≤ F z theta := by
    intro z theta
    show (⨅ m : ℕ, F z (phi m)) ≤ F z theta
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hlt : F z theta < F z theta + δ := by linarith
    have hmem : {x : Fin d → ℝ | F z x < F z theta + δ} ∈ nhds theta :=
      (hFcont z).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
    obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.mem_nhds_iff.1 hmem
    obtain ⟨m, hm⟩ := hphi_dense.exists_dist_lt theta hδ'pos
    have hfm : F z (phi m) < F z theta + δ :=
      hδ' (Metric.mem_ball.mpr (by rwa [dist_comm] at hm))
    have h1 : (⨅ m : ℕ, F z (phi m)) ≤ F z (phi m) := ciInf_le (hbdd z) m
    linarith
  haveI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hd⟩⟩
  have hbddAbs : ∀ x : Fin d → ℝ, BddAbove (Set.range (fun j : Fin d => |x j|)) := by
    intro x
    refine ⟨∑ j, |x j|, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact Finset.single_le_sum (fun i _ => abs_nonneg (x i)) (Finset.mem_univ j)
  have hleSup : ∀ (x : Fin d → ℝ) (j : Fin d), |x j| ≤ ⨆ j, |x j| :=
    fun x j => le_ciSup (hbddAbs x) j
  have hsupLe : ∀ (x : Fin d → ℝ) (t : ℝ), (∀ j, |x j| ≤ t) → (⨆ j, |x j|) ≤ t :=
    fun x t h => ciSup_le h
  have hsupExists : ∀ (x : Fin d → ℝ) (t : ℝ), t < (⨆ j, |x j|) → ∃ j : Fin d, t < |x j| := by
    intro x t ht
    by_contra h
    push_neg at h
    exact absurd (hsupLe x t h) (not_le.2 ht)
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · intro hZ hS
    obtain ⟨ε, hε⟩ := hS
    obtain ⟨m0, hm0pos, _, _⟩ := hε 0
    have hεpos : (0 : ℝ) < (ε : ℝ) := hm0pos
    set R : ℝ := (M z + 1) / lam with hRdef
    set A : Set (Fin d → ℝ) :=
      ⋃ j : Fin d, ({theta : Fin d → ℝ | F z theta ≤ M z + 1} ∩
        {theta : Fin d → ℝ | cc + (ε : ℝ) / 2 ≤ |(theta - thetaStar) j|}) with hAdef
    have hpiece_closed : ∀ j : Fin d, IsClosed
        ({theta : Fin d → ℝ | F z theta ≤ M z + 1} ∩
          {theta : Fin d → ℝ | cc + (ε : ℝ) / 2 ≤ |(theta - thetaStar) j|}) := by
      intro j
      exact IsClosed.inter (isClosed_le (hFcont z) continuous_const)
        (isClosed_le continuous_const (by fun_prop))
    have hAclosed : IsClosed A := by
      rw [hAdef]
      exact isClosed_iUnion_of_finite hpiece_closed
    have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hAsub : A ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R) := by
      intro theta htheta
      rw [hAdef] at htheta
      obtain ⟨j, hthetaJ⟩ := Set.mem_iUnion.1 htheta
      have hFle : F z theta ≤ M z + 1 := hthetaJ.1
      rw [Set.mem_pi]
      intro j' _
      exact abs_le.1 (by
        have hS_le : ∑ i, |theta i| ≤ R := by
          rw [hRdef, le_div_iff₀ hlam, mul_comm]
          linarith [hcoer z theta, hFle]
        calc |theta j'| ≤ ∑ i, |theta i| :=
              Finset.single_le_sum (fun i _ => abs_nonneg (theta i)) (Finset.mem_univ j')
          _ ≤ R := hS_le)
    have hAcompact : IsCompact A := hbox.of_isClosed_subset hAclosed hAsub
    have hseq : ∀ k : ℕ, ∃ m : ℕ, cc + (ε : ℝ) ≤ ⨆ j, |(phi m - thetaStar) j| ∧
        F z (phi m) < M z + 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨m, _, hD, hF⟩ := hε k
      exact ⟨m, hD, hF⟩
    let mm : ℕ → ℕ := fun k => Classical.choose (hseq k)
    have hmm : ∀ k : ℕ, cc + (ε : ℝ) ≤ ⨆ j, |(phi (mm k) - thetaStar) j| ∧
        F z (phi (mm k)) < M z + 1 / ((k : ℝ) + 1) :=
      fun k => Classical.choose_spec (hseq k)
    have hmemA_of : ∀ k : ℕ, phi (mm k) ∈ A := by
      intro k
      have hlt : cc + (ε : ℝ) / 2 < ⨆ j, |(phi (mm k) - thetaStar) j| := by
        linarith [(hmm k).1, hεpos]
      obtain ⟨j, hj⟩ := hsupExists (phi (mm k) - thetaStar) (cc + (ε : ℝ) / 2) hlt
      have hFle : F z (phi (mm k)) ≤ M z + 1 := by
        have hq_le : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
          linarith
        linarith [(hmm k).2]
      rw [hAdef]
      exact Set.mem_iUnion.2 ⟨j, hFle, hj.le⟩
    have hAne : A.Nonempty := ⟨phi (mm 0), hmemA_of 0⟩
    obtain ⟨theta0, htheta0A, hminA⟩ :=
      hAcompact.exists_isMinOn hAne (hFcont z).continuousOn
    have hFmin_le : F z theta0 ≤ M z := by
      refine le_of_forall_pos_le_add (fun δ hδ => ?_)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      have h1 : F z theta0 ≤ F z (phi (mm k)) := hminA (hmemA_of k)
      have h3 : (1 : ℝ) / ((k : ℝ) + 1) ≤ δ := le_of_lt hk
      linarith [(hmm k).2]
    have hminim : ∀ eta : Fin d → ℝ, F z theta0 ≤ F z eta :=
      fun eta => le_trans hFmin_le (hMle z eta)
    have hcontra : cc + (ε : ℝ) / 2 ≤ cc := by
      have hD0 : cc + (ε : ℝ) / 2 ≤ ⨆ j, |(theta0 - thetaStar) j| := by
        rw [hAdef] at htheta0A
        obtain ⟨j, hjint⟩ := Set.mem_iUnion.1 htheta0A
        exact le_trans hjint.2 (hleSup (theta0 - thetaStar) j)
      exact le_trans hD0 (hZ theta0 hminim)
    linarith [hεpos]
  · intro hS theta hmin
    have hFeq : F z theta = M z := by
      apply le_antisymm
      · show F z theta ≤ ⨅ m : ℕ, F z (phi m)
        exact le_ciInf (fun m => hmin (phi m))
      · exact hMle z theta
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨j0, hj0⟩ := hsupExists (theta - thetaStar) cc hcon
    have hcoord : Continuous (fun x : Fin d → ℝ => |(x - thetaStar) j0|) := by fun_prop
    obtain ⟨q, hq0, hqd⟩ :=
      exists_rat_btwn (show (0 : ℝ) < |(theta - thetaStar) j0| - cc by linarith)
    refine hS ⟨q, fun k => ?_⟩
    have hltD : cc + (q : ℝ) < |(theta - thetaStar) j0| := by linarith
    have hmemD : {x : Fin d → ℝ | cc + (q : ℝ) < |(x - thetaStar) j0|} ∈ nhds theta :=
      hcoord.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hltD)
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hltF : F z theta < M z + 1 / ((k : ℝ) + 1) := by
      rw [hFeq]; linarith
    have hmemF : {x : Fin d → ℝ | F z x < M z + 1 / ((k : ℝ) + 1)} ∈ nhds theta :=
      (hFcont z).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hltF)
    obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.mem_nhds_iff.1 hmemD
    obtain ⟨δ2, hδ2pos, hδ2⟩ := Metric.mem_nhds_iff.1 hmemF
    obtain ⟨m, hm⟩ := hphi_dense.exists_dist_lt theta (lt_min hδ1pos hδ2pos)
    have hmball1 : phi m ∈ Metric.ball theta δ1 :=
      Metric.mem_ball.mpr (by rw [dist_comm]; exact lt_of_lt_of_le hm (min_le_left _ _))
    have hmball2 : phi m ∈ Metric.ball theta δ2 :=
      Metric.mem_ball.mpr (by rw [dist_comm]; exact lt_of_lt_of_le hm (min_le_right _ _))
    exact ⟨m, hq0, le_of_lt (lt_of_lt_of_le (hδ1 hmball1) (hleSup (phi m - thetaStar) j0)), hδ2 hmball2⟩
  /- @proof-region region.target-node.session.9cb3d4683df6aef2 end -/
