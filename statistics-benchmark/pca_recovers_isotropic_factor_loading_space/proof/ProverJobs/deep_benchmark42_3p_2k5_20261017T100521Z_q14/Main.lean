import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.ProvedNodes
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

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
:= by
  /- @proof-region region.root.33bc35bef188 begin -/
  intro X S hEig hanti
  let lam : Fin d → ℝ := fun j => rho j - sigma ^ 2
  have hSigma : S = Lambda * Lambda.transpose + sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) :=
    statopia_math_node_1890793592_47ee479f P d q F epsilon hF_L2 hε_L2 sigma hFcov hεcov hcross Lambda mu
  have hmulvec : ∀ x : Fin d → ℝ,
      S *ᵥ x = (Lambda * Lambda.transpose) *ᵥ x + sigma ^ 2 • x := by
    intro x
    have hlin : S.mulVecLin = (Lambda * Lambda.transpose).mulVecLin +
        sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ).mulVecLin := by
      rw [hSigma]
      simp
    have hone : (1 : Matrix (Fin d) (Fin d) ℝ).mulVecLin = LinearMap.id :=
      LinearMap.ext fun y => (Matrix.mulVecLin_apply 1 y).trans (Matrix.one_mulVec y)
    have hx := congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) => f x) hlin
    rw [hone] at hx
    simp only [Matrix.mulVecLin_apply, LinearMap.add_apply, LinearMap.smul_apply] at hx
    exact hx
  have heigM : ∀ j : Fin d, (Lambda * Lambda.transpose) *ᵥ u j = lam j • u j := by
    intro j
    change (Lambda * Lambda.transpose) *ᵥ u j = (rho j - sigma ^ 2) • u j
    rw [sub_smul, eq_sub_iff_add_eq, ← hmulvec]
    exact hEig j
  have hAntiLam : Antitone lam := by
    intro a b hab
    change rho b - sigma ^ 2 ≤ rho a - sigma ^ 2
    exact sub_le_sub_right (hanti hab) (sigma ^ 2)
  have hnonneg : ∀ j : Fin d, 0 ≤ lam j := by
    intro j
    have hv : dotProduct (u j) (u j) = 1 := by simpa using horth j j
    exact (statopia_math_node_422579165_9aacadd7 d q Lambda (u j) (lam j) hv (heigM j)).2
  have hgram := statopia_math_node_2814431898_39cb855d d q Lambda hLambda
  have hrange : LinearMap.range (Lambda * Lambda.transpose).mulVecLin =
      LinearMap.range Lambda.mulVecLin := hgram.1
  have hfinrankM : Module.finrank ℝ
      ↥(LinearMap.range (Lambda * Lambda.transpose).mulVecLin) = q := hgram.2.2
  have hsub := statopia_math_node_856236742_c90712bc d q Lambda lam u hspan heigM
  have hle : LinearMap.range (Lambda * Lambda.transpose).mulVecLin ≤
      Submodule.span ℝ {v : Fin d → ℝ | ∃ j : Fin d, lam j ≠ 0 ∧ v = u j} := by
    rintro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    simpa only [Matrix.mulVecLin_apply] using hsub y
  have hfinrankW : Module.finrank ℝ
        ↥(Submodule.span ℝ {v : Fin d → ℝ | ∃ j : Fin d, lam j ≠ 0 ∧ v = u j}) =
      (Finset.univ.filter (fun j : Fin d => lam j ≠ 0)).card := by
    have hset : {v : Fin d → ℝ | ∃ j : Fin d, lam j ≠ 0 ∧ v = u j} =
        {v : Fin d → ℝ | ∃ j ∈ Finset.univ.filter (fun j : Fin d => lam j ≠ 0), v = u j} := by
      ext v
      simp
    rw [hset]
    exact statopia_math_node_1730365501_588c10f1 d u horth _
  have hcardq : q ≤ (Finset.univ.filter (fun j : Fin d => lam j ≠ 0)).card := by
    have h := Submodule.finrank_mono hle
    rw [hfinrankM, hfinrankW] at h
    exact h
  have hpos : ∀ j : Fin d, j.val < q → 0 < lam j :=
    statopia_math_node_1618166017_efb9b88b d q lam hAntiLam hnonneg hcardq
  have hPle : Submodule.span ℝ {w : Fin d → ℝ | ∃ j : Fin d, j.val < q ∧ w = u j} ≤
      LinearMap.range (Lambda * Lambda.transpose).mulVecLin := by
    rw [Submodule.span_le]
    rintro v ⟨j, hj, rfl⟩
    have hp : lam j ≠ 0 := ne_of_gt (hpos j hj)
    change u j ∈ LinearMap.range (Lambda * Lambda.transpose).mulVecLin
    rw [LinearMap.mem_range]
    refine ⟨(lam j)⁻¹ • u j, ?_⟩
    have h1 : (Lambda * Lambda.transpose).mulVecLin ((lam j)⁻¹ • u j) =
        (lam j)⁻¹ • (Lambda * Lambda.transpose).mulVecLin (u j) := by
      simp
    rw [h1, Matrix.mulVecLin_apply, heigM j, smul_smul, inv_mul_cancel₀ hp, one_smul]
  have hcardP : (Finset.univ.filter (fun j : Fin d => j.val < q)).card = q := by
    have hfil : Finset.univ.filter (fun j : Fin d => j.val < q) =
        Finset.Iio (⟨q, hqd⟩ : Fin d) := by
      ext j
      simp [Fin.lt_def]
    rw [hfil, Fin.card_Iio]
  have hfinrankP : Module.finrank ℝ
        ↥(Submodule.span ℝ {w : Fin d → ℝ | ∃ j : Fin d, j.val < q ∧ w = u j}) = q := by
    have hset : {w : Fin d → ℝ | ∃ j : Fin d, j.val < q ∧ w = u j} =
        {w : Fin d → ℝ | ∃ j ∈ Finset.univ.filter (fun j : Fin d => j.val < q), w = u j} := by
      ext w
      simp
    rw [hset, statopia_math_node_1730365501_588c10f1 d u horth
      (Finset.univ.filter (fun j : Fin d => j.val < q))]
    exact hcardP
  have hPeq : Submodule.span ℝ {w : Fin d → ℝ | ∃ j : Fin d, j.val < q ∧ w = u j} =
      LinearMap.range (Lambda * Lambda.transpose).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hPle (by rw [hfinrankP, hfinrankM])
  have hcol : (Set.range Lambda.col : Set (Fin d → ℝ)) =
      Set.range (fun j : Fin q => fun i : Fin d => Lambda i j) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, by funext i; simp [Matrix.col]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by funext i; simp [Matrix.col]⟩
  have hrangeC : LinearMap.range Lambda.mulVecLin =
      Submodule.span ℝ (Set.range fun j : Fin q => fun i : Fin d => Lambda i j) :=
    (Matrix.range_mulVecLin Lambda).trans (congrArg (Submodule.span ℝ) hcol)
  rw [hPeq, hrange, hrangeC]
  /- @proof-region region.root.33bc35bef188 end -/
