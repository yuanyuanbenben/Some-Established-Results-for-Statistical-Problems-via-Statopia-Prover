import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Vocabulary
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.ProvedNodes
import ProverJobs.job_paper_20b0260ed6f74673a96e9b9321c3333f.Base

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Statlib.Imported

theorem paper_20b0260ed6f74673a96e9b9321c3333f
    {Ω 𝒳 Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace Θ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → 𝒳) (hX : ∀ i, Measurable (X i))
    (hex : ExchangeableSeq X μ)
    (k : Θ → 𝒳 → ℝ) (Q0 : Measure Θ) [IsProbabilityMeasure Q0]
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hmeasPhi : ∀ A : Finset (Fin n),
      AEStronglyMeasurable (fun y : Fin n → 𝒳 => ∫ θ, ∏ i ∈ A, k θ (y i) ∂Q0)
        (Measure.map (fun ω (i : Fin n) => X i.val ω) μ))
    (hLint : Integrable (fun ω => ∑ P ∈ partitionsInto n s,
      ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) /
          ((Nat.factorial (n - 1) : ℕ) : ℝ)) *
        (blockProduct (restrictSeq X n) k Q0 P ω /
          margLikelihood (restrictSeq X n) k Q0 Finset.univ ω)) μ)
    (hRint : ∀ a ∈ orderedCompositions n s, Integrable (fun ω =>
      (∏ j : Fin s, margLikelihood (restrictSeq X n) k Q0 (canonBlock n s a j) ω) /
        margLikelihood (restrictSeq X n) k Q0 Finset.univ ω) μ) :
    (∫ ω, (∑ P ∈ partitionsInto n s,
      ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) /
          ((Nat.factorial (n - 1) : ℕ) : ℝ)) *
        (blockProduct (restrictSeq X n) k Q0 P ω /
          margLikelihood (restrictSeq X n) k Q0 Finset.univ ω)) ∂μ)
    = ∑ a ∈ orderedCompositions n s,
      ((n : ℝ) / (((Nat.factorial s : ℕ) : ℝ) * ∏ j : Fin s, ((a j).val : ℝ))) *
        (∫ ω, ((∏ j : Fin s, margLikelihood (restrictSeq X n) k Q0 (canonBlock n s a j) ω) /
          margLikelihood (restrictSeq X n) k Q0 Finset.univ ω) ∂μ)
:= by
  /- @proof-region region.root.17d0e7815844 begin -/
  classical
  let T : Ω → (Fin n → 𝒳) := fun ω (i : Fin n) => X i.val ω
  let Phi : Finset (Fin n) → (Fin n → 𝒳) → ℝ := fun A y => ∫ θ, ∏ i ∈ A, k θ (y i) ∂Q0
  let O : Finset (Fin s → Finset (Fin n)) :=
    (Finset.univ : Finset (Fin s → Finset (Fin n))).filter
      (fun f => (∀ j : Fin s, (f j).Nonempty) ∧
        (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
        (∀ i : Fin n, ∃ j : Fin s, i ∈ f j))
  let Oa : (Fin s → Fin (n + 1)) → Finset (Fin s → Finset (Fin n)) :=
    fun a => O.filter (fun f => ∀ j : Fin s, (f j).card = (a j).val)
  let ca : (Fin s → Fin (n + 1)) → ℝ :=
    fun a => ∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)
  let D : ℝ := ((Nat.factorial (n - 1) : ℕ) : ℝ)
  let Sf : ℝ := ((Nat.factorial s : ℕ) : ℝ)
  let G : (Fin s → Finset (Fin n)) → Ω → ℝ :=
    fun f ω => (∏ j : Fin s, Phi (f j) (T ω)) / Phi Finset.univ (T ω)
  let Ival : (Fin s → Fin (n + 1)) → ℝ := fun a =>
    ∫ ω, ((∏ j : Fin s, margLikelihood (restrictSeq X n) k Q0 (canonBlock n s a j) ω) /
      margLikelihood (restrictSeq X n) k Q0 Finset.univ ω) ∂μ
  have hpt : ∀ ω : Ω,
      (∑ P ∈ partitionsInto n s,
        ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) / D) *
          (blockProduct (restrictSeq X n) k Q0 P ω /
            margLikelihood (restrictSeq X n) k Q0 Finset.univ ω))
      = (D * Sf)⁻¹ *
        (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) := by
    intro ω
    have hDS : (D * Sf)⁻¹ = D⁻¹ * Sf⁻¹ := by
      have h1 : D ≠ 0 := by
        show ((Nat.factorial (n - 1) : ℕ) : ℝ) ≠ 0
        exact_mod_cast Nat.factorial_ne_zero (n - 1)
      have h2 : Sf ≠ 0 := by
        show ((Nat.factorial s : ℕ) : ℝ) ≠ 0
        exact_mod_cast Nat.factorial_ne_zero s
      field_simp
    have hcA : ∀ (a : Fin s → Fin (n + 1)) (f : Fin s → Finset (Fin n)), f ∈ Oa a →
        (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) = ca a := by
      intro a f hf
      have hfc : ∀ j : Fin s, (f j).card = (a j).val := (Finset.mem_filter.mp hf).2
      show (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ))
        = ∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)
      exact Finset.prod_congr rfl (fun j _ => by rw [hfc j])
    have hY : (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω)
        = (Phi Finset.univ (T ω))⁻¹ *
          (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
            ca a * (∏ j : Fin s, Phi (f j) (T ω))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      show ca a * ((∏ j : Fin s, Phi (f j) (T ω)) / Phi Finset.univ (T ω))
        = (Phi Finset.univ (T ω))⁻¹ * (ca a * (∏ j : Fin s, Phi (f j) (T ω)))
      rw [div_eq_mul_inv]
      ring
    have hOsup : (Finset.univ.filter (fun f : Fin s → Finset (Fin n) =>
              (∀ j : Fin s, (f j).Nonempty) ∧
              (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
              Finset.univ.sup f = Finset.univ)) = O := by
      ext f
      show (f ∈ Finset.univ.filter (fun f : Fin s → Finset (Fin n) =>
              (∀ j : Fin s, (f j).Nonempty) ∧
              (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
              Finset.univ.sup f = Finset.univ))
          ↔ (f ∈ Finset.univ.filter (fun f : Fin s → Finset (Fin n) =>
              (∀ j : Fin s, (f j).Nonempty) ∧
              (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
              (∀ i : Fin n, ∃ j : Fin s, i ∈ f j)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hA, hB, hC⟩
        refine ⟨hA, hB, fun i => ?_⟩
        have hi : i ∈ Finset.univ.sup f := by rw [hC]; exact Finset.mem_univ i
        obtain ⟨j, -, hj⟩ := Finset.mem_sup.mp hi
        exact ⟨j, hj⟩
      · rintro ⟨hA, hB, hC⟩
        refine ⟨hA, hB, ?_⟩
        ext i
        exact ⟨fun _ => Finset.mem_univ i, fun _ => by
          obtain ⟨j, hj⟩ := hC i
          exact Finset.mem_sup.mpr ⟨j, Finset.mem_univ j, hj⟩⟩
    have hsym : (∑ P ∈ partitionsInto n s,
          (∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) * (∏ B ∈ P, Phi B (T ω)))
        = Sf⁻¹ * (∑ f ∈ O, (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
            (∏ j : Fin s, Phi (f j) (T ω))) := by
      have h := statopia_math_node_642534324_01784987 n s hs
        (fun B : Finset (Fin n) => ((Nat.factorial (B.card - 1) : ℕ) : ℝ))
        (fun B : Finset (Fin n) => Phi B (T ω))
      rw [hOsup] at h
      simpa only [one_div] using h
    have hdec : (∑ f ∈ O, (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
            (∏ j : Fin s, Phi (f j) (T ω)))
        = ∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
            (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
              (∏ j : Fin s, Phi (f j) (T ω)) := by
      have h := (statopia_math_node_947343170_012e2f22 n s).2
      exact h ℝ (fun f : Fin s → Finset (Fin n) =>
        (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
          (∏ j : Fin s, Phi (f j) (T ω)))
    have hcsum : (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
          (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
            (∏ j : Fin s, Phi (f j) (T ω)))
        = ∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
            ca a * (∏ j : Fin s, Phi (f j) (T ω)) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro f hf
      rw [hcA a f hf]
    calc (∑ P ∈ partitionsInto n s,
          ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) / D) *
            (blockProduct (restrictSeq X n) k Q0 P ω /
              margLikelihood (restrictSeq X n) k Q0 Finset.univ ω))
        = ∑ P ∈ partitionsInto n s,
            ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) / D) *
              ((∏ B ∈ P, Phi B (T ω)) / Phi Finset.univ (T ω)) := rfl
      _ = (D⁻¹ * (Phi Finset.univ (T ω))⁻¹) *
            (∑ P ∈ partitionsInto n s,
              (∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) *
                (∏ B ∈ P, Phi B (T ω))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro P hP
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = (D⁻¹ * (Phi Finset.univ (T ω))⁻¹) *
            (Sf⁻¹ * (∑ f ∈ O,
              (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
                (∏ j : Fin s, Phi (f j) (T ω)))) := by rw [hsym]
      _ = (D⁻¹ * (Phi Finset.univ (T ω))⁻¹) *
            (Sf⁻¹ * (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
              (∏ j : Fin s, ((Nat.factorial ((f j).card - 1) : ℕ) : ℝ)) *
                (∏ j : Fin s, Phi (f j) (T ω)))) := by rw [hdec]
      _ = (D⁻¹ * (Phi Finset.univ (T ω))⁻¹) *
            (Sf⁻¹ * (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a,
              ca a * (∏ j : Fin s, Phi (f j) (T ω)))) := by rw [hcsum]
      _ = (D * Sf)⁻¹ * (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) := by
          rw [hY, hDS]
          ring
  have hGmain : ∀ a ∈ orderedCompositions n s, ∀ f ∈ Oa a,
      Integrable (G f) μ ∧ (∫ ω, G f ω ∂μ) = Ival a := by
    intro a ha f hf
    have hmem := Finset.mem_filter.mp hf
    have hO := Finset.mem_filter.mp hmem.1
    have hne : ∀ j : Fin s, (f j).Nonempty := hO.2.1
    have hdisj : ∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k) := hO.2.2.1
    have hcover : ∀ i : Fin n, ∃ j : Fin s, i ∈ f j := hO.2.2.2
    have hcard : ∀ j : Fin s, (f j).card = (a j).val := hmem.2
    obtain ⟨σ, hσ⟩ := statopia_math_node_2276611095_99631dac n s a ha f hne hdisj hcover hcard
    let Tσ : Ω → (Fin n → 𝒳) := fun ω (i : Fin n) => X (σ i).val ω
    have hT : Measurable T := measurable_pi_iff.mpr (fun i => hX i.val)
    have hTσ : Measurable Tσ := measurable_pi_iff.mpr (fun i => hX (σ i).val)
    have hpush : Measure.map Tσ μ = Measure.map T μ := hex n σ
    let H : (Fin n → 𝒳) → ℝ :=
      fun y => (∏ j : Fin s, Phi (canonBlock n s a j) y) / Phi Finset.univ y
    have hHmeas : AEStronglyMeasurable H (Measure.map T μ) := by
      have h1 : AEStronglyMeasurable
          (fun y : Fin n → 𝒳 => ∏ j : Fin s, Phi (canonBlock n s a j) y)
          (Measure.map T μ) := by
        have hh : AEStronglyMeasurable
            (∏ j : Fin s, fun (y : Fin n → 𝒳) => Phi (canonBlock n s a j) y)
            (Measure.map T μ) :=
          Finset.aestronglyMeasurable_prod (s := (Finset.univ : Finset (Fin s)))
            (f := fun (j : Fin s) (y : Fin n → 𝒳) => Phi (canonBlock n s a j) y)
            (fun j _ => hmeasPhi (canonBlock n s a j))
        rw [show (∏ j : Fin s, fun (y : Fin n → 𝒳) => Phi (canonBlock n s a j) y)
              = (fun y : Fin n → 𝒳 => ∏ j : Fin s, Phi (canonBlock n s a j) y) from by
            funext y
            exact Finset.prod_apply y Finset.univ
              (fun (j : Fin s) (y : Fin n → 𝒳) => Phi (canonBlock n s a j) y)] at hh
        exact hh
      have h2 : AEStronglyMeasurable (fun y : Fin n → 𝒳 => Phi Finset.univ y)
          (Measure.map T μ) := hmeasPhi Finset.univ
      show AEStronglyMeasurable (fun y : Fin n → 𝒳 =>
        (∏ j : Fin s, Phi (canonBlock n s a j) y) / Phi Finset.univ y) (Measure.map T μ)
      have hinv : Measurable (fun x : ℝ => x⁻¹) :=
        (measurable_inv_iff (f := (id : ℝ → ℝ))).mpr measurable_id
      have h2' : AEMeasurable (fun y : Fin n → 𝒳 => Phi Finset.univ y) (Measure.map T μ) :=
        h2.aemeasurable
      have h3 : AEStronglyMeasurable (fun y : Fin n → 𝒳 => (Phi Finset.univ y)⁻¹)
          (Measure.map T μ) :=
        AEStronglyMeasurable.comp_aemeasurable hinv.aestronglyMeasurable h2'
      simpa only [div_eq_mul_inv] using h1.mul h3
  
    have hHint : Integrable (fun ω => H (T ω)) μ := hRint a ha
    have hp := statopia_math_node_2399454585_e7a325d2 μ T Tσ hT hTσ hpush H hHmeas hHint
    have hprod : ∀ (A : Finset (Fin n)) (g : Fin n → ℝ),
        (∏ i ∈ A, g (σ i)) = ∏ i ∈ A.image σ, g i := by
      intro A g
      refine Finset.prod_bij (fun (i : Fin n) (_ : i ∈ A) => σ i) (fun i hi => ?_)
        (fun i _ k _ h => ?_) (fun b hb => ?_) (fun i _ => rfl)
      · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      · exact σ.injective h
      · obtain ⟨x, hx, hxσ⟩ := Finset.mem_image.mp hb
        exact ⟨x, hx, hxσ⟩
    have h1 : ∀ (ω : Ω) (j : Fin s), Phi (f j) (T ω) = Phi (canonBlock n s a j) (Tσ ω) := by
      intro ω j
      rw [hσ j]
      show (∫ θ, ∏ i ∈ (canonBlock n s a j).image σ, k θ (T ω i) ∂Q0)
        = ∫ θ, ∏ i ∈ canonBlock n s a j, k θ (Tσ ω i) ∂Q0
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun θ => (hprod (canonBlock n s a j) (fun i => k θ (T ω i))).symm))
    have h2 : ∀ ω : Ω, Phi Finset.univ (T ω) = Phi Finset.univ (Tσ ω) := by
      intro ω
      show (∫ θ, ∏ i ∈ Finset.univ, k θ (T ω i) ∂Q0)
        = ∫ θ, ∏ i ∈ Finset.univ, k θ (Tσ ω i) ∂Q0
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      have e : (Finset.univ : Finset (Fin n)).image σ = Finset.univ := by simp
      show (∏ i ∈ Finset.univ, k θ (T ω i)) = ∏ i ∈ Finset.univ, k θ (Tσ ω i)
      rw [hprod Finset.univ (fun i => k θ (T ω i)), e]
    have hpoint : ∀ ω : Ω, G f ω = H (Tσ ω) := by
      intro ω
      show (∏ j : Fin s, Phi (f j) (T ω)) / Phi Finset.univ (T ω)
        = (∏ j : Fin s, Phi (canonBlock n s a j) (Tσ ω)) / Phi Finset.univ (Tσ ω)
      rw [Finset.prod_congr rfl (fun j _ => h1 ω j), h2 ω]
    refine ⟨?_, ?_⟩
    · exact hp.1.congr (Filter.Eventually.of_forall (fun ω => (hpoint ω).symm))
    · have e1 : (∫ ω, G f ω ∂μ) = ∫ ω, H (Tσ ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      have e2 : (∫ ω, H (T ω) ∂μ) = Ival a := rfl
      exact e1.trans (hp.2.trans e2)
  have hGint : ∀ a ∈ orderedCompositions n s, ∀ f ∈ Oa a, Integrable (G f) μ :=
    fun a ha f hf => (hGmain a ha f hf).1
  have hGval : ∀ a ∈ orderedCompositions n s, ∀ f ∈ Oa a, (∫ ω, G f ω ∂μ) = Ival a :=
    fun a ha f hf => (hGmain a ha f hf).2
  have hinner : ∀ a ∈ orderedCompositions n s,
      (∫ ω, (∑ f ∈ Oa a, ca a * G f ω) ∂μ)
        = ((Oa a).card : ℝ) * (ca a * Ival a) := by
    intro a ha
    have hbase : (∫ ω, (∑ f ∈ Oa a, ca a * G f ω) ∂μ)
        = ∑ f ∈ Oa a, (∫ ω, ca a * G f ω ∂μ) := by
      apply integral_finset_sum
      intro f hf
      exact (hGint a ha f hf).const_mul (ca a)
    have hstep : ∀ f ∈ Oa a, (∫ ω, ca a * G f ω ∂μ) = ca a * Ival a := by
      intro f hf
      rw [← hGval a ha f hf]
      simpa only [smul_eq_mul] using integral_const_mul (ca a) (fun ω => G f ω)
    have hstep2 : (∑ f ∈ Oa a, (∫ ω, ca a * G f ω ∂μ)) = ∑ f ∈ Oa a, (ca a * Ival a) :=
      Finset.sum_congr rfl hstep
    rw [hbase, hstep2, Finset.sum_const]
    simp
  have hlin : (∫ ω, (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) ∂μ)
      = ∑ a ∈ orderedCompositions n s, ((Oa a).card : ℝ) * (ca a * Ival a) := by
    have hbase : (∫ ω, (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) ∂μ)
        = ∑ a ∈ orderedCompositions n s, (∫ ω, (∑ f ∈ Oa a, ca a * G f ω) ∂μ) := by
      apply integral_finset_sum
      intro a ha
      exact integrable_finset_sum (Oa a) (fun f hf => (hGint a ha f hf).const_mul (ca a))
    rw [hbase]
    exact Finset.sum_congr rfl (fun a ha => hinner a ha)
  have hcoef : ∀ a ∈ orderedCompositions n s,
      (D * Sf)⁻¹ * (((Oa a).card : ℝ) * (ca a * Ival a))
        = ((n : ℝ) / (Sf * ∏ j : Fin s, ((a j).val : ℝ))) * Ival a := by
    intro a ha
    have ha' : (∀ j : Fin s, 1 ≤ (a j).val) ∧ (∑ j : Fin s, (a j).val) = n := by
      simpa only [orderedCompositions, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    obtain ⟨ha1, ha2⟩ := ha'
    have hcard : (Oa a).card
        = Nat.multinomial (Finset.univ : Finset (Fin s)) (fun j : Fin s => (a j).val) := by
      have hEq : Oa a = (Finset.univ : Finset (Fin s → Finset (Fin n))).filter (fun f =>
          (∀ j : Fin s, f j ≠ ∅) ∧
          (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
          (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
          (∀ j : Fin s, (f j).card = (a j).val)) := by
        ext f
        show (f ∈ Finset.filter (fun f => ∀ j : Fin s, (f j).card = (a j).val)
              (Finset.filter (fun f => (∀ j : Fin s, (f j).Nonempty) ∧
                (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
                (∀ i : Fin n, ∃ j : Fin s, i ∈ f j)) Finset.univ))
            ↔ (f ∈ Finset.filter (fun f =>
                (∀ j : Fin s, f j ≠ ∅) ∧
                (∀ j k : Fin s, j ≠ k → Disjoint (f j) (f k)) ∧
                (∀ i : Fin n, ∃ j : Fin s, i ∈ f j) ∧
                (∀ j : Fin s, (f j).card = (a j).val)) Finset.univ)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.nonempty_iff_ne_empty]
        constructor
        · intro h; exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩
        · intro h; exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
      rw [hEq]
      exact statopia_math_node_4055972497_2dd86b3f n s a ha
    have hfac : ∀ j : Fin s, ((Nat.factorial ((a j).val) : ℕ) : ℝ)
        = ((a j).val : ℝ) * ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ) := by
      intro j
      have hm : 1 ≤ (a j).val := ha1 j
      have h1 : Nat.factorial ((a j).val) = (a j).val * Nat.factorial ((a j).val - 1) := by
        conv_lhs => rw [show (a j).val = ((a j).val - 1) + 1 from (Nat.sub_add_cancel hm).symm]
        rw [Nat.factorial_succ, Nat.sub_add_cancel hm]
      rw [h1]
      push_cast
      ring
    have hF_eq : (∏ j : Fin s, ((Nat.factorial ((a j).val) : ℕ) : ℝ))
        = (∏ j : Fin s, ((a j).val : ℝ)) *
          (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => hfac j)
    have hspec : (∏ j : Fin s, Nat.factorial ((a j).val)) * (Oa a).card = Nat.factorial n := by
      have h := Nat.multinomial_spec (Finset.univ : Finset (Fin s)) (fun j : Fin s => (a j).val)
      rw [← hcard] at h
      simpa [ha2] using h
    have hspecR : (∏ j : Fin s, ((Nat.factorial ((a j).val) : ℕ) : ℝ)) * ((Oa a).card : ℝ)
        = ((Nat.factorial n : ℕ) : ℝ) := by
      rw [← Nat.cast_prod, ← Nat.cast_mul, hspec]
    have hN_eq : ((Nat.factorial n : ℕ) : ℝ)
        = (n : ℝ) * ((Nat.factorial (n - 1) : ℕ) : ℝ) := by
      have h1 : Nat.factorial n = n * Nat.factorial (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
        rw [Nat.factorial_succ, Nat.sub_add_cancel hn]
      rw [h1]
      push_cast
      ring
    have hcomb : ((Oa a).card : ℝ) *
          ((∏ j : Fin s, ((a j).val : ℝ)) *
            (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)))
        = (n : ℝ) * ((Nat.factorial (n - 1) : ℕ) : ℝ) := by
      have h1 : (∏ j : Fin s, ((a j).val : ℝ)) *
            (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)) * ((Oa a).card : ℝ)
          = (n : ℝ) * ((Nat.factorial (n - 1) : ℕ) : ℝ) := by
        rw [← hF_eq, hspecR, hN_eq]
      calc ((Oa a).card : ℝ) *
            ((∏ j : Fin s, ((a j).val : ℝ)) *
              (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)))
          = (∏ j : Fin s, ((a j).val : ℝ)) *
              (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)) *
              ((Oa a).card : ℝ) := by ring
        _ = (n : ℝ) * ((Nat.factorial (n - 1) : ℕ) : ℝ) := h1
    have hA : (∏ j : Fin s, ((a j).val : ℝ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
      exact_mod_cast (show (a j).val ≠ 0 from by have := ha1 j; omega)
    have hSf' : ((Nat.factorial s : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero s
    have hnf : ((Nat.factorial (n - 1) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - 1)
    have hkey : (D * Sf)⁻¹ * ((Oa a).card : ℝ) * ca a
        = (n : ℝ) / (Sf * ∏ j : Fin s, ((a j).val : ℝ)) := by
      show (((Nat.factorial (n - 1) : ℕ) : ℝ) * ((Nat.factorial s : ℕ) : ℝ))⁻¹ *
            ((Oa a).card : ℝ) *
            (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ))
        = (n : ℝ) / (((Nat.factorial s : ℕ) : ℝ) * ∏ j : Fin s, ((a j).val : ℝ))
      rw [eq_div_iff (mul_ne_zero hSf' hA)]
      calc (((Nat.factorial (n - 1) : ℕ) : ℝ) * ((Nat.factorial s : ℕ) : ℝ))⁻¹ *
            ((Oa a).card : ℝ) *
            (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)) *
            (((Nat.factorial s : ℕ) : ℝ) * ∏ j : Fin s, ((a j).val : ℝ))
          = (((Nat.factorial (n - 1) : ℕ) : ℝ) * ((Nat.factorial s : ℕ) : ℝ))⁻¹ *
              (((Oa a).card : ℝ) *
                ((∏ j : Fin s, ((a j).val : ℝ)) *
                  (∏ j : Fin s, ((Nat.factorial ((a j).val - 1) : ℕ) : ℝ)))) *
              ((Nat.factorial s : ℕ) : ℝ) := by ring
        _ = (((Nat.factorial (n - 1) : ℕ) : ℝ) * ((Nat.factorial s : ℕ) : ℝ))⁻¹ *
              ((n : ℝ) * ((Nat.factorial (n - 1) : ℕ) : ℝ)) *
              ((Nat.factorial s : ℕ) : ℝ) := by rw [hcomb]
        _ = (n : ℝ) := by
            have hP : (((Nat.factorial (n - 1) : ℕ) : ℝ) *
                ((Nat.factorial s : ℕ) : ℝ)) ≠ 0 := mul_ne_zero hnf hSf'
            field_simp
    calc (D * Sf)⁻¹ * (((Oa a).card : ℝ) * (ca a * Ival a))
        = ((D * Sf)⁻¹ * ((Oa a).card : ℝ) * ca a) * Ival a := by ring
      _ = ((n : ℝ) / (Sf * ∏ j : Fin s, ((a j).val : ℝ))) * Ival a := by rw [hkey]
  calc (∫ ω, (∑ P ∈ partitionsInto n s,
        ((∏ B ∈ P, ((Nat.factorial (B.card - 1) : ℕ) : ℝ)) /
            ((Nat.factorial (n - 1) : ℕ) : ℝ)) *
          (blockProduct (restrictSeq X n) k Q0 P ω /
            margLikelihood (restrictSeq X n) k Q0 Finset.univ ω)) ∂μ)
      = ∫ ω, (D * Sf)⁻¹ *
          (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (D * Sf)⁻¹ *
          (∫ ω, (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω) ∂μ) := by
        simpa only [smul_eq_mul] using
          integral_const_mul (D * Sf)⁻¹
            (fun ω => (∑ a ∈ orderedCompositions n s, ∑ f ∈ Oa a, ca a * G f ω))
    _ = (D * Sf)⁻¹ *
          (∑ a ∈ orderedCompositions n s, ((Oa a).card : ℝ) * (ca a * Ival a)) := by
        rw [hlin]
    _ = ∑ a ∈ orderedCompositions n s,
          ((n : ℝ) / (Sf * ∏ j : Fin s, ((a j).val : ℝ))) * Ival a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a ha => hcoef a ha)
  /- @proof-region region.root.17d0e7815844 end -/

end Statlib.Imported

-- Paper root revision 380a8ee0-81ec-4605-8ba3-3543e059f7a0
