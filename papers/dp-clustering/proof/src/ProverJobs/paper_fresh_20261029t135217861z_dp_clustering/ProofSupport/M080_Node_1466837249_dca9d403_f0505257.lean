import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M021_Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.Definitions
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M078_Node_2125196411_ab440be6_135a26f9
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProofSupport.M079_Node_4113706424_f2009e3d_da786935

/- Original module ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_1466837249_dca9d403_f0505257; genuine source relocated, namespace-isolated only. -/
namespace DPCompletedProof
open _root_.Statlib.Imported
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_1466837249_dca9d403 : ∀ (g q0 : ℝ → ℝ) (c : ℝ) (t : ℕ)
    (hc : 0 < c) (ht : 1 ≤ t)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ x : ℝ, 0 ≤ q0 x)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (p : Fin t → ℝ) (hp_pos : ∀ j : Fin t, 0 < p j) (hp_sum : ∑ j : Fin t, p j = 1)
    (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (Rm : Fin t → Measure ℝ)
    (hRm_prob : ∀ j : Fin t, IsProbabilityMeasure (Rm j))
    (hRm_eq : ∀ j : Fin t,
      Rm j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j))))
    (hP_eq : P = ∑ j : Fin t, ENNReal.ofReal (p j) • Rm j)
    (N : Fin t → ℕ),
    Tendsto
      (fun n : ℕ => (iidLaw P) {ω : ℕ → ℝ | ∀ j : Fin t,
        let Cj : Finset (Fin n) :=
          Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))
        let nj : ℕ := Cj.card
        let Uj : ℝ := if h : Cj.Nonempty then Cj.sup' h (fun i : Fin n => ω (i : ℕ)) else thetaStar j
        let Yj : ℝ := if nj = 0 then 1 else
          min 1 ((nj : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) * (c + thetaStar j - Uj))
        N j ≤ nj ∧ (1 / 2 : ℝ) ≤ Yj ∧ Yj ≤ 1})
      atTop (nhds 1) := by
  /- @proof-region region.target-node.session.53a7c4e40c84d910 begin -/
  intro g q0 c t hc ht hg_meas hg_nonneg hg_support hg_density hq0_meas hq0_nonneg hT1
  intro P hP p hp_pos hp_sum thetaStar hsep Rm hRm_prob hRm_eq hP_eq N
  haveI := hP
  classical
  let I : Fin t → Set ℝ := fun j => Set.Icc (thetaStar j - c) (thetaStar j + c)
  let cnt : ℕ → (ℕ → ℝ) → Fin t → ℕ := fun n ω j =>
    (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I j)).card
  let mx : ℕ → (ℕ → ℝ) → Fin t → ℝ := fun n ω j =>
    if h : (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I j)).Nonempty
      then (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I j)).sup' h (fun i : Fin n => ω (i : ℕ))
      else thetaStar j
  let vy : ℕ → (ℕ → ℝ) → Fin t → ℝ := fun n ω j =>
    if cnt n ω j = 0 then 1 else
      min 1 ((cnt n ω j : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))) * (c + thetaStar j - mx n ω j))
  let Om : ℕ → Set (ℕ → ℝ) := fun n =>
    {ω : ℕ → ℝ | ∀ j : Fin t, N j ≤ cnt n ω j ∧ (1 / 2 : ℝ) ≤ vy n ω j ∧ vy n ω j ≤ 1}
  change Tendsto (fun n : ℕ => (iidLaw P) (Om n)) atTop (nhds 1)
  have huniv : (iidLaw P) Set.univ = 1 := by
    have h : (Measure.infinitePi (fun _ : ℕ => P)) Set.univ
        = ∏ i ∈ (∅ : Finset ℕ), P (Set.univ) := by
      have h0 := Measure.infinitePi_pi (μ := fun _ : ℕ => P) (hμ := fun _ : ℕ => hP)
        (s := (∅ : Finset ℕ)) (t := fun _ : ℕ => Set.univ) (by simp)
      simpa using h0
    simpa [iidLaw] using h
  have hA1 : ∀ n : ℕ, (iidLaw P) (Om n) ≤ 1 := by
    intro n
    rw [← huniv]
    exact measure_mono (Set.subset_univ _)
  have hB1 : ∀ n : ℕ, (iidLaw P) ((Om n)ᶜ) ≤ 1 := by
    intro n
    rw [← huniv]
    exact measure_mono (Set.subset_univ _)
  have hAtop : ∀ n : ℕ, (iidLaw P) (Om n) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top WithTop.one_ne_top (hA1 n)
  have hBtop : ∀ n : ℕ, (iidLaw P) ((Om n)ᶜ) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top WithTop.one_ne_top (hB1 n)
  have h1top : (1 : ENNReal) < ⊤ := by
    simpa using (ENNReal.ofReal_lt_top (r := 1))
  have hsumtop : ∀ n : ℕ, (iidLaw P) (Om n) + (iidLaw P) ((Om n)ᶜ) ≠ ⊤ := by
    intro n
    refine ne_of_lt (WithTop.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact lt_of_le_of_lt (hA1 n) h1top
    · exact lt_of_le_of_lt (hB1 n) h1top
  have hYle : ∀ (n : ℕ) (ω : ℕ → ℝ) (j : Fin t), vy n ω j ≤ 1 := by
    intro n ω j
    by_cases h0 : cnt n ω j = 0
    · simp [vy, h0]
    · simp only [vy, h0, if_false]
      exact min_le_left _ _
  have hcount : ∀ j : Fin t,
      Tendsto (fun n : ℕ => ((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}).toReal) atTop (nhds 0) := by
    intro j
    exact statopia_math_node_4113706424_f2009e3d g c t hc hg_meas hg_nonneg hg_support
      hg_density P p hp_pos hp_sum thetaStar hsep Rm hRm_prob hRm_eq hP_eq N j
  have htail : ∀ j : Fin t,
      Tendsto (fun n : ℕ => ((iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}).toReal) atTop (nhds 0) := by
    intro j
    exact statopia_math_node_2125196411_ab440be6 g c t hc ht hg_meas hg_nonneg hg_support
      hg_density hT1 P p hp_pos hp_sum thetaStar hsep Rm hRm_prob hRm_eq hP_eq j
  have hbound : ∀ n : ℕ, ((iidLaw P) ((Om n)ᶜ)).toReal
      ≤ ∑ j : Fin t, (((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}).toReal
        + ((iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}).toReal) := by
    intro n
    have hAle : ∀ j : Fin t, (iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j} ≤ 1 := fun j =>
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq huniv)
    have hBle : ∀ j : Fin t, (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2} ≤ 1 := fun j =>
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq huniv)
    have htermlt : ∀ j : Fin t,
        (iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}
          + (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2} < ⊤ := fun j =>
      WithTop.add_lt_top.mpr
        ⟨lt_of_le_of_lt (hAle j) h1top, lt_of_le_of_lt (hBle j) h1top⟩
    have hterm : ∀ j : Fin t,
        (iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j ∨ vy n ω j < 1 / 2}
          ≤ (iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}
            + (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2} := by
      intro j
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro ω h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hsub : (Om n)ᶜ ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin t)),
        {ω : ℕ → ℝ | cnt n ω j < N j ∨ vy n ω j < 1 / 2} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Om, Set.mem_setOf_eq, not_forall] at hω
      obtain ⟨j, hj⟩ := hω
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine Set.mem_iUnion.mpr ⟨by simp, ?_⟩
      simp only [Set.mem_setOf_eq]
      by_cases hA : N j ≤ cnt n ω j
      · by_cases hB : (1 / 2 : ℝ) ≤ vy n ω j
        · exact absurd ⟨hA, hB, hYle n ω j⟩ hj
        · exact Or.inr (not_le.mp hB)
      · exact Or.inl (not_le.mp hA)
    have hm : ((iidLaw P) ((Om n)ᶜ))
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin t)),
            ((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}
              + (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}) := by
      refine le_trans (measure_mono hsub) (le_trans
        (measure_biUnion_finset_le (Finset.univ : Finset (Fin t))
          (fun j => {ω : ℕ → ℝ | cnt n ω j < N j ∨ vy n ω j < 1 / 2}))
        (Finset.sum_le_sum (fun j _ => hterm j)))
    have hfin : ∑ j ∈ (Finset.univ : Finset (Fin t)),
        ((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}
          + (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}) < ⊤ :=
      WithTop.sum_lt_top.mpr (fun j _ => htermlt j)
    have hle := ENNReal.toReal_mono (ne_of_lt hfin) hm
    have hsum_eq : (∑ j ∈ (Finset.univ : Finset (Fin t)),
        ((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}
          + (iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2})).toReal
        = ∑ j : Fin t, (((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}).toReal
          + ((iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}).toReal) := by
      rw [ENNReal.toReal_sum (fun j _ => ne_of_lt (htermlt j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact ENNReal.toReal_add (ne_of_lt (lt_of_le_of_lt (hAle j) h1top))
        (ne_of_lt (lt_of_le_of_lt (hBle j) h1top))
    rw [hsum_eq] at hle
    exact hle
  have hbad : Tendsto (fun n : ℕ => ((iidLaw P) ((Om n)ᶜ)).toReal) atTop (nhds 0) := by
    have hsumlim : Tendsto (fun n : ℕ => ∑ j : Fin t,
        (((iidLaw P) {ω : ℕ → ℝ | cnt n ω j < N j}).toReal
          + ((iidLaw P) {ω : ℕ → ℝ | vy n ω j < 1 / 2}).toReal)) atTop (nhds 0) := by
      have h := tendsto_finset_sum (Finset.univ : Finset (Fin t))
        (fun j _ => (hcount j).add (htail j))
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumlim
      (Eventually.of_forall fun n => ENNReal.toReal_nonneg) (Eventually.of_forall hbound)
  have hupper : ∀ n : ℕ, ((iidLaw P) (Om n)).toReal ≤ 1 := by
    intro n
    have h := ENNReal.toReal_mono WithTop.one_ne_top (hA1 n)
    simpa using h
  have hlower : ∀ n : ℕ, 1 - ((iidLaw P) ((Om n)ᶜ)).toReal ≤ ((iidLaw P) (Om n)).toReal := by
    intro n
    have hsum : (1 : ENNReal) ≤ (iidLaw P) (Om n) + (iidLaw P) ((Om n)ᶜ) := by
      rw [← huniv, ← Set.union_compl_self (Om n)]
      exact measure_union_le _ _
    have h2 : ((iidLaw P) (Om n) + (iidLaw P) ((Om n)ᶜ)).toReal
        = ((iidLaw P) (Om n)).toReal + ((iidLaw P) ((Om n)ᶜ)).toReal :=
      ENNReal.toReal_add (hAtop n) (hBtop n)
    have h3 : (1 : ENNReal).toReal ≤ ((iidLaw P) (Om n) + (iidLaw P) ((Om n)ᶜ)).toReal :=
      ENNReal.toReal_mono (hsumtop n) hsum
    rw [ENNReal.toReal_one, h2] at h3
    linarith
  have hlim : Tendsto (fun n : ℕ => ((iidLaw P) (Om n)).toReal) atTop (nhds 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - ((iidLaw P) ((Om n)ᶜ)).toReal) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hbad
    have h2 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h3 := tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2
      (Eventually.of_forall hlower) (Eventually.of_forall hupper)
    simpa using h3
  have hcongr : (fun n : ℕ => (iidLaw P) (Om n))
      = fun n : ℕ => ENNReal.ofReal (((iidLaw P) (Om n)).toReal) := by
    funext n
    exact ((ENNReal.ofReal_toReal_eq_iff).mpr (hAtop n)).symm
  rw [hcongr]
  have hcont : Tendsto (fun n : ℕ => ENNReal.ofReal (((iidLaw P) (Om n)).toReal)) atTop
      (nhds (ENNReal.ofReal 1)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  simpa using hcont
  /- @proof-region region.target-node.session.53a7c4e40c84d910 end -/

end Statlib.Imported
end DPCompletedProof
