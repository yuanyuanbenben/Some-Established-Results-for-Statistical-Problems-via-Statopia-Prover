import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2340343151_79e1234f : ∀ (c : ℝ) (hc : 0 < c) (t : ℕ) (ht : 0 < t)
    (g q0 : ℝ → ℝ)
    (hg_meas : Measurable g) (hg_nonneg : ∀ y : ℝ, 0 ≤ g y)
    (hg_support : ∀ y : ℝ, y ∉ Set.Icc (-c) c → g y = 0)
    (hq0_meas : Measurable q0) (hq0_nonneg : ∀ y : ℝ, 0 ≤ q0 y)
    (hq0_density : ∫⁻ y, ENNReal.ofReal (q0 y) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ y ∈ Set.Icc (-c) c, m ≤ g y ∧ g y ≤ M)
    (theta : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |theta j - theta k|)
    (L : ℝ) (hL : 0 < L)
    (delta : Fin t → ℝ) (hdelta : ∀ j : Fin t, 0 < delta j)
    (hT4 : ∀ j : Fin t, ∀ y ∈ Set.Ioo (theta j - delta j) (theta j + delta j), L ≤ q0 y)
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hne : ∀ j : Fin t,
      1 ≤ (Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (theta j - c) (theta j + c))).card)
    (hcover : ∑ j : Fin t,
      (Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (theta j - c) (theta j + c))).card = n)
    (hnotbd : ∀ (i : Fin n) (j : Fin t), x i ≠ theta j - c ∧ x i ≠ theta j + c),
    let C : Fin t → Finset (Fin n) :=
      fun j => Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (theta j - c) (theta j + c));
    let Num : ℝ :=
      ∑ A ∈ tau n t,
        (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, margLik g q0 B x);
    IsPartitionOf n t (Finset.image C Finset.univ) ∧
      (∏ j : Fin t, (((C j).card - 1).factorial : ℝ)) *
          (∏ j : Fin t, margLik g q0 (C j) x) ≤ Num ∧
      ((∀ j : Fin t, 0 < (((C j).card - 1).factorial : ℝ)) ∧
        (∀ j : Fin t, 0 < margLik g q0 (C j) x)) ∧
      0 < Num := by
  /- @proof-region region.target-node.session.7f7827780b1533fc begin -/
  intro c hc t ht g q0 hg_meas hg_nonneg hg_support hq0_meas hq0_nonneg hq0_density hT1 theta hsep L hL delta hdelta hT4 n hn x hne hcover hnotbd
  classical
  let C : Fin t → Finset (Fin n) := fun j => Finset.univ.filter (fun i : Fin n => x i ∈ Set.Icc (theta j - c) (theta j + c))
  let Num : ℝ := ∑ A ∈ tau n t, (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, margLik g q0 B x)
  change IsPartitionOf n t (Finset.image C Finset.univ) ∧
      (∏ j : Fin t, (((C j).card - 1).factorial : ℝ)) *
          (∏ j : Fin t, margLik g q0 (C j) x) ≤ Num ∧
      ((∀ j : Fin t, 0 < (((C j).card - 1).factorial : ℝ)) ∧
        (∀ j : Fin t, 0 < margLik g q0 (C j) x)) ∧
      0 < Num
  obtain ⟨m, M, hm_pos, hmM, hgb⟩ := hT1
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
  have hg_le_M : ∀ y : ℝ, g y ≤ M := by
    intro y
    by_cases hy : y ∈ Set.Icc (-c) c
    · exact (hgb y hy).2
    · rw [hg_support y hy]; exact hM_nonneg
  have hg_ge_m : ∀ y ∈ Set.Icc (-c) c, m ≤ g y := fun y hy => (hgb y hy).1
  have hmemC : ∀ (j : Fin t) (i : Fin n), i ∈ C j ↔ x i ∈ Set.Icc (theta j - c) (theta j + c) := by
    intro j i
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
  have hCne : ∀ j : Fin t, (C j).Nonempty := by
    intro j
    have h1 : 1 ≤ (C j).card := by simpa only [C] using hne j
    exact Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hdisj : ∀ j k : Fin t, j ≠ k → Disjoint (C j) (C k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro i hij hik
    rw [hmemC j i] at hij
    rw [hmemC k i] at hik
    have hj1 : |x i - theta j| ≤ c := by
      rw [abs_le]; exact ⟨by linarith [hij.1], by linarith [hij.2]⟩
    have hk1 : |x i - theta k| ≤ c := by
      rw [abs_le]; exact ⟨by linarith [hik.1], by linarith [hik.2]⟩
    have h2 : |theta j - theta k| ≤ 2 * c := by
      calc |theta j - theta k| = |(theta j - x i) + (x i - theta k)| := by
              rw [show theta j - theta k = (theta j - x i) + (x i - theta k) by ring]
        _ ≤ |theta j - x i| + |x i - theta k| := abs_add_le _ _
        _ = |x i - theta j| + |x i - theta k| := by rw [abs_sub_comm]
        _ ≤ c + c := add_le_add hj1 hk1
        _ = 2 * c := by ring
    linarith [hsep j k hjk]
  have hC_inj : Function.Injective C := by
    intro j k hjk
    by_contra hne_jk
    obtain ⟨a, ha⟩ := hCne j
    have hak : a ∈ C k := by rw [← hjk]; exact ha
    rw [hmemC j a] at ha
    rw [hmemC k a] at hak
    have hj1 : |x a - theta j| ≤ c := by
      rw [abs_le]; exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hk1 : |x a - theta k| ≤ c := by
      rw [abs_le]; exact ⟨by linarith [hak.1], by linarith [hak.2]⟩
    have h3 : |theta j - theta k| ≤ 2 * c := by
      calc |theta j - theta k| = |(theta j - x a) + (x a - theta k)| := by
              rw [show theta j - theta k = (theta j - x a) + (x a - theta k) by ring]
        _ ≤ |theta j - x a| + |x a - theta k| := abs_add_le _ _
        _ = |x a - theta j| + |x a - theta k| := by rw [abs_sub_comm]
        _ ≤ c + c := add_le_add hj1 hk1
        _ = 2 * c := by ring
    linarith [hsep j k hne_jk]
  have hupper : Finset.univ.biUnion C = Finset.univ := by
    have hpd : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint C := by
      intro j _ k _ hjk; exact hdisj j k hjk
    have hcard : (Finset.univ.biUnion C).card = n := by
      rw [Finset.card_biUnion hpd]
      simpa only [C] using hcover
    have hsub : Finset.univ.biUnion C ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
    have hcl : (Finset.univ : Finset (Fin n)).card ≤ (Finset.univ.biUnion C).card := by
      simp [hcard]
    exact Finset.eq_of_subset_of_card_le hsub hcl
  have hpart : IsPartitionOf n t (Finset.image C Finset.univ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Finset.card_image_of_injOn (fun a _ b _ h => hC_inj h), Finset.card_univ,
        Fintype.card_fin]
    · intro B hB
      rw [Finset.mem_image] at hB
      obtain ⟨j, _, rfl⟩ := hB
      exact hCne j
    · intro B hB D hD hBD
      rw [Finset.mem_image] at hB hD
      obtain ⟨j, _, rfl⟩ := hB
      obtain ⟨k, _, rfl⟩ := hD
      have hjk : j ≠ k := by rintro rfl; exact hBD rfl
      exact hdisj j k hjk
    · intro a
      have ha : a ∈ Finset.univ.biUnion C := by
        rw [hupper]; exact Finset.mem_univ a
      rw [Finset.mem_biUnion] at ha
      obtain ⟨j, _, hj⟩ := ha
      exact ⟨C j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hj⟩
  have hmarg_nonneg : ∀ (B : Finset (Fin n)), 0 ≤ margLik g q0 B x := by
    intro B
    change 0 ≤ ∫ θ, Finset.prod B (fun i => g (x i - θ)) * q0 θ
    apply MeasureTheory.integral_nonneg
    intro θ
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hg_nonneg (x i - θ))) (hq0_nonneg θ)
  have hpos : ∀ j : Fin t, 0 < margLik g q0 (C j) x := by
    intro j
    set A := C j with hA
    have hAne : A.Nonempty := by rw [hA]; exact hCne j
    have hmemA : ∀ i : Fin n, i ∈ A ↔ x i ∈ Set.Icc (theta j - c) (theta j + c) := by
      intro i; rw [hA]; exact hmemC j i
    obtain ⟨iu, hiuA, hiumax⟩ := Finset.exists_max_image A x hAne
    obtain ⟨iv, hivA, hivmin⟩ := Finset.exists_min_image A x hAne
    let u := x iu
    let v := x iv
    have hu_lt : u < theta j + c := by
      have hmem := (hmemA iu).mp hiuA
      exact lt_of_le_of_ne hmem.2 (hnotbd iu j).2
    have hv_gt : theta j - c < v := by
      have hmem := (hmemA iv).mp hivA
      exact lt_of_le_of_ne' hmem.1 (hnotbd iv j).1
    set d := min (min (v + c - theta j) (theta j - u + c)) (delta j) with hd
    have hd_pos : 0 < d := by
      rw [hd]
      exact lt_min (lt_min (by linarith [hv_gt]) (by linarith [hu_lt])) (hdelta j)
    have hd_le_d2 : d ≤ v + c - theta j := by
      rw [hd]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hd_le_d1 : d ≤ theta j - u + c := by
      rw [hd]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hd_le_delta : d ≤ delta j := by
      rw [hd]; exact min_le_right _ _
    have hf_nn : 0 ≤ᵐ[volume] (fun θ : ℝ => (∏ i ∈ A, g (x i - θ)) * q0 θ) :=
      Filter.Eventually.of_forall
        (fun θ => mul_nonneg (Finset.prod_nonneg (fun i _ => hg_nonneg (x i - θ))) (hq0_nonneg θ))
    have hf_aesm : AEStronglyMeasurable (fun θ : ℝ => (∏ i ∈ A, g (x i - θ)) * q0 θ) volume := by
      apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · exact Finset.measurable_prod A (fun i _ => hg_meas.comp (measurable_const.sub measurable_id))
      · exact hq0_meas
    have hfd : ∀ θ ∈ Set.Ioo (theta j - d) (theta j + d),
        m ^ A.card * L ≤ (∏ i ∈ A, g (x i - θ)) * q0 θ := by
      intro θ hθ
      rw [Set.mem_Ioo] at hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      have hfac : ∀ i ∈ A, m ≤ g (x i - θ) := by
        intro i hiA
        have hxle : x i ≤ u := hiumax i hiA
        have hvx : v ≤ x i := hivmin i hiA
        have hut : u - c < θ := by linarith [hθ1, hd_le_d1]
        have hvt : θ < v + c := by linarith [hθ2, hd_le_d2]
        have hmem : x i - θ ∈ Set.Icc (-c) c := by
          rw [Set.mem_Icc]; constructor <;> linarith [hut, hvt, hxle, hvx]
        exact hg_ge_m (x i - θ) hmem
      have hprod : m ^ A.card ≤ ∏ i ∈ A, g (x i - θ) := by
        have hp := Finset.prod_le_prod (s := A) (f := fun _ => m) (g := fun i => g (x i - θ))
          (fun i _ => le_of_lt hm_pos) hfac
        rwa [Finset.prod_const] at hp
      have hq0j : L ≤ q0 θ := by
        apply hT4 j
        rw [Set.mem_Ioo]; constructor <;> linarith [hθ1, hθ2, hd_le_delta]
      exact le_trans (mul_le_mul_of_nonneg_left hq0j (le_of_lt (pow_pos hm_pos _)))
        (mul_le_mul_of_nonneg_right hprod (hq0_nonneg θ))
    have hlb : ENNReal.ofReal (m ^ A.card * L * (2 * d)) ≤
        ∫⁻ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ) := by
      have hmkL_nn : (0 : ℝ) ≤ m ^ A.card * L := le_of_lt (mul_pos (pow_pos hm_pos _) hL)
      have hvol : volume (Set.Ioo (theta j - d) (theta j + d)) = ENNReal.ofReal (2 * d) := by
        rw [Real.volume_Ioo]; congr 1; ring
      calc ENNReal.ofReal (m ^ A.card * L * (2 * d))
          = ENNReal.ofReal (m ^ A.card * L) * ENNReal.ofReal (2 * d) := by
              rw [ENNReal.ofReal_mul hmkL_nn]
        _ = ENNReal.ofReal (m ^ A.card * L) * volume (Set.Ioo (theta j - d) (theta j + d)) := by
              rw [hvol]
        _ = ∫⁻ θ, (Set.Ioo (theta j - d) (theta j + d)).indicator
              (fun _ => ENNReal.ofReal (m ^ A.card * L)) θ := by
              rw [MeasureTheory.lintegral_indicator_const measurableSet_Ioo]
        _ ≤ ∫⁻ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ) := by
              apply MeasureTheory.lintegral_mono
              intro θ
              by_cases hθ : θ ∈ Set.Ioo (theta j - d) (theta j + d)
              · rw [Set.indicator_of_mem hθ]
                exact ENNReal.ofReal_le_ofReal (hfd θ hθ)
              · rw [Set.indicator_of_notMem hθ]
                exact zero_le _
    have hf_int : Integrable (fun θ : ℝ => (∏ i ∈ A, g (x i - θ)) * q0 θ) volume := by
      have hlt : ∫⁻ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ) ≤ ENNReal.ofReal (M ^ A.card) := by
        have hpt : ∀ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ) ≤ ENNReal.ofReal (M ^ A.card * q0 θ) := by
          intro θ
          apply ENNReal.ofReal_le_ofReal
          have hprod : (∏ i ∈ A, g (x i - θ)) ≤ M ^ A.card := by
            have hp := Finset.prod_le_prod (s := A) (f := fun i => g (x i - θ)) (g := fun _ => M)
              (fun i _ => hg_nonneg (x i - θ)) (fun i _ => hg_le_M (x i - θ))
            rwa [Finset.prod_const] at hp
          exact mul_le_mul_of_nonneg_right hprod (hq0_nonneg θ)
        calc ∫⁻ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ)
            ≤ ∫⁻ θ, ENNReal.ofReal (M ^ A.card * q0 θ) := MeasureTheory.lintegral_mono hpt
          _ = ∫⁻ θ, ENNReal.ofReal (M ^ A.card) * ENNReal.ofReal (q0 θ) := by
                simp_rw [ENNReal.ofReal_mul (le_of_lt (pow_pos hM_pos _))]
          _ = ENNReal.ofReal (M ^ A.card) * ∫⁻ θ, ENNReal.ofReal (q0 θ) := by
                rw [MeasureTheory.lintegral_const_mul]
                exact hq0_meas.ennreal_ofReal
          _ = ENNReal.ofReal (M ^ A.card) * 1 := by rw [hq0_density]
          _ = ENNReal.ofReal (M ^ A.card) := mul_one _
      exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hf_aesm hf_nn).mp
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlt)
    have h_eq : ENNReal.ofReal (margLik g q0 A x) =
        ∫⁻ θ, ENNReal.ofReal ((∏ i ∈ A, g (x i - θ)) * q0 θ) := by
      change ENNReal.ofReal (∫ θ, Finset.prod A (fun i => g (x i - θ)) * q0 θ) =
        ∫⁻ θ, ENNReal.ofReal (Finset.prod A (fun i => g (x i - θ)) * q0 θ)
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nn
    have harg_pos : 0 < m ^ A.card * L * (2 * d) :=
      mul_pos (mul_pos (pow_pos hm_pos _) hL) (by linarith [hd_pos])
    have hfin : 0 < ENNReal.ofReal (margLik g q0 A x) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr harg_pos) (by rw [h_eq]; exact hlb)
    exact ENNReal.ofReal_pos.mp hfin
  have hB : (∏ j : Fin t, (((C j).card - 1).factorial : ℝ)) *
      (∏ j : Fin t, margLik g q0 (C j) x) ≤ Num := by
    have hfact_eq : (∏ B ∈ Finset.image C Finset.univ, ((B.card - 1).factorial : ℝ)) =
        ∏ j : Fin t, (((C j).card - 1).factorial : ℝ) := by
      rw [Finset.prod_image (fun a _ b _ h => hC_inj h)]
    have hmarg_eq : (∏ B ∈ Finset.image C Finset.univ, margLik g q0 B x) =
        ∏ j : Fin t, margLik g q0 (C j) x := by
      rw [Finset.prod_image (fun a _ b _ h => hC_inj h)]
    have hAx_mem : Finset.image C Finset.univ ∈ tau n t := by
      rw [tau]
      exact Finset.mem_filter.mpr ⟨by simp, hpart⟩
    have hterm_nn : ∀ A ∈ tau n t,
        0 ≤ (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, margLik g q0 B x) := by
      intro A _
      exact mul_nonneg (Finset.prod_nonneg (fun B _ => Nat.cast_nonneg _))
        (Finset.prod_nonneg (fun B _ => hmarg_nonneg B))
    rw [← hfact_eq, ← hmarg_eq]
    change (∏ B ∈ Finset.image C Finset.univ, ((B.card - 1).factorial : ℝ)) *
        (∏ B ∈ Finset.image C Finset.univ, margLik g q0 B x) ≤
        ∑ A ∈ tau n t, (∏ B ∈ A, ((B.card - 1).factorial : ℝ)) * (∏ B ∈ A, margLik g q0 B x)
    exact Finset.single_le_sum (fun A hA => hterm_nn A hA) hAx_mem
  have hE : 0 < Num := by
    have hLHS_pos : 0 < (∏ j : Fin t, (((C j).card - 1).factorial : ℝ)) *
        (∏ j : Fin t, margLik g q0 (C j) x) := by
      apply mul_pos
      · exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _))
      · exact Finset.prod_pos (fun j _ => hpos j)
    exact lt_of_lt_of_le hLHS_pos hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hpart
  · exact hB
  · refine ⟨?_, ?_⟩
    · intro j
      exact Nat.cast_pos.mpr (Nat.factorial_pos _)
    · exact hpos
  · exact hE
  /- @proof-region region.target-node.session.7f7827780b1533fc end -/

end Statlib.Imported
