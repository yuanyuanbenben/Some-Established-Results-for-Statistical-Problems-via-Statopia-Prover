import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Vocabulary
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.Base
import ProverJobs.paper_fresh_20261029t135217861z_dp_clustering.ProvedNodes.Node_3597484326_59681b58_80f928b2
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
open Statlib.Imported

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal
namespace Statlib.Imported

set_option autoImplicit false in
theorem statopia_math_node_2125196411_ab440be6 : ∀ (g : ℝ → ℝ) (c : ℝ) (t : ℕ) (hc : 0 < c) (ht : 1 ≤ t)
    (hg_meas : Measurable g) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_support : ∀ x : ℝ, x ∉ Set.Icc (-c) c → g x = 0)
    (hg_density : ∫⁻ x, ENNReal.ofReal (g x) ∂volume = 1)
    (hT1 : ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ Set.Icc (-c) c, m ≤ g x ∧ g x ≤ M)
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (p : Fin t → ℝ) (hp_pos : ∀ j : Fin t, 0 < p j) (hp_sum : ∑ j : Fin t, p j = 1)
    (thetaStar : Fin t → ℝ)
    (hsep : ∀ j k : Fin t, j ≠ k → 2 * c < |thetaStar j - thetaStar k|)
    (Rm : Fin t → Measure ℝ)
    (hRm_prob : ∀ j : Fin t, IsProbabilityMeasure (Rm j))
    (hRm_eq : ∀ j : Fin t,
      Rm j = volume.withDensity (fun x : ℝ => ENNReal.ofReal (g (x - thetaStar j))))
    (hP_eq : P = ∑ j : Fin t, ENNReal.ofReal (p j) • Rm j),
    ∀ j : Fin t,
      Tendsto
        (fun n : ℕ => ((iidLaw P) {ω : ℕ → ℝ |
          (if (Finset.univ.filter
                (fun i : Fin n => ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card = 0
            then (1 : ℝ)
            else min 1
              (((Finset.univ.filter
                  (fun i : Fin n =>
                    ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).card : ℝ)
                * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ)))
                * (c + thetaStar j -
                  (if h : (Finset.univ.filter
                      (fun i : Fin n =>
                        ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).Nonempty
                    then (Finset.univ.filter
                        (fun i : Fin n =>
                          ω (i : ℕ) ∈ Set.Icc (thetaStar j - c) (thetaStar j + c))).sup' h
                          (fun i : Fin n => ω (i : ℕ))
                    else thetaStar j)))) < 1 / 2}).toReal)
        atTop (nhds 0) := by
  /- @proof-region region.target-node.session.120ab4dc3b0a43c0 begin -/
  intro g c t hc ht hg_meas hg_nonneg hg_support hg_density hT1 P _ p hp_pos hp_sum thetaStar hsep Rm
    hRm_prob hRm_eq hP_eq j
  obtain ⟨m, M, hm, hmM, hTM⟩ := hT1
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  set I : Set ℝ := Set.Icc (thetaStar j - c) (thetaStar j + c) with hI
  set C₀ : ℝ := M / (4 * c * m) with hC₀
  have hC₀pos : 0 < C₀ := by
    rw [hC₀]
    have h4cm : (0:ℝ) < 4 * c * m := by nlinarith
    exact div_pos hMpos h4cm
  have hexp : (0:ℝ) < 1 / (2 * (t:ℝ)) := by
    have htR : (0:ℝ) < (t:ℝ) := by
      have : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
      linarith
    positivity
  have hloglim : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ => (Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ)))) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp hloglim
  have hinv : Tendsto (fun n : ℕ => ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hg0 : Tendsto (fun n : ℕ => C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹)
      atTop (nhds 0) := by
    simpa using hinv.const_mul C₀
  have hmain : ∀ᶠ n : ℕ in atTop,
      (iidLaw P) {ω : ℕ → ℝ |
        (if (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card = 0 then (1 : ℝ)
          else min 1
            (((Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card : ℝ)
              * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ)))
              * (c + thetaStar j -
                (if h : (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).Nonempty
                  then (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).sup' h
                    (fun i : Fin n => ω (i : ℕ))
                  else thetaStar j)))) < 1 / 2}
        ≤ ENNReal.ofReal (C₀ * ((Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ))))⁻¹) := by
    have hLbig : ∀ᶠ n : ℕ in atTop,
        1 / (4 * c) ≤ (Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))) :=
      hL.eventually (eventually_ge_atTop (1 / (4 * c)))
    filter_upwards [hLbig, eventually_ge_atTop 2] with n hLn hn2
    have hc4 : (0:ℝ) < 1 / (4 * c) := by
      have h4c : (0:ℝ) < 4 * c := by linarith
      positivity
    set L : ℝ := (Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))) with hLdef
    have hLpos : 0 < L := by
      rw [hLdef]
      exact lt_of_lt_of_le hc4 hLn
    set u : ℕ → ℝ := fun k => 1 / (2 * (k:ℝ) * L) with hudef
    have hu_pos : ∀ k : ℕ, 1 ≤ k → 0 < u k := by
      intro k hk
      have hkR : (0:ℝ) < (k:ℝ) := by
        have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        linarith
      simp only [hudef]
      positivity
    have hu_le : ∀ k : ℕ, 1 ≤ k → u k ≤ 2 * c := by
      intro k hk
      have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      have h4 : (1:ℝ) ≤ 4 * c * L := by
        have h5 : (4 * c) * (1 / (4 * c)) ≤ (4 * c) * L :=
          mul_le_mul_of_nonneg_left hLn (by linarith)
        have h4c : (0:ℝ) < 4 * c := by linarith
        rwa [mul_one_div, div_self (ne_of_gt h4c)] at h5
      have hprod : (1:ℝ) ≤ (2 * (k:ℝ) * L) * (2 * c) := by nlinarith
      have hpos : (0:ℝ) < 2 * (k:ℝ) * L := by
        have hk0 : (0:ℝ) < (k:ℝ) := by linarith
        positivity
      have hmul : (2 * (k:ℝ) * L) * u k = 1 := by
        have hk0 : (k:ℝ) ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < (k:ℝ))
        have hL0 : L ≠ 0 := ne_of_gt hLpos
        simp only [hudef]
        field_simp
      nlinarith [hmul, hprod, hpos]
    have hI_meas : MeasurableSet I := by
      rw [hI]
      exact measurableSet_Icc
    set Y : (ℕ → ℝ) → ℝ := fun ω =>
      if (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card = 0 then (1 : ℝ)
      else min 1
        (((Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card : ℝ) * L
          * (c + thetaStar j -
            (if h : (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).Nonempty
              then (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).sup' h
                (fun i : Fin n => ω (i : ℕ))
              else thetaStar j))) with hY
    set cyl : Finset (Fin n) → Fin n → Set (ℕ → ℝ) :=
      fun S i => Set.pi ((Finset.range n : Finset ℕ) : Set ℕ)
        (fun m => if m = (i:ℕ) then Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)
          else if m ∈ S.image (fun j : Fin n => (j:ℕ)) then I else Iᶜ) with hcyldef
    set q : ℝ≥0∞ := P I with hq
    set r : ℝ≥0∞ := P Iᶜ with hr
    have hqr : q + r = 1 := by
      have h := measure_add_measure_compl (μ := P) hI_meas
      rw [measure_univ] at h
      simpa [hq, hr] using h
    have hpow : (∑ T : Finset (Fin n), q ^ T.card * r ^ (n - T.card)) ≤ 1 := by
      have hprod := Finset.prod_add (fun _ : Fin n => q) (fun _ : Fin n => r)
        (Finset.univ : Finset (Fin n))
      rw [hqr, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow] at hprod
      rw [← hprod.symm, ← Finset.powerset_univ]
      refine Finset.sum_le_sum (fun T _ => ?_)
      have hcard : (((Finset.univ : Finset (Fin n)) \ T)).card = n - T.card := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
      have hgoal : (∏ _i ∈ T, q) * (∏ _i ∈ (Finset.univ : Finset (Fin n)) \ T, r)
          = q ^ T.card * r ^ (n - T.card) := by
        rw [Finset.prod_const, Finset.prod_const, hcard]
      exact le_of_eq hgoal.symm
    have hchild := statopia_math_node_3597484326_59681b58
      (g := g) (c := c) (m := m) (M := M) (hc := hc) (hm := hm)
      (hg_meas := hg_meas) (hg_bound := hTM) (hg_support := hg_support)
      (t := t) (P := P) (hP := inferInstance) (p := p) (hp := hp_pos)
      (thetaStar := thetaStar) (hsep := hsep) (Rm := Rm) (hRm := hRm_eq)
      (hP_eq := hP_eq) (j := j)
    have hq_ge : ENNReal.ofReal (p j * (m * (2 * c))) ≤ q := by
      rw [hq]
      simpa only [hI] using hchild.1
    have htail : ∀ k : ℕ, 1 ≤ k →
        P (Set.Ioc (thetaStar j + c - u k) (thetaStar j + c)) ≤
          ENNReal.ofReal (p j * (M * u k)) := by
      intro k hk
      exact hchild.2 (u k) (le_of_lt (hu_pos k hk)) (hu_le k hk)
    have hcylprod : ∀ (S : Finset (Fin n)) (i : Fin n), i ∈ S →
        (iidLaw P) (cyl S i) = P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) *
          q ^ (S.card - 1) * r ^ (n - S.card) := by
      intro S i hiS
      set A : Set ℝ := Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c) with hAdef
      set T : Finset ℕ := S.image (fun i : Fin n => (i:ℕ)) with hTdef
      have hTsub : T ⊆ Finset.range n := by
        intro m hm
        rw [hTdef] at hm
        obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_range.mpr j'.isLt
      have hTcard : T.card = S.card := by
        rw [hTdef]
        exact Finset.card_image_of_injOn (fun a _ b _ hab => Fin.ext hab)
      have hiT : (i:ℕ) ∈ T := by
        rw [hTdef]
        exact Finset.mem_image.mpr ⟨i, hiS, rfl⟩
      have hmeas : ∀ m ∈ Finset.range n,
          MeasurableSet (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ) := by
        intro m _
        by_cases h1 : m = (i:ℕ)
        · rw [if_pos h1]
          rw [hAdef]
          exact measurableSet_Ioc
        · rw [if_neg h1]
          by_cases h2 : m ∈ T
          · rw [if_pos h2]; exact hI_meas
          · rw [if_neg h2]; exact hI_meas.compl
      have hstep1 : (iidLaw P) (cyl S i) = ∏ m ∈ Finset.range n,
          P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ) := by
        have hpi := Measure.infinitePi_pi (μ := fun _ : ℕ => P) (s := Finset.range n)
          (t := fun m => if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ) hmeas
        rw [hcyldef]
        exact hpi
      rw [hstep1]
      have hfilT : (Finset.range n).filter (fun m => m ∈ T) = T := by
        ext m
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hTsub h, h⟩⟩
      have hfilTc : (Finset.range n).filter (fun m => ¬ m ∈ T) = Finset.range n \ T := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_sdiff]
      have hfilT1 : T.filter (fun m => m = (i:ℕ)) = {(i:ℕ)} := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hiT, h⟩⟩
      have hfilT2 : T.filter (fun m => ¬ m = (i:ℕ)) = T.erase (i:ℕ) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      have hinter : T ∩ Finset.range n = T := by
        ext m
        simp only [Finset.mem_inter]
        exact ⟨fun h => h.1, fun h => ⟨h, hTsub h⟩⟩
      have h2nd : (∏ m ∈ Finset.range n \ T, P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ))
          = r ^ ((Finset.range n \ T).card) := by
        rw [← Finset.prod_const (s := Finset.range n \ T) (b := r)]
        refine Finset.prod_congr rfl (fun m hm => ?_)
        obtain ⟨-, hmT⟩ := Finset.mem_sdiff.mp hm
        rw [if_neg (fun h => hmT (by rw [h]; exact hiT)), if_neg hmT, hr]
      have h1st : (∏ m ∈ T, P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ))
          = P A * q ^ (S.card - 1) := by
        rw [← Finset.prod_filter_mul_prod_filter_not (s := T) (p := fun m => m = (i:ℕ))
          (f := fun m => P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ))]
        have herase : (∏ m ∈ T.erase (i:ℕ), P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ))
            = q ^ (T.erase (i:ℕ)).card := by
          rw [← Finset.prod_const (s := T.erase (i:ℕ)) (b := q)]
          refine Finset.prod_congr rfl (fun m hm => ?_)
          obtain ⟨hmi, hmT⟩ := Finset.mem_erase.mp hm
          rw [if_neg hmi, if_pos hmT, hq]
        rw [hfilT1, hfilT2, Finset.prod_singleton, if_pos rfl, herase,
          Finset.card_erase_of_mem hiT, hTcard]
      have hU : (Finset.range n \ T).card = n - S.card := by
        rw [Finset.card_sdiff, Finset.card_range, hinter, hTcard]
      rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.range n) (p := fun m => m ∈ T)
        (f := fun m => P (if m = (i:ℕ) then A else if m ∈ T then I else Iᶜ))]
      rw [hfilT, hfilTc, h1st, h2nd, hU]
    have hsub : {ω : ℕ → ℝ | Y ω < 1 / 2}
        ⊆ ⋃ (S : Finset (Fin n)), ⋃ (i : Fin n), (if i ∈ S then cyl S i else ∅) := by
      intro ω hω
      simp only [Set.mem_setOf_eq, hY] at hω
      by_cases hcard : (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card = 0
      · rw [if_pos hcard] at hω
        norm_num at hω
      · rw [if_neg hcard] at hω
        set C : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I) with hC
        have hCpos : 0 < C.card := Nat.pos_of_ne_zero hcard
        have hCne : C.Nonempty := Finset.card_pos.mp hCpos
        rw [dif_pos hCne] at hω
        have hX : (C.card : ℝ) * L * (c + thetaStar j - C.sup' hCne (fun i : Fin n => ω (i:ℕ)))
            < 1 / 2 := by
          by_contra hcon
          push_neg at hcon
          have h2 : (1/2:ℝ) ≤ min 1
              ((C.card : ℝ) * L * (c + thetaStar j - C.sup' hCne (fun i : Fin n => ω (i:ℕ)))) :=
            le_min (by norm_num) hcon
          linarith
        have hk0 : (0:ℝ) < (C.card : ℝ) := by exact_mod_cast hCpos
        have hu : (C.card : ℝ) * L * u C.card = 1/2 := by
          simp only [hudef]
          have hL0 : L ≠ 0 := ne_of_gt hLpos
          have hk0' : (C.card : ℝ) ≠ 0 := ne_of_gt hk0
          field_simp
        have hex : ∃ i ∈ C, thetaStar j + c - u C.card < ω (i:ℕ) := by
          by_contra hcon
          push_neg at hcon
          have hle : C.sup' hCne (fun i : Fin n => ω (i:ℕ)) ≤ thetaStar j + c - u C.card :=
            (Finset.sup'_le_iff hCne (fun i : Fin n => ω (i:ℕ))).mpr hcon
          have hstep : u C.card ≤ c + thetaStar j - C.sup' hCne (fun i : Fin n => ω (i:ℕ)) := by
            linarith
          have hLk : (0:ℝ) < (C.card : ℝ) * L := mul_pos hk0 hLpos
          have h2 : (1/2:ℝ) ≤ (C.card : ℝ) * L *
              (c + thetaStar j - C.sup' hCne (fun i : Fin n => ω (i:ℕ))) := by
            calc (1/2:ℝ) = (C.card : ℝ) * L * u C.card := hu.symm
              _ ≤ (C.card : ℝ) * L *
                    (c + thetaStar j - C.sup' hCne (fun i : Fin n => ω (i:ℕ))) :=
                  mul_le_mul_of_nonneg_left hstep (le_of_lt hLk)
          linarith
        obtain ⟨i, hiC, hi⟩ := hex
        refine Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
        rw [if_pos hiC]
        have hiI : ω (i:ℕ) ∈ I := (Finset.mem_filter.mp hiC).2
        have hiIcc : ω (i:ℕ) ≤ thetaStar j + c := by
          rw [hI] at hiI
          exact (Set.mem_Icc.mp hiI).2
        simp only [hcyldef, Set.mem_pi, Set.mem_Ioc]
        intro m hm
        have hmn : m < n := Finset.mem_range.mp hm
        by_cases hmi : m = (i:ℕ)
        · rw [if_pos hmi]
          rw [hmi]
          exact ⟨hi, hiIcc⟩
        · rw [if_neg hmi]
          by_cases hmT : m ∈ C.image (fun j : Fin n => (j:ℕ))
          · rw [if_pos hmT]
            obtain ⟨j', hj'C, hj'm⟩ := Finset.mem_image.mp hmT
            rw [← hj'm]
            exact (Finset.mem_filter.mp hj'C).2
          · rw [if_neg hmT]
            intro hmem
            exact hmT (Finset.mem_image.mpr ⟨⟨m, hmn⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, rfl⟩)
    show (iidLaw P) {ω : ℕ → ℝ | Y ω < 1 / 2} ≤ ENNReal.ofReal (C₀ * L⁻¹)
    set Sig : ℝ≥0∞ := ∑ S : Finset (Fin n), q ^ (S.card - 1) * r ^ (n - S.card) with hSig
    have hq_le : q ≤ 1 := by
      rw [hq]
      calc P I ≤ P Set.univ := measure_mono (Set.subset_univ I)
        _ = 1 := measure_univ
    have hterm : ∀ S : Finset (Fin n),
        q * (q ^ (S.card - 1) * r ^ (n - S.card)) ≤ q ^ S.card * r ^ (n - S.card) := by
      intro S
      by_cases hc : S.card = 0
      · rw [hc]
        simp only [Nat.sub_zero, Nat.zero_sub, pow_zero, one_mul]
        calc q * r ^ n ≤ 1 * r ^ n := mul_le_mul_right' hq_le _
          _ = r ^ n := one_mul _
      · have hS1 : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hc
        have heq : q * (q ^ (S.card - 1) * r ^ (n - S.card))
            = q ^ S.card * r ^ (n - S.card) := by
          have hpoweq : q ^ S.card = q * q ^ (S.card - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hS1]
            rw [pow_succ']
          rw [hpoweq, mul_assoc]
        exact le_of_eq heq
    have hsum_le : q * Sig ≤ 1 := by
      rw [hSig, Finset.mul_sum]
      calc (∑ S : Finset (Fin n), q * (q ^ (S.card - 1) * r ^ (n - S.card)))
          ≤ ∑ S : Finset (Fin n), q ^ S.card * r ^ (n - S.card) :=
            Finset.sum_le_sum (fun S _ => hterm S)
        _ ≤ 1 := hpow
    have h2 : ∀ S : Finset (Fin n),
        (∑ i : Fin n, (iidLaw P) (if i ∈ S then cyl S i else ∅))
          ≤ (S.card : ℝ≥0∞) *
            (P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card)) := by
      intro S
      have hfilS : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S) = S := by
        ext i
        simp
      calc (∑ i : Fin n, (iidLaw P) (if i ∈ S then cyl S i else ∅))
          = ∑ i : Fin n, (if i ∈ S then (iidLaw P) (cyl S i) else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            by_cases hi : i ∈ S
            · rw [if_pos hi, if_pos hi]
            · rw [if_neg hi, if_neg hi]
              simp
        _ ≤ ∑ i : Fin n, (if i ∈ S then
              P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card)
            else 0) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            by_cases hi : i ∈ S
            · rw [if_pos hi, if_pos hi]
              exact le_of_eq (hcylprod S i hi)
            · rw [if_neg hi, if_neg hi]
        _ = (S.card : ℝ≥0∞) *
            (P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card)) := by
            rw [← Finset.sum_filter (s := (Finset.univ : Finset (Fin n))) (p := fun i => i ∈ S)
              (f := fun _ => P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card))]
            rw [hfilS, Finset.sum_const, nsmul_eq_mul]
    have h3 : (∑ S : Finset (Fin n), (S.card : ℝ≥0∞) *
          (P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card)))
        ≤ ENNReal.ofReal (p j * (M / (2 * L))) * Sig := by
      rw [hSig, Finset.mul_sum]
      refine Finset.sum_le_sum (fun S _ => ?_)
      by_cases hc : S.card = 0
      · rw [hc]
        simp
      · have hS1 : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hc
        have hk0 : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
        have hb := htail S.card hS1
        have hreal : (S.card : ℝ) * (p j * (M * u S.card)) = p j * (M / (2 * L)) := by
          simp only [hudef]
          have hk0' : (S.card : ℝ) ≠ 0 := ne_of_gt hk0
          have hL0 : L ≠ 0 := ne_of_gt hLpos
          field_simp
        have hkey : (S.card : ℝ≥0∞) * P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c))
            ≤ ENNReal.ofReal (p j * (M / (2 * L))) := by
          calc (S.card : ℝ≥0∞) * P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c))
              ≤ (S.card : ℝ≥0∞) * ENNReal.ofReal (p j * (M * u S.card)) :=
                mul_le_mul_left' hb _
            _ = ENNReal.ofReal ((S.card : ℝ) * (p j * (M * u S.card))) := by
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (S.card))]
            _ = ENNReal.ofReal (p j * (M / (2 * L))) := by rw [hreal]
        calc (S.card : ℝ≥0∞) *
              (P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card))
            = ((S.card : ℝ≥0∞) * P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)))
                * q ^ (S.card - 1) * r ^ (n - S.card) := by ring
          _ ≤ ENNReal.ofReal (p j * (M / (2 * L))) * q ^ (S.card - 1) * r ^ (n - S.card) := by
              gcongr
          _ = ENNReal.ofReal (p j * (M / (2 * L))) * (q ^ (S.card - 1) * r ^ (n - S.card)) := by ring
    have h4 : ENNReal.ofReal (p j * (M / (2 * L))) * Sig ≤ ENNReal.ofReal (C₀ * L⁻¹) := by
      have h2cm : (0:ℝ) < 2 * c * m := by nlinarith
      have hMLpos : (0:ℝ) < M / (2 * L) := by
        have h2L : (0:ℝ) < 2 * L := by linarith
        exact div_pos hMpos h2L
      have hSp : ENNReal.ofReal (p j) * Sig ≤ ENNReal.ofReal (1 / (2 * c * m)) := by
        have h2cm_ne : ENNReal.ofReal (2 * c * m) ≠ 0 := by
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact h2cm
        have h2cm_top : ENNReal.ofReal (2 * c * m) ≠ ⊤ := ENNReal.ofReal_ne_top
        rw [← ENNReal.mul_le_mul_iff_left h2cm_ne h2cm_top]
        have hrhs : ENNReal.ofReal (1 / (2 * c * m)) * ENNReal.ofReal (2 * c * m) = 1 := by
          rw [← ENNReal.ofReal_mul (le_of_lt (by positivity : (0:ℝ) < 1 / (2 * c * m)))]
          have hr : 1 / (2 * c * m) * (2 * c * m) = 1 := by
            rw [one_div, inv_mul_cancel₀ (ne_of_gt h2cm)]
          rw [hr, ENNReal.ofReal_one]
        rw [hrhs]
        have hlp : ENNReal.ofReal (p j) * ENNReal.ofReal (2 * c * m)
            = ENNReal.ofReal (p j * (2 * c * m)) :=
          (ENNReal.ofReal_mul (le_of_lt (hp_pos j))).symm
        have hp2 : ENNReal.ofReal (p j * (2 * c * m)) ≤ q := by
          have hh := hq_ge
          rwa [show p j * (m * (2 * c)) = p j * (2 * c * m) from by ring] at hh
        calc (ENNReal.ofReal (p j) * Sig) * ENNReal.ofReal (2 * c * m)
            = (ENNReal.ofReal (p j) * ENNReal.ofReal (2 * c * m)) * Sig := by ring
          _ = ENNReal.ofReal (p j * (2 * c * m)) * Sig := by rw [hlp]
          _ ≤ q * Sig := mul_le_mul_right' hp2 _
          _ ≤ 1 := hsum_le
      have hYeq : ENNReal.ofReal (p j * (M / (2 * L)))
          = ENNReal.ofReal (M / (2 * L)) * ENNReal.ofReal (p j) := by
        rw [ENNReal.ofReal_mul (le_of_lt (hp_pos j))]
        ring
      calc ENNReal.ofReal (p j * (M / (2 * L))) * Sig
          = ENNReal.ofReal (M / (2 * L)) * (ENNReal.ofReal (p j) * Sig) := by
            rw [hYeq]; ring
        _ ≤ ENNReal.ofReal (M / (2 * L)) * ENNReal.ofReal (1 / (2 * c * m)) :=
            mul_le_mul_left' hSp _
        _ = ENNReal.ofReal (C₀ * L⁻¹) := by
            rw [← ENNReal.ofReal_mul (le_of_lt hMLpos), hC₀]
            congr 1
            field_simp
            ring
    have h1 : (iidLaw P) {ω : ℕ → ℝ | Y ω < 1 / 2}
        ≤ ∑ S : Finset (Fin n), ∑ i : Fin n, (iidLaw P) (if i ∈ S then cyl S i else ∅) := by
      refine le_trans (measure_mono hsub) ?_
      refine le_trans (measure_iUnion_le _) ?_
      rw [tsum_fintype]
      refine Finset.sum_le_sum (fun S _ => ?_)
      refine le_trans (measure_iUnion_le _) ?_
      rw [tsum_fintype]
    calc (iidLaw P) {ω : ℕ → ℝ | Y ω < 1 / 2}
        ≤ ∑ S : Finset (Fin n), ∑ i : Fin n, (iidLaw P) (if i ∈ S then cyl S i else ∅) := h1
      _ ≤ ∑ S : Finset (Fin n), (S.card : ℝ≥0∞) *
            (P (Set.Ioc (thetaStar j + c - u S.card) (thetaStar j + c)) * q ^ (S.card - 1) * r ^ (n - S.card)) :=
          Finset.sum_le_sum (fun S _ => h2 S)
      _ ≤ ENNReal.ofReal (p j * (M / (2 * L))) * Sig := h3
      _ ≤ ENNReal.ofReal (C₀ * L⁻¹) := h4
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hmain
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hg0) ε hε
  refine ⟨max N1 (max N2 2), fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set S : Set (ℕ → ℝ) := {ω : ℕ → ℝ |
      (if (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card = 0 then (1 : ℝ)
        else min 1
          (((Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).card : ℝ)
            * (Real.log (n : ℝ)) ^ ((1 : ℝ) / (2 * (t : ℝ)))
            * (c + thetaStar j -
              (if h : (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).Nonempty
                then (Finset.univ.filter (fun i : Fin n => ω (i : ℕ) ∈ I)).sup' h
                  (fun i : Fin n => ω (i : ℕ))
                else thetaStar j)))) < 1 / 2} with hS
  have hlogpos : 0 < Real.log (n:ℝ) := by
    have h1 : (1:ℝ) < (n:ℝ) := by
      have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3
      linarith
    exact Real.log_pos h1
  have hLposn : 0 < (Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))) := Real.rpow_pos_of_pos hlogpos _
  have hcpos : 0 < C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹ :=
    mul_pos hC₀pos (inv_pos.mpr hLposn)
  have hle : (iidLaw P) S ≤
      ENNReal.ofReal (C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹) := by
    simpa [hS] using hN1 n hn1
  have hbound : ((iidLaw P) S).toReal ≤ C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹ := by
    calc ((iidLaw P) S).toReal
        ≤ (ENNReal.ofReal (C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹ :=
          ENNReal.toReal_ofReal (le_of_lt hcpos)
  have hd : C₀ * ((Real.log (n:ℝ)) ^ ((1:ℝ) / (2 * (t:ℝ))))⁻¹ < ε := by
    have h2 := hN2 n hn2
    rw [Real.dist_eq, sub_zero] at h2
    rwa [abs_of_nonneg (le_of_lt hcpos)] at h2
  have hfin : ((iidLaw P) S).toReal < ε := lt_of_le_of_lt hbound hd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  simpa [hS] using hfin
  /- @proof-region region.target-node.session.120ab4dc3b0a43c0 end -/

end Statlib.Imported
