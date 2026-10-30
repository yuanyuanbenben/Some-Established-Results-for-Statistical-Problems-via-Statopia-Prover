import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ExternalNodes.Node_bd6a8ff2ea70e2db0d42
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Vocabulary
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.ProvedNodes
import ProverJobs.job_paper_e9c0500526fe4a15b7473a5f9efc21ed.Base

namespace PaperProofTasks.job_paper_e9c0500526fe4a15b7473a5f9efc21ed

namespace Statlib.Imported
open _root_.Statlib
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
universe u₀ u₁

theorem paper_e9c0500526fe4a15b7473a5f9efc21ed :
    ∀ (δ a c0 alpha cvar ccirc eps0 Ccor : ℝ),
      0 < δ → δ < 1 / 2 →
      0 < a → a < 1 / 2 →
      0 < c0 → 0 < alpha → 0 < cvar → 0 < ccirc → ccirc < 1 →
      0 < eps0 → eps0 < 1 → 0 < Ccor →
      ∃ cII : ℝ, 0 < cII ∧
      
      ∀ (p : ℕ → ℕ), (∀ n, 1 ≤ p n) →
      ∀ (Om : ℕ → Type u₀) [mOm : ∀ n, MeasurableSpace.{u₀} (Om n)]
        (Pm : ∀ n, MeasureTheory.Measure.{u₀} (Om n)),
        (∀ n, IsProbabilityMeasure (Pm n)) →
      
      ∀ (muv : (n : ℕ) → Fin (p n) → ℝ)
        (S : (n : ℕ) → Matrix (Fin (p n)) (Fin (p n)) ℝ),
        (hSpsd : ∀ n, (S n).PosSemidef) →
      ∀ (Z : (n : ℕ) → Fin n → Om n → Fin (p n) → ℝ),
        
        (hZmeas : ∀ n i j, Measurable (fun om => Z n i om j)) →
      
      ∀ (X : (n : ℕ) → Fin n → Om n → Fin (p n) → ℝ),
        (hX : ∀ n i om j,
          X n i om j = muv n j + (sqrtCovMat (hSpsd n)).mulVec (Z n i om) j) →
        
        (hindep : ∀ n, iIndepFun (fun (i : Fin n) (om : Om n) => Z n i om) (Pm n)) →
        (hident : ∀ n (i i' : Fin n), IdentDistrib (Z n i) (Z n i') (Pm n) (Pm n)) →
        
        (hZmean : ∀ n (hn : 1 ≤ n) j, Integrable (fun om => Z n ⟨0, hn⟩ om j) (Pm n) ∧
          ∫ om, Z n ⟨0, hn⟩ om j ∂(Pm n) = 0) →
        
        (hZcov : ∀ n (hn : 1 ≤ n) i j,
          Integrable (fun om => Z n ⟨0, hn⟩ om i * Z n ⟨0, hn⟩ om j) (Pm n) ∧
            ∫ om, Z n ⟨0, hn⟩ om i * Z n ⟨0, hn⟩ om j ∂(Pm n) = if i = j then 1 else 0) →
        
        (hsubexp : ∀ n (hn : 1 ≤ n) (u : Fin (p n) → ℝ),
          Real.sqrt (∑ j : Fin (p n), u j ^ 2) = 1 →
            Statlib.StatFoundation.Vocabulary.orliczNorm 1
              (fun om => ∑ j : Fin (p n), u j * Z n ⟨0, hn⟩ om j) (Pm n)
              ≤ ENNReal.ofReal c0) →

        
        (hXmeas : ∀ n (hn : 1 ≤ n) j, Measurable (fun om => X n ⟨0, hn⟩ om j)) →
        
        (hvar : ∀ n (hn : 1 ≤ n) j,
          Integrable (fun om => (X n ⟨0, hn⟩ om j - muv n j) ^ 2) (Pm n) ∧
            ∫ om, (X n ⟨0, hn⟩ om j - muv n j) ^ 2 ∂(Pm n) = S n j j) →

        
        (hspos : ∀ n j, 0 < sdOf (S n) j) →
      
      ∀ (perm : ∀ n, Equiv.Perm (Fin (p n))),
        (hperm : ∀ n (i i' : Fin (p n)), i.1 ≤ i'.1 → sdOf (S n) (perm n i') ≤ sdOf (S n) (perm n i)) →
        
        
        (htail : ∀ n,
          (∀ j : Fin (p n), kIdx p a n ≤ j.1 + 1 →
            sdOf (S n) (perm n j) ≤ cvar * (((j.1 + 1 : ℕ) : ℝ)) ^ (-alpha)) ∧
          (∀ j : Fin (kIdx p a n),
            ccirc * (((j.1 + 1 : ℕ) : ℝ)) ^ (-alpha) ≤
              sdOf (S n) (perm n (posIn (pn := p n) (kIdx_le p a n) j)))) →

        
        (hcorr : ∀ n, ∀ i j : Fin (ellIdx p n), i ≠ j →
          Rcorr (S n) (perm n) (ellIdx p n) (ellIdx_le p n) i j ≤ 1 - eps0) →
        
        (hRpospsd : ∀ n, (Rpos (S n) (perm n) (ellIdx p n) (ellIdx_le p n)).PosSemidef) →
        
        (hRsum : ∀ n,
          ∑ i : Fin (ellIdx p n),
            ∑ j : Fin (ellIdx p n), (if (i : ℕ) < (j : ℕ) then
              Rpos (S n) (perm n) (ellIdx p n) (ellIdx_le p n) i j else 0)
            ≤ Ccor * (ellIdx p n : ℝ)) →
      
      ∀ (tau : ℕ → ℝ), (htau : ∀ n, 0 ≤ tau n ∧ tau n < 1) →
        (htau2 : ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
          ∀ n, n0 ≤ n → c ≤ (1 - tau n) * Real.sqrt (Real.log (n : ℝ))) →
      
      ∀ (Om' : ℕ → Type) [mOm' : ∀ n, MeasurableSpace (Om' n)] (Pm' : ∀ n, Measure (Om' n)),
        (∀ n, IsProbabilityMeasure (Pm' n)) →
      ∀ (G : (n : ℕ) → Om' n → Fin (p n) → ℝ),
        (hG : ∀ n, Measurable (G n)) →
        (hGlaw : ∀ n, Measure.map (G n) (Pm' n) = stdGaussianLaw (p n)) →
        
        ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n, n0 ≤ n →
          @IIn p a Om mOm Pm Om' mOm' Pm' X muv S hSpsd G tau perm n
            ≤ cII * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ)
:= by
  /- @proof-region region.root.6a3b72de6eef begin -/
  intro δ a c0 alpha cvar ccirc eps0 Ccor hδ hδ2 ha ha2 hc0 hα hcvar hccirc hccirc1 heps heps1 hCcor
  obtain ⟨CB, hCBpos, hCB⟩ := ExternalRevision_bb11d988567af52975f2aee092d3dde32f3d1f221c6808fdb6d1bca0ad00547c.citation
  refine ⟨CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3, ?_, ?_⟩
  · have h2 : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : (0 : ℝ) < 4 / Real.exp 1 := by positivity
    positivity
  · intro p hp Om mOm Pm hPm muv S hSpsd Z hZmeas X hX hindep hident hZmean hZcov hsubexp
      hXmeas hvar hspos perm hperm htail hcorr hRpospsd hRsum tau htau htau2 Om' mOm' Pm' hPm'
      G hG hGlaw
    obtain ⟨n1, hn1, hkbd⟩ :=
      (statopia_math_node_268850332_99045989 a ha ha2 p hp).2 δ hδ
    refine ⟨max 1 n1, le_max_left 1 n1, ?_⟩
    intro n hn
    have hn1' : 1 ≤ n := le_trans (le_max_left 1 n1) hn
    have hnn1 : n1 ≤ n := le_trans (le_max_right 1 n1) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
      linarith
    have hk7 : (kIdx p a n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ δ := hkbd n hnn1
    have hD3 : (0 : ℝ) < (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 := by
      have h2 : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
      have h4 : (0 : ℝ) < 4 / Real.exp 1 := by positivity
      positivity
    have hCd3 : (0 : ℝ) ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 :=
      le_of_lt (mul_pos hCBpos hD3)
    have hmain : IIn p a Om Pm Om' Pm' X muv S hSpsd G tau perm n
        ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
            * (kIdx p a n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      set k : ℕ := kIdx p a n with hkdef
      have hk1 : 1 ≤ k := by
        have hell1 : (1 : ℝ) ≤ (ellIdx p n : ℝ) :=
          le_trans (le_min (le_max_left (1 : ℝ) _) (by exact_mod_cast hp n)) (Nat.le_ceil _)
        have hkg : (1 : ℝ) ≤ (kIdx p a n : ℝ) :=
          le_trans (le_min (le_trans hell1 (le_max_left _ _)) (by exact_mod_cast hp n))
            (Nat.le_ceil _)
        exact_mod_cast hkg
      have hkp : k ≤ p n := kIdx_le p a n
      set D : Matrix (Fin k) (Fin k) ℝ :=
        Matrix.diagonal (fun l : Fin k => sdOf (S n) (perm n (posIn hkp l))) with hD
      set Pim : Matrix (Fin k) (Fin (p n)) ℝ :=
        Matrix.of (fun (l : Fin k) (m : Fin (p n)) =>
          if m = perm n (posIn hkp l) then (1 : ℝ) else 0) with hPim
      set Dpow : Matrix (Fin k) (Fin k) ℝ :=
        Matrix.diagonal (fun l : Fin k => (D l l) ^ (-(tau n))) with hDpow
      set Cmat : Matrix (Fin (p n)) (Fin k) ℝ :=
        sqrtCovMat (hSpsd n) * Matrix.transpose Pim * Dpow with hCmat
      set W : Submodule ℝ (Fin (p n) → ℝ) :=
        Submodule.span ℝ (Set.range (fun l : Fin k => (fun m : Fin (p n) => Cmat m l))) with hW
      set r : ℕ := Module.finrank ℝ W with hr
      obtain ⟨Q, hQorth, hQspan⟩ := statopia_math_node_542235460_c14e1d61 (p n) W
      set R : Matrix (Fin r) (Fin k) ℝ := Matrix.transpose Q * Cmat with hR
      obtain ⟨hr1, hrk, hQQ, hCmatEq, hCmatT, hmv, hCne⟩ :=
        statopia_math_node_176343912_26262eb8 (p n) k (hp n) hk1 hkp (S n) (hSpsd n) (hspos n)
          (tau n) (htau n).1 (htau n).2 (perm n) Q hQorth hQspan
      obtain ⟨hMrw, hMiff⟩ :=
        statopia_math_node_3886841519_02de1ee8 (p n) k (hp n) hk1 hkp (S n) (hSpsd n) (hspos n)
          (tau n) (htau n).1 (htau n).2 (perm n) Q hQorth hQspan
      set Zbar : Om n → (Fin (p n) → ℝ) :=
        fun om j => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Z n i om j with hZbar
      have hMvdot : ∀ (v : Fin (p n) → ℝ) (j0 : Fin (p n)),
          Matrix.mulVec (sqrtCovMat (hSpsd n)) v j0
            = ∑ m : Fin (p n), sqrtCovMat (hSpsd n) j0 m * v m := by
        intro v j0
        first
          | rfl
          | (simp only [Matrix.mulVec]; rfl)
      have hZbar' : ∀ om : Om n,
          Zbar om = fun j : Fin (p n) => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Z n i om j :=
        fun om => rfl
      have hSnVec : ∀ om : Om n,
          SnVec (X n) (muv n) om = Matrix.mulVec (sqrtCovMat (hSpsd n)) (Zbar om) := by
        intro om
        funext j
        have h1 : ∀ i : Fin n,
            X n i om j - muv n j
              = ∑ m : Fin (p n), sqrtCovMat (hSpsd n) j m * Z n i om m := by
          intro i
          rw [hX n i om j, add_sub_cancel_left, hMvdot]
        have h2 : (∑ i : Fin n, (X n i om j - muv n j))
            = ∑ i : Fin n, ∑ m : Fin (p n), sqrtCovMat (hSpsd n) j m * Z n i om m :=
          Finset.sum_congr rfl (fun i _ => h1 i)
        show (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, (X n i om j - muv n j)
            = Matrix.mulVec (sqrtCovMat (hSpsd n)) (Zbar om) j
        rw [h2, Finset.sum_comm, hMvdot, hZbar' om]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ => by ring))
      set Zs : Om n → (Fin r → ℝ) :=
        fun om => Matrix.mulVec (Matrix.transpose Q) (Zbar om) with hZs
      set Zt : Om' n → (Fin r → ℝ) :=
        fun om => Matrix.mulVec (Matrix.transpose Q) (G n om) with hZt
      set A : ℝ → Set (Fin r → ℝ) :=
        fun t => {x | ∀ l : Fin k, Matrix.mulVec (Matrix.transpose R) x l ≤ t} with hA
      have hMk : ∀ om : Om n,
          maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om)
            = (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk1⟩, Finset.mem_univ _⟩
                (fun l : Fin k => Matrix.mulVec (Matrix.transpose R) (Zs om) l) := by
        intro om
        rw [hSnVec om]
        exact hMrw (Zbar om)
      have hMk' : ∀ om : Om' n,
          maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om)
            = (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk1⟩, Finset.mem_univ _⟩
                (fun l : Fin k => Matrix.mulVec (Matrix.transpose R) (Zt om) l) := by
        intro om
        exact hMrw (G n om)
      have hMiffS : ∀ (t : ℝ) (om : Om n),
          maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om) ≤ t
            ↔ Zs om ∈ A t := by
        intro t om
        rw [hSnVec om]
        exact hMiff (Zbar om) t
      have hMiffT : ∀ (t : ℝ) (om : Om' n),
          maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om) ≤ t
            ↔ Zt om ∈ A t := by
        intro t om
        exact hMiff (G n om) t
      have hcoordmeas : ∀ (l : Fin k),
          Measurable (fun x : Fin r → ℝ => Matrix.mulVec (Matrix.transpose R) x l) := by
        intro l
        have h : (fun x : Fin r → ℝ => Matrix.mulVec (Matrix.transpose R) x l)
            = fun x => ∑ m : Fin r, Matrix.transpose R l m * x m := by
          funext x
          first
            | rfl
            | (simp only [Matrix.mulVec]; rfl)
        rw [h]
        exact Finset.measurable_sum _ (fun m _ => measurable_const.mul (measurable_pi_apply m))
      have hAmeas : ∀ t : ℝ, MeasurableSet (A t) := by
        intro t
        have hset : A t = ⋂ l : Fin k,
            {x : Fin r → ℝ | Matrix.mulVec (Matrix.transpose R) x l ≤ t} := by
          ext x
          simp only [A, Set.mem_setOf_eq, Set.mem_iInter]
        rw [hset]
        exact MeasurableSet.iInter (fun l => measurableSet_Iic.preimage (hcoordmeas l))
      have hAconv : ∀ t : ℝ, Convex ℝ (A t) := by
        intro t x hx y hy a b ha hb hab
        simp only [A, Set.mem_setOf_eq] at hx hy ⊢
        intro l
        have h1 : Matrix.mulVec (Matrix.transpose R) (a • x + b • y) l
            = a * Matrix.mulVec (Matrix.transpose R) x l
              + b * Matrix.mulVec (Matrix.transpose R) y l := by
          rw [Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_smul, Matrix.mulVec_smul,
            Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        rw [h1]
        have h2 : a * Matrix.mulVec (Matrix.transpose R) x l ≤ a * t :=
          mul_le_mul_of_nonneg_left (hx l) ha
        have h3 : b * Matrix.mulVec (Matrix.transpose R) y l ≤ b * t :=
          mul_le_mul_of_nonneg_left (hy l) hb
        have h4 : a * t + b * t = t := by
          rw [← add_mul, hab, one_mul]
        linarith [h2, h3, h4]
      have hZbarmeas : ∀ j : Fin (p n), Measurable (fun om => Zbar om j) := by
        intro j
        have h : (fun om => Zbar om j)
            = fun om => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Z n i om j := by
          funext om
          exact congrFun (hZbar' om) j
        rw [h]
        exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hZmeas n i j))
      have hZscoord : ∀ l : Fin r, Measurable (fun om => Zs om l) := by
        intro l
        have h : (fun om => Zs om l)
            = fun om => ∑ j : Fin (p n), Matrix.transpose Q l j * Zbar om j := by
          funext om
          first
            | rfl
            | (simp only [Zs, Matrix.mulVec]; rfl)
        rw [h]
        exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hZbarmeas j))
      have hZtcoord : ∀ l : Fin r, Measurable (fun om => Zt om l) := by
        intro l
        have h : (fun om => Zt om l)
            = fun om => ∑ j : Fin (p n), Matrix.transpose Q l j * G n om j := by
          funext om
          first
            | rfl
            | (simp only [Zt, Matrix.mulVec]; rfl)
        rw [h]
        exact Finset.measurable_sum _
          (fun j _ => measurable_const.mul ((measurable_pi_apply j).comp (hG n)))
      have hZsmeas : Measurable Zs := measurable_pi_iff.mpr hZscoord
      have hZtmeas : Measurable Zt := measurable_pi_iff.mpr hZtcoord
      have hMkmeas : Measurable
          (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om)) := by
        have hcomp : ∀ l : Fin k,
            Measurable (fun om => Matrix.mulVec (Matrix.transpose R) (Zs om) l) := by
          intro l
          have h : (fun om => Matrix.mulVec (Matrix.transpose R) (Zs om) l)
              = fun om => ∑ j : Fin r, Matrix.transpose R l j * Zs om j := by
            funext om
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          rw [h]
          exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hZscoord j))
        have hfun : (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om))
            = (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk1⟩, Finset.mem_univ _⟩
                (fun (l : Fin k) (om : Om n) => Matrix.mulVec (Matrix.transpose R) (Zs om) l) := by
          funext om
          rw [hMk om, Finset.sup'_apply]
        rw [hfun]
        exact Finset.measurable_sup' _ (fun l _ => hcomp l)
      have hMk'meas : Measurable
          (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om)) := by
        have hcomp : ∀ l : Fin k,
            Measurable (fun om => Matrix.mulVec (Matrix.transpose R) (Zt om) l) := by
          intro l
          have h : (fun om => Matrix.mulVec (Matrix.transpose R) (Zt om) l)
              = fun om => ∑ j : Fin r, Matrix.transpose R l j * Zt om j := by
            funext om
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          rw [h]
          exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hZtcoord j))
        have hfun : (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n)
              (StildeVec (hSpsd n) (G n) om))
            = (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk1⟩, Finset.mem_univ _⟩
                (fun (l : Fin k) (om : Om' n) => Matrix.mulVec (Matrix.transpose R) (Zt om) l) := by
          funext om
          rw [hMk' om, Finset.sup'_apply]
        rw [hfun]
        exact Finset.measurable_sup' _ (fun l _ => hcomp l)
      have hpt : ∀ t : ℝ,
          |((Measure.map
              (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om))
              (Pm n)) (Set.Iic t)).toReal
            - ((Measure.map
              (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om))
              (Pm' n)) (Set.Iic t)).toReal|
          ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (r : ℝ) ^ ((1 : ℝ) / 4)
              * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        intro t
        have hL : ((Measure.map
              (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om))
              (Pm n)) (Set.Iic t)).toReal
            = ((Pm n) {om : Om n |
                maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om) ≤ t}).toReal := by
          rw [Measure.map_apply hMkmeas measurableSet_Iic]
          rfl
        have hR : ((Measure.map
              (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om))
              (Pm' n)) (Set.Iic t)).toReal
            = ((Pm' n) {om : Om' n |
                maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om) ≤ t}).toReal := by
          rw [Measure.map_apply hMk'meas measurableSet_Iic]
          rfl
        have hsetS : {om : Om n |
              maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om) ≤ t}
            = Zs ⁻¹' (A t) := by
          ext om
          exact hMiffS t om
        have hsetT : {om : Om' n |
              maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om) ≤ t}
            = Zt ⁻¹' (A t) := by
          ext om
          exact hMiffT t om
        have hL2 : (Pm n) {om : Om n |
              maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om) ≤ t}
            = (Measure.map Zs (Pm n)) (A t) := by
          rw [hsetS, ← Measure.map_apply hZsmeas (hAmeas t)]
        have hR2 : (Pm' n) {om : Om' n |
              maxOverJ (perm n) k (sdOf (S n)) (tau n) (StildeVec (hSpsd n) (G n) om) ≤ t}
            = (Measure.map Zt (Pm' n)) (A t) := by
          rw [hsetT, ← Measure.map_apply hZtmeas (hAmeas t)]
        have hRlaw : (Measure.map Zt (Pm' n)) (A t) = (stdGaussianLaw r) (A t) := by
          haveI := hPm' n
          have h := statopia_math_node_2848356570_ec1c5090 (p n) r (hp n) hr1 Q hQorth
            (Om' n) (Pm' n) (G n) (hG n) (hGlaw n)
          rw [h]
        have hVmeas : ∀ (i : Fin n) (j : Fin r),
            Measurable (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) := by
          intro i j
          have h : (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n i om) j)
              = fun om => ∑ m : Fin (p n), Matrix.transpose Q j m * Z n i om m := by
            funext om
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          rw [h]
          exact Finset.measurable_sum _ (fun m _ => measurable_const.mul (hZmeas n i m))
        have hVsum : ∀ om : Om n,
            (fun j : Fin r => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n,
                Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) = Zs om := by
          intro om
          funext j
          have h1 : ∀ i : Fin n,
              Matrix.mulVec (Matrix.transpose Q) (Z n i om) j
                = ∑ m : Fin (p n), Matrix.transpose Q j m * Z n i om m := by
            intro i
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          have hL' : (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n,
                Matrix.mulVec (Matrix.transpose Q) (Z n i om) j
              = (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, ∑ m : Fin (p n),
                  Matrix.transpose Q j m * Z n i om m := by
            rw [Finset.sum_congr rfl (fun i _ => h1 i)]
          have hform : Zs om j = ∑ m : Fin (p n), Matrix.transpose Q j m * Zbar om m := by
            first
              | rfl
              | (simp only [Zs, Matrix.mulVec]; rfl)
          have hZbarstep : (∑ m : Fin (p n), Matrix.transpose Q j m * Zbar om m)
              = ∑ m : Fin (p n), Matrix.transpose Q j m
                  * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Z n i om m) :=
            Finset.sum_congr rfl (fun m _ => by rw [hZbar' om])
          have hstep : (∑ m : Fin (p n), Matrix.transpose Q j m
                * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Z n i om m))
              = (Real.sqrt (n : ℝ))⁻¹ * ∑ m : Fin (p n), ∑ i : Fin n,
                  Matrix.transpose Q j m * Z n i om m := by
            simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i _ => by ring))
          have hR' : Zs om j = (Real.sqrt (n : ℝ))⁻¹ * ∑ m : Fin (p n), ∑ i : Fin n,
                Matrix.transpose Q j m * Z n i om m := by
            rw [hform, hZbarstep, hstep]
          rw [hL', hR', Finset.sum_comm]
        have hWmap : Measure.map (fun om => fun j : Fin r => (Real.sqrt (n : ℝ))⁻¹ *
              ∑ i : Fin n, Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) (Pm n)
            = Measure.map Zs (Pm n) := by
          rw [show (fun om => fun j : Fin r => (Real.sqrt (n : ℝ))⁻¹ *
              ∑ i : Fin n, Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) = Zs
            from funext hVsum]
        have hQcol : ∀ l : Fin r, Real.sqrt (∑ j : Fin (p n), (Q j l) ^ 2) = 1 := by
          intro l
          have h1 : ∑ j : Fin (p n), Q j l * Q j l = 1 := by
            have h := congrFun (congrFun hQorth l) l
            simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h
          rw [show (∑ j : Fin (p n), (Q j l) ^ 2) = ∑ j : Fin (p n), Q j l * Q j l from by
            simp only [sq]]
          rw [h1, Real.sqrt_one]
        have hsubexpQ : ∀ l : Fin r, Statlib.StatFoundation.Vocabulary.orliczNorm 1
            (fun om => ∑ j : Fin (p n), Q j l * Z n ⟨0, hn1'⟩ om j) (Pm n)
            ≤ ENNReal.ofReal c0 :=
          fun l => hsubexp n hn1' (fun j => Q j l) (hQcol l)
        have hmulVec_meas : Measurable
            (fun v : Fin (p n) → ℝ => Matrix.mulVec (Matrix.transpose Q) v) := by
          refine measurable_pi_iff.mpr (fun l => ?_)
          have h : (fun v : Fin (p n) → ℝ => Matrix.mulVec (Matrix.transpose Q) v l)
              = fun v => ∑ j : Fin (p n), Matrix.transpose Q l j * v j := by
            funext v
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          rw [h]
          exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
        have hVindep : iIndepFun (fun (i : Fin n) (om : Om n) =>
            fun j : Fin r => Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) (Pm n) := by
          have h := (hindep n).comp
            (fun (_ : Fin n) (v : Fin (p n) → ℝ) => Matrix.mulVec (Matrix.transpose Q) v)
            (fun (_ : Fin n) => hmulVec_meas)
          simpa using h
        have hVident : ∀ i i' : Fin n,
            IdentDistrib (fun om => fun j : Fin r =>
                Matrix.mulVec (Matrix.transpose Q) (Z n i om) j)
              (fun om => fun j : Fin r =>
                Matrix.mulVec (Matrix.transpose Q) (Z n i' om) j) (Pm n) (Pm n) := by
          intro i i'
          have h := (hident n i i').comp hmulVec_meas
          simpa using h
        have hVmean : ∀ j : Fin r,
            Integrable (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j) (Pm n) ∧
              ∫ om, Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j ∂(Pm n) = 0 := by
          intro j
          have hfun : (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j)
              = fun om => ∑ m : Fin (p n), Matrix.transpose Q j m * Z n ⟨0, hn1'⟩ om m := by
            funext om
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          have hcoord : ∀ m : Fin (p n),
              Integrable (fun om => Matrix.transpose Q j m * Z n ⟨0, hn1'⟩ om m) (Pm n) :=
            fun m => ((hZmean n hn1' m).1).const_mul (Matrix.transpose Q j m)
          have hint : Integrable (fun om => ∑ m : Fin (p n),
              Matrix.transpose Q j m * Z n ⟨0, hn1'⟩ om m) (Pm n) :=
            MeasureTheory.integrable_finset_sum _ (fun m _ => hcoord m)
          refine ⟨?_, ?_⟩
          · rw [hfun]
            exact hint
          · rw [hfun, MeasureTheory.integral_finset_sum _ (fun m _ => hcoord m)]
            refine Finset.sum_eq_zero (fun m _ => ?_)
            rw [MeasureTheory.integral_const_mul, (hZmean n hn1' m).2, mul_zero]
        have hVcov : ∀ p q : Fin r,
            Integrable (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) p
                * Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) q) (Pm n) ∧
              ∫ om, Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) p
                * Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) q ∂(Pm n)
                = if p = q then 1 else 0 := by
          intro pp qq
          have hunfold : ∀ (s : Fin r) (om : Om n),
              Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) s
                = ∑ m : Fin (p n), Matrix.transpose Q s m * Z n ⟨0, hn1'⟩ om m := by
            intro s om
            first
              | rfl
              | (simp only [Matrix.mulVec]; rfl)
          have hprod : ∀ om : Om n,
              Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) pp
                  * Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) qq
                = ∑ m : Fin (p n), ∑ m' : Fin (p n),
                    (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                      * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m') := by
            intro om
            rw [hunfold pp om, hunfold qq om, Finset.sum_mul_sum]
            exact Finset.sum_congr rfl (fun m _ =>
              Finset.sum_congr rfl (fun m' _ => by ring))
          have hterm : ∀ m m' : Fin (p n),
              Integrable (fun om => (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m')) (Pm n) :=
            fun m m' => ((hZcov n hn1' m m').1).const_mul _
          have hinner : ∀ m : Fin (p n),
              Integrable (fun om => ∑ m' : Fin (p n),
                (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                  * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m')) (Pm n) :=
            fun m => MeasureTheory.integrable_finset_sum _ (fun m' _ => hterm m m')
          have hval : ∀ m m' : Fin (p n),
              (∫ om, (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                  * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m') ∂(Pm n))
                = (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                  * (if m = m' then (1 : ℝ) else 0) := by
            intro m m'
            rw [MeasureTheory.integral_const_mul, (hZcov n hn1' m m').2]
          refine ⟨?_, ?_⟩
          · rw [show (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) pp
                  * Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) qq)
                  = fun om => ∑ m : Fin (p n), ∑ m' : Fin (p n),
                      (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                        * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m')
                from funext hprod]
            exact MeasureTheory.integrable_finset_sum _ (fun m _ => hinner m)
          · rw [show (fun om => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) pp
                  * Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) qq)
                  = fun om => ∑ m : Fin (p n), ∑ m' : Fin (p n),
                      (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                        * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m')
                from funext hprod]
            rw [MeasureTheory.integral_finset_sum _ (fun m _ => hinner m)]
            have hsingle : ∀ m : Fin (p n),
                (∫ om, ∑ m' : Fin (p n),
                  (Matrix.transpose Q pp m * Matrix.transpose Q qq m')
                    * (Z n ⟨0, hn1'⟩ om m * Z n ⟨0, hn1'⟩ om m') ∂(Pm n))
                  = Matrix.transpose Q pp m * Matrix.transpose Q qq m := by
              intro m
              rw [MeasureTheory.integral_finset_sum _ (fun m' _ => hterm m m')]
              rw [Finset.sum_congr rfl (fun m' _ => hval m m')]
              rw [Finset.sum_congr rfl (fun m' _ => by rw [mul_ite, mul_one, mul_zero])]
              rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ m)]
            rw [Finset.sum_congr rfl (fun m _ => hsingle m)]
            simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using
              congrFun (congrFun hQorth pp) qq
        haveI := hPm n
        obtain ⟨h3mem, h3bound⟩ := statopia_math_node_412305318_6575e435 (p n) r k hr1 hrk
          (Om n) (Pm n) (Z n ⟨0, hn1'⟩) (fun j => hZmeas n ⟨0, hn1'⟩ j) Q hQorth c0 hc0 hsubexpQ
        have hpow3 : ∀ (v : Fin r → ℝ), (∑ j : Fin r, v j ^ 2) ^ ((3 : ℝ) / 2)
            = (Real.sqrt (∑ j : Fin r, v j ^ 2)) ^ 3 := by
          intro v
          have hv : (0 : ℝ) ≤ ∑ j : Fin r, v j ^ 2 :=
            Finset.sum_nonneg (fun j _ => sq_nonneg (v j))
          rcases eq_or_lt_of_le hv with h0 | hpos
          · rw [← h0, Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0), Real.sqrt_zero]
            norm_num
          · rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by norm_num, Real.rpow_add hpos,
              Real.rpow_one, ← Real.sqrt_eq_rpow,
              show (Real.sqrt (∑ j : Fin r, v j ^ 2)) ^ 3
                = (Real.sqrt (∑ j : Fin r, v j ^ 2)) ^ 2
                  * Real.sqrt (∑ j : Fin r, v j ^ 2) from by ring,
              Real.sq_sqrt hv]
        have hthird : ∫ om, (∑ j : Fin r,
              (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j) ^ 2) ^ ((3 : ℝ) / 2)
              ∂(Pm n)
            ≤ (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2) := by
          simpa only [hpow3] using h3bound
        have hthird_int : Integrable (fun om => (∑ j : Fin r,
              (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j) ^ 2) ^ ((3 : ℝ) / 2))
            (Pm n) := by
          have h3mem3 : MemLp (fun om => Real.sqrt (∑ l : Fin r,
              (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) l) ^ 2)) 3 (Pm n) :=
            h3mem.mono_exponent (p := (3 : ℝ≥0∞)) (by norm_num)
          have hint3 : Integrable (fun om => ‖Real.sqrt (∑ l : Fin r,
              (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) l) ^ 2)‖ ^ 3) (Pm n) :=
            h3mem3.integrable_norm_pow (p := 3) (by norm_num)
          have hfe : (fun om => (∑ j : Fin r,
                (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j) ^ 2) ^ ((3 : ℝ) / 2))
              = fun om => ‖Real.sqrt (∑ l : Fin r,
                  (Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) l) ^ 2)‖ ^ 3 := by
            funext om
            rw [hpow3 (fun j => Matrix.mulVec (Matrix.transpose Q) (Z n ⟨0, hn1'⟩ om) j),
              Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [hfe]
          exact hint3
        have hVmeasPi : ∀ i : Fin n, Measurable (fun om => fun j : Fin r =>
            Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) :=
          fun i => hmulVec_meas.comp (measurable_pi_iff.mpr (fun j => hZmeas n i j))
        have hVsumSmul : ∀ om : Om n,
            (Real.sqrt (n : ℝ))⁻¹ • (∑ i : Fin n, Matrix.mulVec (Matrix.transpose Q) (Z n i om))
              = Zs om := by
          intro om
          rw [show (Real.sqrt (n : ℝ))⁻¹ • (∑ i : Fin n,
                Matrix.mulVec (Matrix.transpose Q) (Z n i om))
              = (fun j : Fin r => (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n,
                  Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) from by
            funext j
            simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]]
          exact hVsum om
        have hpre : (Pm n) (Set.preimage (fun om => (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n,
              Matrix.mulVec (Matrix.transpose Q) (Z n i om)) (A t))
            = (Measure.map Zs (Pm n)) (A t) := by
          have hfe : (fun om => (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n,
              Matrix.mulVec (Matrix.transpose Q) (Z n i om)) = Zs := funext hVsumSmul
          rw [hfe, ← Measure.map_apply hZsmeas (hAmeas t)]
        have hB := hCB r n hr1 hn1' (Om n) (Pm n) (hPm n)
          (fun (i : Fin n) (om : Om n) (j : Fin r) =>
            Matrix.mulVec (Matrix.transpose Q) (Z n i om) j)
          hVmeasPi hVindep hVident hVmean hVcov hthird_int (A t) (hAmeas t) (hAconv t)
        have hLval : ((Measure.map Zs (Pm n)) (A t)).toReal
            = ((Measure.map
                (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n) (SnVec (X n) (muv n) om))
                (Pm n)) (Set.Iic t)).toReal := by
          rw [← hL2, ← hL]
        have hRval : ((stdGaussianLaw r) (A t)).toReal
            = ((Measure.map
                (fun om => maxOverJ (perm n) k (sdOf (S n)) (tau n)
                  (StildeVec (hSpsd n) (G n) om)) (Pm' n)) (Set.Iic t)).toReal := by
          rw [← hRlaw, ← hR2, ← hR]
        rw [hpre] at hB
        rw [show (Measure.pi (fun _ : Fin r => gaussianReal 0 1)) = stdGaussianLaw r from rfl] at hB
        rw [hLval, hRval] at hB
  
        refine hB.trans ?_
        have hCBnonneg : (0 : ℝ) ≤ CB * (r : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_nonneg hCBpos.le (Real.rpow_nonneg (by positivity) _)
        have hImono := mul_le_mul_of_nonneg_left hthird hCBnonneg
        have hstep1 : (CB * (r : ℝ) ^ ((1 : ℝ) / 4) * ∫ om, (∑ j : Fin r,
              ((fun (i : Fin n) (om : Om n) (j : Fin r) =>
                Matrix.mulVec (Matrix.transpose Q) (Z n i om) j) ⟨0, hn1'⟩ om j) ^ 2)
                ^ ((3 : ℝ) / 2)
              ∂(Pm n)) * (n : ℝ) ^ (-(1 : ℝ) / 2)
            ≤ (CB * (r : ℝ) ^ ((1 : ℝ) / 4)
                * ((2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2)))
                * (n : ℝ) ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hImono (Real.rpow_nonneg hnpos.le _)
        have hEq : (CB * (r : ℝ) ^ ((1 : ℝ) / 4)
              * ((2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((3 : ℝ) / 2)))
              * (n : ℝ) ^ (-(1 : ℝ) / 2)
            = CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (r : ℝ) ^ ((1 : ℝ) / 4)
              * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
          ring
        have hExpeq : CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
              * (r : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 : ℝ) / 2)
            = CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
              * (r : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num]
        exact hstep1.trans ((le_of_eq hEq).trans (le_of_eq hExpeq))
      have hsup : IIn p a Om Pm Om' Pm' X muv S hSpsd G tau perm n
          ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (r : ℝ) ^ ((1 : ℝ) / 4)
              * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        ciSup_le hpt
      have hrk7 : CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (r : ℝ) ^ ((1 : ℝ) / 4)
              * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((7 : ℝ) / 4)
              * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have hkpos : (0 : ℝ) < (k : ℝ) := by
          have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          linarith
        have hr4 : (r : ℝ) ^ ((1 : ℝ) / 4) ≤ (k : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrk) (by norm_num)
        have hsplit : (k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((3 : ℝ) / 2)
            = (k : ℝ) ^ ((7 : ℝ) / 4) := by
          rw [← Real.rpow_add hkpos,
            show (1 : ℝ) / 4 + (3 : ℝ) / 2 = (7 : ℝ) / 4 from by norm_num]
        have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hnpos.le _
        calc CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (r : ℝ) ^ ((1 : ℝ) / 4)
                * (k : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ))
            = (CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
                * ((r : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((3 : ℝ) / 2)))
                * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
                * ((k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ) ^ ((3 : ℝ) / 2)))
                * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ hn4
              refine mul_le_mul_of_nonneg_left ?_ hCd3
              exact mul_le_mul_of_nonneg_right hr4 (Real.rpow_nonneg (le_of_lt hkpos) _)
          _ = CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3 * (k : ℝ) ^ ((7 : ℝ) / 4)
                * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [hsplit]
      exact hsup.trans hrk7
    have hmono : CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
            * (kIdx p a n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
            * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
      have hpow : (n : ℝ) ^ δ * (n : ℝ) ^ (-(1 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
        rw [← Real.rpow_add hnpos]
        rw [show δ + -(1 / 2 : ℝ) = -(1 / 2 : ℝ) + δ from by ring]
      calc CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
              * (kIdx p a n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
              * (n : ℝ) ^ δ * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hk7 hCd3) (Real.rpow_nonneg hnpos.le _)
        _ = CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
              * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
            rw [mul_assoc, hpow]
    have hstep_final : IIn p a Om Pm Om' Pm' X muv S hSpsd G tau perm n
        ≤ CB * (2 ^ ((1 : ℝ) / 4) * (4 / Real.exp 1) * c0) ^ 3
            * (kIdx p a n : ℝ) ^ ((7 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := hmain
    exact hstep_final.trans hmono
  /- @proof-region region.root.6a3b72de6eef end -/

-- Paper root revision 5b7b32ab-4b5b-4916-a813-cdcb9709cffc

