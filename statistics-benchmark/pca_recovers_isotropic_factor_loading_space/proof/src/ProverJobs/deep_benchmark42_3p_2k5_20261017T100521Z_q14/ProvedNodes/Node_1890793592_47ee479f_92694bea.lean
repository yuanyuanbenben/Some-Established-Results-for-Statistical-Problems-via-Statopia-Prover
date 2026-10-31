import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Vocabulary
import ProverJobs.deep_benchmark42_3p_2k5_20261017T100521Z_q14.Base

open MeasureTheory Matrix

open MeasureTheory Matrix

set_option autoImplicit false in
theorem statopia_math_node_1890793592_47ee479f : ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d q : ℕ)
    (F : Ω → Fin q → ℝ)
    (epsilon : Ω → Fin d → ℝ)
    (hF_L2 : MemLp F 2 P)
    (heps_L2 : MemLp epsilon 2 P)
    (sigma : ℝ)
    (hFcov : ∀ k l : Fin q,
      ∫ ω, F ω k * F ω l ∂P = if k = l then 1 else 0)
    (hepscov : ∀ i j : Fin d,
      ∫ ω, epsilon ω i * epsilon ω j ∂P = if i = j then sigma ^ 2 else 0)
    (hcross : ∀ (k : Fin q) (j : Fin d),
      ∫ ω, F ω k * epsilon ω j ∂P = 0)
    (Lambda : Matrix (Fin d) (Fin q) ℝ)
    (mu : Fin d → ℝ),
    (fun (i j : Fin d) => ∫ ω,
        ((mu + Lambda *ᵥ F ω + epsilon ω) - mu) i *
          ((mu + Lambda *ᵥ F ω + epsilon ω) - mu) j ∂P)
      = Lambda * Matrix.transpose Lambda +
        sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  /- @proof-region region.target-node.session.d8eaeb352a0f9759 begin -/
  intro Ω _ P _ d q F epsilon hF_L2 heps_L2 sigma hFcov hepscov hcross Lambda mu
  ext i j
  have hpt : ∀ ω : Ω,
      ((mu + Lambda *ᵥ F ω + epsilon ω) - mu) = Lambda *ᵥ F ω + epsilon ω := by
    intro ω
    ext k
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  have hcongr : (fun ω => ((mu + Lambda *ᵥ F ω + epsilon ω) - mu) i *
        ((mu + Lambda *ᵥ F ω + epsilon ω) - mu) j)
      = fun ω => ((Lambda *ᵥ F ω) i + epsilon ω i) *
          ((Lambda *ᵥ F ω) j + epsilon ω j) := by
    funext ω
    rw [hpt ω]
    simp only [Pi.add_apply]
  rw [hcongr]
  let Y : Ω → Fin d → ℝ := fun ω => Lambda *ᵥ F ω
  change (∫ ω, (Y ω i + epsilon ω i) * (Y ω j + epsilon ω j) ∂P)
      = (Lambda * Matrix.transpose Lambda + sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i j
  have hY_eq : ∀ (ω : Ω) (i : Fin d), Y ω i = ∑ k, Lambda i k * F ω k := by
    intro ω i
    simp only [Y, Matrix.mulVec, dotProduct]
  have hF_coord : ∀ k : Fin q, MemLp (fun ω => F ω k) 2 P := fun k =>
    MeasureTheory.memLp_pi_iff.mp hF_L2 k
  have heps_coord : ∀ j : Fin d, MemLp (fun ω => epsilon ω j) 2 P := fun j =>
    MeasureTheory.memLp_pi_iff.mp heps_L2 j
  have hFF : ∀ k l : Fin q, Integrable (fun ω => F ω k * F ω l) P := by
    intro k l
    exact (hF_coord k).integrable_mul (hF_coord l)
  have hFe : ∀ (k : Fin q) (j : Fin d), Integrable (fun ω => F ω k * epsilon ω j) P := by
    intro k j
    exact (hF_coord k).integrable_mul (heps_coord j)
  have heF : ∀ (i : Fin d) (l : Fin q), Integrable (fun ω => epsilon ω i * F ω l) P := by
    intro i l
    exact (heps_coord i).integrable_mul (hF_coord l)
  have hee : ∀ i j : Fin d, Integrable (fun ω => epsilon ω i * epsilon ω j) P := by
    intro i j
    exact (heps_coord i).integrable_mul (heps_coord j)
  have hYY_expand : ∀ ω : Ω, Y ω i * Y ω j
      = ∑ k, ∑ l, (Lambda i k * Lambda j l) * (F ω k * F ω l) := by
    intro ω
    rw [hY_eq ω i, hY_eq ω j]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hYeps_expand : ∀ ω : Ω, Y ω i * epsilon ω j
      = ∑ k, Lambda i k * (F ω k * epsilon ω j) := by
    intro ω
    rw [hY_eq ω i]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hepsY_expand : ∀ ω : Ω, epsilon ω i * Y ω j
      = ∑ l, Lambda j l * (epsilon ω i * F ω l) := by
    intro ω
    rw [hY_eq ω j]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hYY_int : Integrable (fun ω => Y ω i * Y ω j) P := by
    have heq : (fun ω => Y ω i * Y ω j)
        = fun ω => ∑ k, ∑ l, (Lambda i k * Lambda j l) * (F ω k * F ω l) := by
      funext ω
      exact hYY_expand ω
    rw [heq]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ =>
      MeasureTheory.integrable_finset_sum _ (fun l _ =>
        (hFF k l).const_mul (Lambda i k * Lambda j l)))
  have hYeps_int : Integrable (fun ω => Y ω i * epsilon ω j) P := by
    have heq : (fun ω => Y ω i * epsilon ω j)
        = fun ω => ∑ k, Lambda i k * (F ω k * epsilon ω j) := by
      funext ω
      exact hYeps_expand ω
    rw [heq]
    exact MeasureTheory.integrable_finset_sum _ (fun k _ =>
      (hFe k j).const_mul (Lambda i k))
  have hepsY_int : Integrable (fun ω => epsilon ω i * Y ω j) P := by
    have heq : (fun ω => epsilon ω i * Y ω j)
        = fun ω => ∑ l, Lambda j l * (epsilon ω i * F ω l) := by
      funext ω
      exact hepsY_expand ω
    rw [heq]
    exact MeasureTheory.integrable_finset_sum _ (fun l _ =>
      (heF i l).const_mul (Lambda j l))
  have hYY_val : ∫ ω, Y ω i * Y ω j ∂P = ∑ k, Lambda i k * Lambda j k := by
    calc
      ∫ ω, Y ω i * Y ω j ∂P
          = ∫ ω, ∑ k, ∑ l, (Lambda i k * Lambda j l) * (F ω k * F ω l) ∂P := by
              congr 1
              funext ω
              exact hYY_expand ω
      _ = ∑ k, ∫ ω, ∑ l, (Lambda i k * Lambda j l) * (F ω k * F ω l) ∂P := by
              rw [MeasureTheory.integral_finset_sum]
              intro k hk
              exact MeasureTheory.integrable_finset_sum _ (fun l hl =>
                (hFF k l).const_mul (Lambda i k * Lambda j l))
      _ = ∑ k, ∑ l, ∫ ω, (Lambda i k * Lambda j l) * (F ω k * F ω l) ∂P := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [MeasureTheory.integral_finset_sum]
              intro l hl
              exact (hFF k l).const_mul (Lambda i k * Lambda j l)
      _ = ∑ k, ∑ l, (Lambda i k * Lambda j l) * (∫ ω, F ω k * F ω l ∂P) := by
              apply Finset.sum_congr rfl
              intro k hk
              apply Finset.sum_congr rfl
              intro l hl
              rw [MeasureTheory.integral_const_mul]
      _ = ∑ k, Lambda i k * Lambda j k := by
              apply Finset.sum_congr rfl
              intro k hk
              have hinner : ∀ l : Fin q,
                  (Lambda i k * Lambda j l) * (∫ ω, F ω k * F ω l ∂P)
                    = if k = l then Lambda i k * Lambda j k else 0 := by
                intro l
                rw [hFcov k l]
                by_cases h : k = l <;> simp [h]
              simp_rw [hinner]
              simp
  have hYeps_val : ∫ ω, Y ω i * epsilon ω j ∂P = 0 := by
    calc
      ∫ ω, Y ω i * epsilon ω j ∂P
          = ∫ ω, ∑ k, Lambda i k * (F ω k * epsilon ω j) ∂P := by
              congr 1
              funext ω
              exact hYeps_expand ω
      _ = ∑ k, ∫ ω, Lambda i k * (F ω k * epsilon ω j) ∂P := by
              rw [MeasureTheory.integral_finset_sum]
              intro k hk
              exact (hFe k j).const_mul (Lambda i k)
      _ = ∑ k, Lambda i k * (∫ ω, F ω k * epsilon ω j ∂P) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [MeasureTheory.integral_const_mul]
      _ = 0 := by
              simp [hcross]
  have hepsY_val : ∫ ω, epsilon ω i * Y ω j ∂P = 0 := by
    calc
      ∫ ω, epsilon ω i * Y ω j ∂P
          = ∫ ω, ∑ l, Lambda j l * (epsilon ω i * F ω l) ∂P := by
              congr 1
              funext ω
              exact hepsY_expand ω
      _ = ∑ l, ∫ ω, Lambda j l * (epsilon ω i * F ω l) ∂P := by
              rw [MeasureTheory.integral_finset_sum]
              intro l hl
              exact (heF i l).const_mul (Lambda j l)
      _ = ∑ l, Lambda j l * (∫ ω, epsilon ω i * F ω l ∂P) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [MeasureTheory.integral_const_mul]
      _ = 0 := by
              have hzero : ∀ l : Fin q, ∫ ω, epsilon ω i * F ω l ∂P = 0 := by
                intro l
                rw [show (∫ ω, epsilon ω i * F ω l ∂P) = ∫ ω, F ω l * epsilon ω i ∂P from by
                  congr 1
                  funext ω
                  ring]
                exact hcross l i
              simp [hzero]
  have hExp : ∀ ω : Ω, (Y ω i + epsilon ω i) * (Y ω j + epsilon ω j)
      = (Y ω i * Y ω j + Y ω i * epsilon ω j) +
          (epsilon ω i * Y ω j + epsilon ω i * epsilon ω j) := by
    intro ω
    ring
  have hIntegral :
      ∫ ω, (Y ω i + epsilon ω i) * (Y ω j + epsilon ω j) ∂P
        = ∑ k, Lambda i k * Lambda j k + (if i = j then sigma ^ 2 else 0) := by
    calc
      ∫ ω, (Y ω i + epsilon ω i) * (Y ω j + epsilon ω j) ∂P
          = ∫ ω, (Y ω i * Y ω j + Y ω i * epsilon ω j) +
              (epsilon ω i * Y ω j + epsilon ω i * epsilon ω j) ∂P := by
              congr 1
              funext ω
              exact hExp ω
      _ = ∫ ω, (Y ω i * Y ω j + Y ω i * epsilon ω j) ∂P
            + ∫ ω, (epsilon ω i * Y ω j + epsilon ω i * epsilon ω j) ∂P := by
              rw [MeasureTheory.integral_add
                (f := fun ω => Y ω i * Y ω j + Y ω i * epsilon ω j)
                (g := fun ω => epsilon ω i * Y ω j + epsilon ω i * epsilon ω j)
                (hYY_int.add hYeps_int) (hepsY_int.add (hee i j))]
      _ = (∫ ω, Y ω i * Y ω j ∂P + ∫ ω, Y ω i * epsilon ω j ∂P)
            + (∫ ω, epsilon ω i * Y ω j ∂P + ∫ ω, epsilon ω i * epsilon ω j ∂P) := by
              rw [MeasureTheory.integral_add
                (f := fun ω => Y ω i * Y ω j) (g := fun ω => Y ω i * epsilon ω j)
                hYY_int hYeps_int]
              rw [MeasureTheory.integral_add
                (f := fun ω => epsilon ω i * Y ω j) (g := fun ω => epsilon ω i * epsilon ω j)
                hepsY_int (hee i j)]
      _ = (∑ k, Lambda i k * Lambda j k + 0) + (0 + (if i = j then sigma ^ 2 else 0)) := by
              rw [hYY_val, hYeps_val, hepsY_val, hepscov i j]
      _ = ∑ k, Lambda i k * Lambda j k + (if i = j then sigma ^ 2 else 0) := by
              ring
  have hRHS : (Lambda * Matrix.transpose Lambda +
        sigma ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) i j
      = ∑ k, Lambda i k * Lambda j k + (if i = j then sigma ^ 2 else 0) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  rw [hIntegral, hRHS]
  /- @proof-region region.target-node.session.d8eaeb352a0f9759 end -/
