import Mathlib
import Statlib.StatFoundation.Vocabulary.Conformal

open Statlib.StatFoundation.Vocabulary

namespace Statlib.Workspace.Conformal

theorem cqr_002_strict_lower_rank_event_cardinality_bound {m k : ℕ}
    (hm : 0 < m) (score : Fin m → ℝ) :
    (Finset.univ.filter (fun i : Fin m => k ≤ strictLowerScoreCount score i)).card ≤
      m - k := by
  classical
  let B : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => k ≤ strictLowerScoreCount score i)
  change B.card ≤ m - k
  by_cases hB : B.Nonempty
  · obtain ⟨i0, hi0B, hmin⟩ := Finset.exists_min_image B score hB
    have hi0_bad : k ≤ strictLowerScoreCount score i0 := by
      simpa [B] using hi0B
    let L : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => score j < score i0)
    have hL_card : L.card = strictLowerScoreCount score i0 := by
      simp [L, strictLowerScoreCount]
    have hkL : k ≤ L.card := by
      simpa [hL_card] using hi0_bad
    have hdisj : Disjoint L B := by
      rw [Finset.disjoint_left]
      intro j hjL hjB
      have hlt : score j < score i0 := by
        simpa [L] using hjL
      have hle : score i0 ≤ score j := hmin j hjB
      exact not_lt_of_ge hle hlt
    have hunion_le : (L ∪ B).card ≤ m := by
      calc
        (L ∪ B).card ≤ (Finset.univ : Finset (Fin m)).card := by
          apply Finset.card_le_card
          intro x _
          exact Finset.mem_univ x
        _ = m := by simp
    have hsum_le : B.card + L.card ≤ m := by
      have hcard_union : (L ∪ B).card = L.card + B.card :=
        Finset.card_union_of_disjoint hdisj
      omega
    have hk_m : k ≤ m := le_trans hkL (by
      calc
        L.card ≤ B.card + L.card := Nat.le_add_left L.card B.card
        _ ≤ m := hsum_le)
    rw [Nat.le_sub_iff_add_le hk_m]
    exact le_trans (Nat.add_le_add_left hkL B.card) hsum_le
  · have hB_empty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    simp [hB_empty]

end Statlib.Workspace.Conformal
