import VOA.DeligneAudit.DeligneFusionCVRectCommutative
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationOrder

/-!
# Reversed polynomial coefficient orders imply actual CV cutoff regions

Only coefficients inside the prescribed reflection degree are converted.
Higher coefficients vanish by the separate polynomial degree theorem;
their indices need not lie below that degree merely because the order
is below the excess function.
-/

namespace VOA.DeligneAudit.A2.CVRectCutoff

open VOA.DeligneAudit.CVPart CVFamily CVRectCommutative CVRectIntegrationOrder

theorem excess_add_clipped (ξ : List ℕ) (m : ℕ) :
    excess ξ m + clippedSum ξ m = ξ.length * m := by
  induction ξ with
  | nil => simp [excess, clippedSum]
  | cons a ξ ih =>
      have ha := Nat.sub_add_min_cancel m a
      simp only [excess, clippedSum, List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul] at ih ⊢
      omega

theorem multiplicity_pos {ξ : List ℕ} {m j : ℕ} (h : j < excess ξ m) : 1 ≤ m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  simp [hm0, excess] at h

theorem length_pos {ξ : List ℕ} {m j : ℕ} (h : j < excess ξ m) : 1 ≤ ξ.length := by
  cases ξ with
  | nil => simp [excess] at h
  | cons a ξ => simp

/-- A low reversed coefficient belongs to an actual rootwise CV vanishing
region. The reflection-degree hypothesis is necessary. -/
theorem excess_cv_region (r n e m j : ℕ)
    (hj : j < excess (parts r n e) m)
    (hdegree : j ≤ (r + n + e - 1) * m) :
    ∃ k, 1 + m * k + T k (parts r n e) ≤ (r + n + e - 1) * m - j + m := by
  have hm := multiplicity_pos hj
  have hN : 1 ≤ r + n + e := by
    simpa only [parts_length] using length_pos hj
  obtain ⟨k, hk⟩ := parts_region_optimizer r n e m hm
  have he := excess_add_clipped (parts r n e) m
  rw [parts_length] at he
  have hmul : (r + n + e - 1) * m + m = (r + n + e) * m := by
    calc
      (r + n + e - 1) * m + m = (r + n + e - 1 + 1) * m := by ring
      _ = (r + n + e) * m := by rw [Nat.sub_add_cancel hN]
  refine ⟨k, ?_⟩
  omega

end VOA.DeligneAudit.A2.CVRectCutoff

#print axioms VOA.DeligneAudit.A2.CVRectCutoff.excess_add_clipped
#print axioms VOA.DeligneAudit.A2.CVRectCutoff.excess_cv_region
