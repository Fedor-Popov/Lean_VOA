import VOA.DeligneAudit.DeligneFusionD1SiteGWeight

/-!
# Actual highest-weight and truncation relations of the new current site

All generator relations follow from existing sector tables and the weight
exclusion. No dimension theorem, Demazure identification, or fusion input is
used. The coordinate table's skew symmetry is a finite Lie-table fact.
-/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.DeligneSector

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)

include hskew in
theorem skew_self_zero (a c : Fin S.n) : S.f a a c = 0 := by
  have hz : (2 : ℂ) * S.f a a c = 0 := by linear_combination hskew a a c
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem theta_pair_ne_zero : S.f S.hθ S.c₀ S.c₀ ≠ 0 := by
  have he : S.f S.hθ S.c₀ S.c₀ = -(S.thetaH S.hθ : ℂ) := by
    simpa only [if_pos rfl] using S.cartan_table S.hθ S.hθ_cartan S.c₀
  rw [he]
  exact neg_ne_zero.mpr (by exact_mod_cast S.hθ_ne)

include hskew in
theorem htheta_ne_c0 : S.hθ ≠ S.c₀ := by
  intro he
  apply theta_pair_ne_zero S
  rw [he]
  exact skew_self_zero S hskew S.c₀ S.c₀

include hskew in
theorem raising_ne_c0 (e : Fin S.n) (he : S.raising e) : e ≠ S.c₀ := by
  intro heq
  subst e
  apply theta_pair_ne_zero S
  rw [hskew, S.raising_table S.c₀ he S.hθ, neg_zero]

include hskew in
theorem cartan_ne_c0 (h : Fin S.n) (hh : S.cartan h) : h ≠ S.c₀ := by
  intro heq
  subst h
  have hz : S.f S.c₀ S.hθ S.c₀ = 0 := by
    rw [S.cartan_table S.c₀ hh S.hθ, if_neg (htheta_ne_c0 S hskew)]
  apply theta_pair_ne_zero S
  rw [hskew, hz, neg_zero]

include hskew in
theorem cartanN_ne_c0 (h : Fin S.n) (hh : S.cartanN h) : h ≠ S.c₀ := by
  intro heq
  subst h
  have hz : S.f S.c₀ S.hθ S.c₀ = 0 := by
    rw [S.cartanN_table S.c₀ hh S.hθ, if_neg (htheta_ne_c0 S hskew)]
  apply theta_pair_ne_zero S
  rw [hskew, hz, neg_zero]

theorem oneOp_w_zero (c : Fin S.n) (hc : c ≠ S.c₀) : oneOp c (w S.c₀) = 0 := by
  simp [w, Pi.single_apply, hc, Ne.symm hc]

theorem zeroOp_raising (e : Fin S.n) (he : S.raising e) : zeroOp S.f e (w S.c₀) = 0 := by
  apply Prod.ext
  · change coOp S.f e (Pi.single S.c₀ 1) = 0
    funext y
    rw [coOp_apply]
    simp [slotA, Pi.single_apply, S.raising_table e he]
  · rfl

theorem zeroOp_cartan (h : Fin S.n) (hh : S.cartan h) :
    zeroOp S.f h (w S.c₀) = (S.thetaH h : ℂ) • w S.c₀ := by
  apply Prod.ext
  · change coOp S.f h (Pi.single S.c₀ 1) = (S.thetaH h : ℂ) • Pi.single S.c₀ 1
    funext y
    rw [coOp_apply]
    by_cases hy : y = S.c₀
    · subst y; simp [slotA, Pi.single_apply, S.cartan_table h hh]
    · simp [slotA, Pi.single_apply, S.cartan_table h hh, hy, Ne.symm hy]
  · simp [w]

theorem zeroOp_cartanN (h : Fin S.n) (hh : S.cartanN h) :
    zeroOp S.f h (w S.c₀) = -(S.thetaN h : ℂ) • w S.c₀ := by
  apply Prod.ext
  · change coOp S.f h (Pi.single S.c₀ 1) = -(S.thetaN h : ℂ) • Pi.single S.c₀ 1
    funext y
    rw [coOp_apply]
    by_cases hy : y = S.c₀
    · subst y; simp [slotA, Pi.single_apply, S.cartanN_table h hh]
    · simp [slotA, Pi.single_apply, S.cartanN_table h hh, hy, Ne.symm hy]
  · simp [w]

theorem site_raising (e : Fin S.n) (he : S.raising e) (r : ℕ) :
    (rep S.f S.jacobi hskew).op e r (w S.c₀) = 0 := by
  rcases r with _ | r
  · exact zeroOp_raising S e he
  · rcases r with _ | r
    · exact oneOp_w_zero S e (raising_ne_c0 S hskew e he)
    · rfl

theorem site_cartan_pos (h : Fin S.n) (hh : S.cartan h) (r : ℕ) (hr : 1 ≤ r) :
    (rep S.f S.jacobi hskew).op h r (w S.c₀) = 0 := by
  rcases r with _ | r
  · omega
  · rcases r with _ | r
    · exact oneOp_w_zero S h (cartan_ne_c0 S hskew h hh)
    · rfl

theorem site_cartanN_pos (h : Fin S.n) (hh : S.cartanN h) (r : ℕ) (hr : 1 ≤ r) :
    (rep S.f S.jacobi hskew).op h r (w S.c₀) = 0 := by
  rcases r with _ | r
  · omega
  · rcases r with _ | r
    · exact oneOp_w_zero S h (cartanN_ne_c0 S hskew h hh)
    · rfl

theorem site_truncation (x : Fin S.n) :
    (rep S.f S.jacobi hskew).op x (if x = S.c₀ then 2 else 1) (w S.c₀) = 0 := by
  split_ifs with hx
  · rfl
  · exact oneOp_w_zero S x hx

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.site_raising
#print axioms VOA.DeligneAudit.D1SiteG.site_truncation
