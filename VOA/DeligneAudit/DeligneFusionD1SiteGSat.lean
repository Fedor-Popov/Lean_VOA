import VOA.DeligneAudit.DeligneFusionD1SiteGRelations
import VOA.DeligneAudit.DeligneFusionUnivG

/-!
# The explicit site satisfies the actual one-site presentation

All tails and eigenrelations are proved from the explicit coadjoint-plus-line
action, existing sector weight tables, Jacobi, and finite-table skew symmetry.
No Demazure realization or total-dimension input appears.
-/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.UnivG

noncomputable section

/-- The `k = 1`, theta cutoff `d = 2` presentation, kept in a light file.
Its tails and eigenrelations are precisely those of Ravinder's one-site
family; this definition avoids importing unrelated character computations. -/
def oneSiteSpec (S : DeligneSectorData) : RelSpec S.n where
  tails := {t | (∃ e r, S.raising e ∧ t = [(e, r)]) ∨
    (∃ h r, S.cartan h ∧ 1 ≤ r ∧ t = [(h, r)]) ∨
    (∃ i, S.lowering i ∧ t = List.replicate (S.lowExp i + 1) (i, 0)) ∨
    (∃ x, S.fusion x ∧ t = [(x, if x = S.c₀ then 2 else 1)]) ∨
    (∃ h r, S.cartanN h ∧ 1 ≤ r ∧ t = [(h, r)])}
  eig := {q | (∃ h, S.cartan h ∧ q = (h, (S.thetaH h : ℂ))) ∨
    (∃ h, S.cartanN h ∧ q = (h, -(S.thetaN h : ℂ)))}

private theorem iterate_word {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule f V) (x : Fin n) (v : V) :
    ∀ k : ℕ, (R.op x 0)^[k] v = wordOp R (List.replicate k (x, 0)) v
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply', iterate_word R x v k]
      rfl

theorem site_sat (S : DeligneSectorData)
    (hskew : ∀ a b c, S.f a b c = -S.f b a c) :
    Sat S.f (rep S.f S.jacobi hskew) (w S.c₀) (oneSiteSpec S) := by
  constructor
  · intro t ht
    rcases ht with ⟨e, r, he, rfl⟩ | ⟨h, r, hh, hr, rfl⟩ |
      ⟨i, hi, rfl⟩ | ⟨x, _, rfl⟩ | ⟨h, r, hh, hr, rfl⟩
    · exact site_raising S hskew e he r
    · exact site_cartan_pos S hskew h hh r hr
    · rw [← iterate_word]
      exact site_lowering_nil S i hi
    · exact site_truncation S hskew x
    · exact site_cartanN_pos S hskew h hh r hr
  · rintro _ (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩)
    · exact zeroOp_cartan S h hh
    · exact zeroOp_cartanN S h hh

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.site_sat
