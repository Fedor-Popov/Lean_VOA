/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionUnivG

/-! # Lightweight defining local Weyl/fusion relation specifications

This module contains only the relation specification, its exact satisfaction
characterization and its actual universal source. Dimension and squeeze
statements remain in DeligneFusionUnivGSector.
-/

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.A2

noncomputable section

variable (S : DeligneSectorData)

/-- **The local Weyl and fusion relations of `W_loc(mθ)`** as a relation specification. -/
def lwSpec (m : ℕ) : RelSpec S.n where
  tails := {t | (∃ e r, S.raising e ∧ t = [(e, r)]) ∨ (∃ h r, S.cartan h ∧ 1 ≤ r ∧ t = [(h, r)]) ∨
    (∃ i, S.lowering i ∧ t = List.replicate (m * S.lowExp i + 1) (i, 0)) ∨
    (∃ x, S.fusion x ∧ t = [(x, m)]) ∨ (∃ h r, S.cartanN h ∧ 1 ≤ r ∧ t = [(h, r)])}
  eig := {q | (∃ h, S.cartan h ∧ q = (h, ((m * S.thetaH h : ℕ) : ℂ))) ∨
    (∃ h, S.cartanN h ∧ q = (h, -((m * S.thetaN h : ℕ) : ℂ)))}

theorem iterate_eq_wordOpG {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ} {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : CurrentModule f V) (x : Fin n) (w : V) :
    ∀ k : ℕ, (ρ.op x 0)^[k] w = wordOp ρ (List.replicate k (x, 0)) w
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply', iterate_eq_wordOpG ρ x w k]; rfl

/-- **`LocalWeylRelG` is `Sat (lwSpec S m)`.** -/
theorem localWeylRelG_iff {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)
    (w : V) (m : ℕ) : LocalWeylRelG S ρ w m ↔ Sat S.f ρ w (lwSpec S m) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro t (⟨e, r, he, rfl⟩ | ⟨hh, r, hc, hr, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ |
        ⟨hh, r, hc, hr, rfl⟩)
      · exact h.raising e he r
      · exact h.cartan_pos hh hc r hr
      · rw [← iterate_eq_wordOpG]; exact h.lowering i hi
      · exact h.fusion x hx
      · exact h.cartanN_pos hh hc r hr
    · rintro q (⟨hh, hc, rfl⟩ | ⟨hh, hc, rfl⟩)
      · exact h.cartan_zero hh hc
      · exact h.cartanN_zero hh hc
  · intro h
    exact
      { raising := fun e he r => h.tail [(e, r)] (Or.inl ⟨e, r, he, rfl⟩)
        cartan_pos := fun hh hc r hr => h.tail [(hh, r)] (Or.inr (Or.inl ⟨hh, r, hc, hr, rfl⟩))
        cartan_zero := fun hh hc => h.eig (hh, _) (Or.inl ⟨hh, hc, rfl⟩)
        lowering := fun i hi => by
          rw [iterate_eq_wordOpG]
          exact h.tail _ (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩)))
        fusion := fun x hx => h.tail [(x, m)] (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, rfl⟩))))
        cartanN_pos := fun hh hc r hr =>
          h.tail [(hh, r)] (Or.inr (Or.inr (Or.inr (Or.inr ⟨hh, r, hc, hr, rfl⟩))))
        cartanN_zero := fun hh hc => h.eig (hh, _) (Or.inr ⟨hh, hc, rfl⟩) }

/-- The generator of the universal `W_loc(mθ)`-type module satisfies `LocalWeylRelG`. -/
theorem univ_localWeylRelG (m : ℕ) :
    LocalWeylRelG S (univRepG S.f (lwSpec S m)) (wUG S.f (lwSpec S m)) m :=
  (localWeylRelG_iff S _ _ m).mpr (univG_sat S.f (lwSpec S m))

end
end VOA.DeligneAudit.UnivG

#print axioms VOA.DeligneAudit.UnivG.localWeylRelG_iff
#print axioms VOA.DeligneAudit.UnivG.univ_localWeylRelG
