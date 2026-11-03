/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp6

/-!
# Specialisation `s = r` (layer 7, generic part)

`diagS : A⟦r⟧⟦s⟧ → A⟦r⟧`, `∑ sᵏ fₖ(r) ↦ ∑ rᵏ fₖ(r)`, is a ring homomorphism (`diagHom`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries

open scoped BigOperators

noncomputable section

section Diag

variable {A : Type*} [CommRing A]

/-- `∑ sᵏ fₖ(r) ↦ ∑ rᵏ fₖ(r)`. -/
def diagS (G : PowerSeries (PowerSeries A)) : PowerSeries A :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), coeff (n - k) (coeff k G)

theorem coeff_diagS (G : PowerSeries (PowerSeries A)) (n : ℕ) :
    coeff n (diagS G) = ∑ k ∈ Finset.range (n + 1), coeff (n - k) (coeff k G) := coeff_mk _ _

/-- The coefficient as a sum over pairs `(k, e)` with `k + e = n`. -/
theorem coeff_diagS' (G : PowerSeries (PowerSeries A)) (n : ℕ) :
    coeff n (diagS G) = ∑ p ∈ Finset.antidiagonal n, coeff p.2 (coeff p.1 G) := by
  rw [coeff_diagS, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff b (coeff a G))]

theorem diagS_add (G H : PowerSeries (PowerSeries A)) : diagS (G + H) = diagS G + diagS H := by
  ext n : 1; simp [coeff_diagS, Finset.sum_add_distrib]

theorem diagS_one : diagS (1 : PowerSeries (PowerSeries A)) = 1 := by
  ext n : 1
  rw [coeff_diagS, Finset.sum_eq_single 0]
  · rcases n with _ | n <;> simp [coeff_one]
  · intro b _ hb; rw [coeff_one, if_neg hb, map_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

theorem diagS_mul (G H : PowerSeries (PowerSeries A)) : diagS (G * H) = diagS G * diagS H := by
  ext n : 1
  rw [coeff_diagS', coeff_mul]
  simp only [coeff_mul, map_sum, coeff_diagS', Finset.sum_mul_sum]
  simp_rw [← Finset.sum_product']
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨(x.2.1.1 + x.2.2.1, x.2.1.2 + x.2.2.2), ((x.2.1.1, x.2.2.1), (x.2.1.2, x.2.2.2))⟩)
    (fun y => ⟨(y.2.1.1 + y.2.2.1, y.2.1.2 + y.2.2.2), ((y.2.1.1, y.2.2.1), (y.2.1.2, y.2.2.2))⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, ⟨e, f⟩⟩⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_antidiagonal] at hx ⊢
    exact ⟨by omega, trivial, trivial⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, ⟨e, f⟩⟩⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_antidiagonal] at hx ⊢
    exact ⟨by omega, trivial, trivial⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, ⟨e, f⟩⟩⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_antidiagonal] at hx
    obtain ⟨-, h1, h2⟩ := hx
    subst h1; subst h2; rfl
  · rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, ⟨e, f⟩⟩⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_antidiagonal] at hx
    obtain ⟨-, h1, h2⟩ := hx
    subst h1; subst h2; rfl
  · rintro ⟨⟨a, b⟩, ⟨⟨c, d⟩, ⟨e, f⟩⟩⟩ _
    rfl

/-- `diagS` as a ring homomorphism. -/
def diagHom : PowerSeries (PowerSeries A) →+* PowerSeries A where
  toFun := diagS
  map_one' := diagS_one
  map_mul' := diagS_mul
  map_zero' := by ext n : 1; simp [coeff_diagS]
  map_add' := diagS_add

end Diag

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
