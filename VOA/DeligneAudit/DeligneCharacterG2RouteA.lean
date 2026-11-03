/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Route A for `G₂`, layer R1: the rational-function setting

`L = ℚ[X^±, Y^±, q^±]` (as `AddMonoidAlgebra ℚ (Fin 3 → ℤ)`, exponents `(a, b, c)` for `X^a Y^b q^c`, where
`X = z^{α₁}`, `Y = z^{α₂}`), `K = Frac L`.  Every operator of the route is built from
**monomial substitutions** `σ_M` (`M` an additive endomorphism of `ℤ³`, injective), extended to `K`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.G2RA

open AddMonoidAlgebra

noncomputable section

abbrev E3 := Fin 3 → ℤ
abbrev L := AddMonoidAlgebra ℚ E3
abbrev K := FractionRing L

/-- The monomial `X^a Y^b q^c` in `L`. -/
def monoL (v : E3) : L := single v 1

/-- The monomial in `K`. -/
def mono (v : E3) : K := algebraMap L K (monoL v)

theorem mono_add (u v : E3) : mono (u + v) = mono u * mono v := by
  simp [mono, monoL, single_mul_single, ← map_mul]

theorem mono_zero : mono (0 : E3) = 1 := by simp [mono, monoL, one_def]

theorem mono_ne_zero (v : E3) : mono v ≠ 0 := by
  intro h
  have h1 := mono_add v (-v)
  rw [add_neg_cancel, mono_zero, h, zero_mul] at h1
  exact one_ne_zero h1

/-- `1 - z^v ≠ 0` for `v ≠ 0`. -/
theorem one_sub_mono_ne_zero (v : E3) (hv : v ≠ 0) : (1 : K) - mono v ≠ 0 := by
  intro h
  have h1 : algebraMap L K (monoL 0) = algebraMap L K (monoL v) := by
    rw [← mono, ← mono, mono_zero]; exact (sub_eq_zero.mp h)
  have h2 := IsFractionRing.injective L K h1
  exact hv (Finsupp.single_left_injective one_ne_zero h2).symm

/-- Monomial substitution on `L`. -/
def substL (M : E3 →+ E3) : L →+* L := mapDomainRingHom ℚ M

theorem substL_injective (M : E3 →+ E3) (hM : Function.Injective M) :
    Function.Injective (substL M) :=
  Finsupp.mapDomain_injective hM

/-- Monomial substitution on `K`. -/
def subst (M : E3 →+ E3) (hM : Function.Injective M) : K →+* K :=
  IsLocalization.map K (substL M)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (substL_injective M hM))

theorem subst_mono (M : E3 →+ E3) (hM : Function.Injective M) (v : E3) :
    subst M hM (mono v) = mono (M v) := by
  rw [subst, mono, IsLocalization.map_eq]
  simp [substL, monoL, mono, mapDomainRingHom_apply, Finsupp.mapDomain_single]

end

end VOA.DeligneAudit.DeligneCharacter.G2RA
