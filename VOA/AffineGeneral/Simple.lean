/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Virasoro
import VOA.AffineGeneral.Casimir
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.CartanCriterion

/-!
# The universal affine VOA of every simple Lie algebra

* `simpleData κ hinv hnd`: Lie data for a finite-dimensional simple complex Lie algebra with a
  nondegenerate invariant form, indexed by `Fin (finrank ℂ 𝔤)` (Mathlib's `finBasis`); the dual Coxeter
  number `h` is half the adjoint Casimir eigenvalue (`casimir_scalar`).
* `universalAffineVOA κ hinv hnd k hk : VertexOperatorAlgebra (vacuumSpace κ hinv k)` for `k + h ≠ 0`.
* `killingInvariant`, `killingAffineVOA`: the same with the Killing form.  Its nondegeneracy is automatic:
  `[IsSimple ℂ 𝔤]` gives `IsKilling` through Mathlib's Cartan criterion (`HasTrivialRadical.instIsKilling`).

No hypothesis beyond simplicity (and nondegeneracy of the chosen form) remains.
-/

namespace VOA.AffineGeneral

noncomputable section

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤] [LieAlgebra.IsSimple ℂ 𝔤]

/-- Lie data of a simple `𝔤` with a nondegenerate invariant form `κ`. -/
def simpleData (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) : LieData κ (Fin (Module.finrank ℂ 𝔤)) :=
  LieData.ofSimple hinv hnd (Module.finBasis ℂ 𝔤)

/-- **The universal affine VOA `V^k(𝔤)` of a simple Lie algebra**, for any nondegenerate invariant
form `κ` and non-critical level `k + h ≠ 0` (`h` = dual Coxeter number in the normalization of `κ`). -/
def universalAffineVOA (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    VertexOperatorAlgebra (AffineLie.vacuumSpace κ hinv k) :=
  affineVOA (simpleData 𝔤 κ hinv hnd) k hk

/-- Its central charge is `dim 𝔤 · k / (k + h)`. -/
theorem universalAffineVOA_centralCharge (κ : LinearMap.BilinForm ℂ 𝔤) (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (k : ℂ) (hk : k + (simpleData 𝔤 κ hinv hnd).h ≠ 0) :
    (universalAffineVOA 𝔤 κ hinv hnd k hk).centralCharge =
      (Module.finrank ℂ 𝔤 : ℂ) * k / (k + (simpleData 𝔤 κ hinv hnd).h) := by
  show (Fintype.card (Fin (Module.finrank ℂ 𝔤)) : ℂ) * k / _ = _
  rw [Fintype.card_fin]

-- Deprecated aliases
@[deprecated universalAffineVOA (since := "2026-10-28")]
alias simpleAffineVOA := universalAffineVOA
@[deprecated universalAffineVOA_centralCharge (since := "2026-10-28")]
alias simpleAffineVOA_centralCharge := universalAffineVOA_centralCharge

/-- The Killing form is symmetric and invariant in the sense of `AffineLie`. -/
theorem killingInvariant : (killingForm ℂ 𝔤).IsInvariant where
  symm x y := LieModule.traceForm_comm ℂ 𝔤 𝔤 x y
  invariant x y z := LieModule.traceForm_apply_lie_apply ℂ 𝔤 𝔤 x y z

/-- **`V^k(𝔤)` with the Killing form**, for every simple `𝔤`. -/
def killingAffineVOA (k : ℂ)
    (hk : k + (simpleData 𝔤 (killingForm ℂ 𝔤) (killingInvariant 𝔤)
      (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ 𝔤)).h ≠ 0) :
    VertexOperatorAlgebra (AffineLie.vacuumSpace (killingForm ℂ 𝔤) (killingInvariant 𝔤) k) :=
  universalAffineVOA 𝔤 (killingForm ℂ 𝔤) (killingInvariant 𝔤)
    (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ 𝔤) k hk

/-- **In the Killing normalization the adjoint Casimir is the identity: `h = 1/2`.**
Proof: `tr C = ∑ᵢ tr(ad bᵢ ∘ ad dᵢ) = ∑ᵢ Killing(bᵢ, dᵢ) = dim 𝔤`, while `C = 2h · id` has trace
`2h · dim 𝔤`. -/
theorem killing_h :
    (simpleData 𝔤 (killingForm ℂ 𝔤) (killingInvariant 𝔤)
      (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ 𝔤)).h = 1 / 2 := by
  set D := simpleData 𝔤 (killingForm ℂ 𝔤) (killingInvariant 𝔤)
    (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ 𝔤) with hD
  haveI : Nontrivial 𝔤 := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact LieAlgebra.IsSimple.non_abelian (R := ℂ) (L := 𝔤) ⟨fun x y => Subsingleton.elim _ _⟩
  have hC : casimirOp D.basis D.dual = (2 * D.h) • (1 : Module.End ℂ 𝔤) := by
    ext x
    rw [casimirOp_apply, D.casimir x]
    simp
  have htr1 : LinearMap.trace ℂ 𝔤 (casimirOp D.basis D.dual) = (Module.finrank ℂ 𝔤 : ℂ) := by
    rw [casimirOp, map_sum]
    have : ∀ i, LinearMap.trace ℂ 𝔤 (LieModule.toEnd ℂ 𝔤 𝔤 (D.basis i) * LieModule.toEnd ℂ 𝔤 𝔤 (D.dual i))
        = 1 := by
      intro i
      have h := D.pair i i
      rw [if_pos rfl] at h
      rw [← h]
      rfl
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have htr2 : LinearMap.trace ℂ 𝔤 (casimirOp D.basis D.dual) = 2 * D.h * Module.finrank ℂ 𝔤 := by
    rw [hC, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hpos : (Module.finrank ℂ 𝔤 : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := 𝔤)).ne'
  have : 2 * D.h * Module.finrank ℂ 𝔤 = 1 * Module.finrank ℂ 𝔤 := by rw [← htr2, htr1, one_mul]
  have h2 := mul_right_cancel₀ hpos this
  linear_combination h2 / 2

/-- **`V^k(𝔤)` for every simple `𝔤`, Killing normalization, explicit non-criticality `k ≠ -1/2`.**
(With `κ = λ · Killing` the dual Coxeter number becomes `1/(2λ)`; the standard normalization
`λ = 1/(2h∨)` gives `h = h∨`.) -/
def killingAffineVOA' (k : ℂ) (hk : k + 1 / 2 ≠ 0) :
    VertexOperatorAlgebra (AffineLie.vacuumSpace (killingForm ℂ 𝔤) (killingInvariant 𝔤) k) :=
  killingAffineVOA 𝔤 k (by rw [killing_h]; exact hk)

/-- Lie data for the form `Killing / (2 hv)`.  When `hv` is the dual Coxeter number of `𝔤` this is the
standard normalization (long roots of length 2), and `standardData_h` shows `h = hv`. -/
def standardData (hv : ℂ) (hhv : hv ≠ 0) :
    LieData ((2 * hv)⁻¹ • killingForm ℂ 𝔤) (Fin (Module.finrank ℂ 𝔤)) :=
  (simpleData 𝔤 (killingForm ℂ 𝔤) (killingInvariant 𝔤)
    (LieAlgebra.IsKilling.killingForm_nondegenerate ℂ 𝔤)).smulForm (2 * hv)⁻¹
    (inv_ne_zero (mul_ne_zero two_ne_zero hhv))

theorem standardData_h (hv : ℂ) (hhv : hv ≠ 0) :
    (standardData 𝔤 hv hhv).h = hv := by
  rw [standardData, LieData.smulForm_h, killing_h]
  field_simp

/-- **`V^k(𝔤)` in the normalization `κ = Killing/(2 hv)`, for `k + hv ≠ 0`.**  With `hv = h∨` this is the
universal affine VOA at level `k` in the standard normalization, e.g. at the Deligne levels
`k = -h∨/6 - 1`. -/
def standardAffineVOA (hv : ℂ) (hhv : hv ≠ 0) (k : ℂ) (hk : k + hv ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData 𝔤 hv hhv) k) :=
  affineVOA (standardData 𝔤 hv hhv) k (by rw [standardData_h]; exact hk)

theorem standardAffineVOA_centralCharge (hv : ℂ) (hhv : hv ≠ 0) (k : ℂ)
    (hk : k + hv ≠ 0) :
    (standardAffineVOA 𝔤 hv hhv k hk).centralCharge = (Module.finrank ℂ 𝔤 : ℂ) * k / (k + hv) := by
  show (Fintype.card (Fin (Module.finrank ℂ 𝔤)) : ℂ) * k / (k + (standardData 𝔤 hv hhv).h) = _
  rw [Fintype.card_fin, standardData_h]

end

end VOA.AffineGeneral
