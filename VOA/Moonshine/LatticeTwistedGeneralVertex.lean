/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralCharge
import VOA.Moonshine.LatticeTwistedVertex

/-! # Charge-parametric vertex for even lattices
Adapted from `LatticeTwistedVertex` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)

noncomputable def YTL (α : L.carrier) (k : ℤ) :
    End ℂ (FockT (rank L) ⊗[ℂ] Space L hEven C) :=
  YTg (chargeCoord L α) (L.form α α) ((2 : ℂ) ^ (-(L.form α α))) (eT L hEven C α) k

theorem YTL_truncation (α : L.carrier)
    (x : FockT (rank L) ⊗[ℂ] Space L hEven C) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YTL L hEven C α k x = 0 :=
  YTg_truncation _ _ _ _ x

theorem eT_swap (α β : L.carrier) :
    eT L hEven C β * eT L hEven C α
      = (-1 : ℂ) ^ (L.form α β).natAbs • (eT L hEven C α * eT L hEven C β) := by
  rw [eT_mul, eT_mul, latticeCocycle_swap_sign L hEven β α, add_comm β α, mul_smul,
    form_symm L β α, neg_one_zpow_eq_pow_natAbs]

theorem YTL_local (hPos : L.PosDef) (α β : L.carrier) (e e' : ℤ) :
    Local (resc (YTL L hEven C α) 2 e) (resc (YTL L hEven C β) 2 e') :=
  YTg_local (chargeCoord L α) (chargeCoord L β) (L.form α β) (sum_chargeCoord L hPos α β) _ _ _ _
    _ _ (eT_swap L hEven C α β) e e'

theorem FgenT_YTL_local (a : Fin (rank L)) (β : L.carrier) (e : ℤ) :
    Local (FgenT (Tm := Space L hEven C) a)
      (resc (YTL L hEven C β) 2 e) :=
  FgenT_YTg_local a _ _ _ _ e

noncomputable def FgenTFld (a : Fin (rank L)) :
    Fld (FockT (rank L) ⊗[ℂ] Space L hEven C) :=
  rescFld (A := modeTT a) (by norm_num : 0 < 2) (modeTT_truncation a) 1

noncomputable def YTLFld (α : L.carrier) (e : ℤ) :
    Fld (FockT (rank L) ⊗[ℂ] Space L hEven C) :=
  rescFld (A := YTL L hEven C α) (by norm_num : 0 < 2) (YTL_truncation L hEven C α) e

theorem prod_FgenTFld_YTLFld_zero (a : Fin (rank L)) (β : L.carrier) (e : ℤ) :
    Fld.prod 0 (FgenTFld L hEven C a) (YTLFld L hEven C β e)
      = chargeCoord L β a • YTLFld L hEven C β (e + 1) := by
  apply Subtype.ext
  rw [Fld.prod_of_nonneg le_rfl, Fld.smul_val]
  change cCoeff 0 (bracketDist (FgenT a)
    (resc (YTg (chargeCoord L β) (L.form β β) ((2 : ℂ) ^ (-(L.form β β)))
      (eT L hEven C β)) 2 e)) = _
  rw [bracketDist_FgenT_YTg, cCoeff_deltaDeriv, if_pos rfl, Nat.factorial_zero,
    Nat.cast_one, one_smul]
  rfl

theorem prod_FgenTFld_YTLFld_pos (a : Fin (rank L)) (β : L.carrier) (e : ℤ) {j : ℤ}
    (hj : 0 < j) : Fld.prod j (FgenTFld L hEven C a) (YTLFld L hEven C β e) = 0 := by
  apply Subtype.ext
  rw [Fld.prod_of_nonneg hj.le]
  change cCoeff j.toNat (bracketDist (FgenT a)
    (resc (YTg (chargeCoord L β) (L.form β β) ((2 : ℂ) ^ (-(L.form β β)))
      (eT L hEven C β)) 2 e)) = _
  rw [bracketDist_FgenT_YTg, cCoeff_deltaDeriv, if_neg (by omega)]
  rfl

def latGenSet : Set (Fld (FockT (rank L) ⊗[ℂ] Space L hEven C)) :=
  Set.range (FgenTFld L hEven C) ∪ Set.range (fun p : L.carrier × ℤ => YTLFld L hEven C p.1 p.2)

theorem latGenSet_local (hPos : L.PosDef) :
    ∀ a ∈ latGenSet L hEven C, ∀ b ∈ latGenSet L hEven C, Local a.1 b.1 := by
  rintro a (⟨i, rfl⟩ | ⟨⟨α, e⟩, rfl⟩) b (⟨j, rfl⟩ | ⟨⟨β, e'⟩, rfl⟩)
  · exact FgenT_local i j
  · exact FgenT_YTL_local L hEven C i β e'
  · exact (FgenT_YTL_local L hEven C j α e).symm
  · exact YTL_local L hEven C hPos α β e e'

theorem latticeTwistedSystem_local (hPos : L.PosDef)
    {a b : Fld (FockT (rank L) ⊗[ℂ] Space L hEven C)}
    (ha : a ∈ TGenerated (latGenSet L hEven C)) (hb : b ∈ TGenerated (latGenSet L hEven C)) :
    Local a.1 b.1 :=
  tgenerated_local (latGenSet_local L hEven C hPos) ha hb

end Lattice

section LatticeNeg

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)

theorem YTL_neg (α : L.carrier) (k : ℤ) :
    YTL L hEven C (-α) k = (-1 : ℂ) ^ k • YTL L hEven C α k := by
  have hc : chargeCoord L (-α) = -chargeCoord L α := funext (chargeCoord_neg L α)
  have hf : L.form (-α) (-α) = L.form α α := by simp
  rw [YTL, YTL, hc, hf, eT_neg, YTg_neg]
  congr 1
  obtain ⟨c, hc⟩ := hEven α
  exact neg_one_zpow_congr (by omega)

theorem YTL_add_neg_of_odd (α : L.carrier) {k : ℤ} (hk : k % 2 = 1) :
    YTL L hEven C α k + YTL L hEven C (-α) k = 0 := by
  rw [YTL_neg, show (-1 : ℂ) ^ k = -1 by
    rw [neg_one_zpow_congr (b := 1) (by omega)]; norm_num, neg_one_smul, add_neg_cancel]

theorem YTL_sub_neg_of_even (α : L.carrier) {k : ℤ} (hk : k % 2 = 0) :
    YTL L hEven C α k - YTL L hEven C (-α) k = 0 := by
  rw [YTL_neg, show (-1 : ℂ) ^ k = 1 by
    rw [neg_one_zpow_congr (b := 0) (by omega)]; norm_num, one_smul, sub_self]

theorem YTL_zero (k : ℤ) : YTL L hEven C 0 k = if k = -2 then 1 else 0 := by
  have hc : chargeCoord L (0 : L.carrier) = 0 := funext (chargeCoord_zero L)
  rw [YTL, hc, map_zero, neg_zero, zpow_zero, eT_zero, YTg_zero_charge]

end LatticeNeg

end VOA.Moonshine.LatticeTwistedGeneral
