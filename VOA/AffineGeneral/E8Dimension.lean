/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.CartanLatticeSimple
import VOA.LatticesAndCodes.Leech.RepCount

/-!
# `dim 𝔢₈ = 248`: the `E₈` lattice has `240` roots

The `E₈` root lattice is even, unimodular (its Cartan matrix has an explicit integer inverse) and
positive definite of rank `8`, so its theta series is a level-one modular form of weight `4`.
`M₄` is spanned by `E₄ = 1 + 240 q + …`, hence `r(2) = 240 r(0) = 240` (`e8E_repCount_two`).
With `dim (V_L)₁ = rank L + #roots` (`LatticeLie.finrank_V1`) this gives
**`finrank ℂ e8Lie = 248`** (`finrank_e8Lie`), the `currentDimension` of the Deligne case `E₈`.
-/

open Complex UpperHalfPlane EisensteinSeries
open scoped MatrixGroups Real

namespace ModularForm

theorem wtIdx_four {p : ℕ × ℕ} (hp : p ∈ wtIdx 4) : p = (1, 0) := by
  rw [mem_wtIdx] at hp
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.injEq]
  omega

/-- On level-one modular forms of weight `4`, `c₁ = 240 c₀` (`M₄ = ℂ E₄`). -/
theorem coeff_one_of_weight_four (f : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ)) :
    (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = 240 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0 := by
  have hf : f ∈ Submodule.span ℂ (Set.range (eisBasisFun 4)) := by
    rw [span_eisBasisFun]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, rfl⟩ := hg
    have hq : qExpansion 1 (eisBasisFun 4 p : ℍ → ℂ)
        = (qExpansion 1 (E₄ : ℍ → ℂ)) ^ (p : ℕ × ℕ).1
          * (qExpansion 1 (E₆ : ℍ → ℂ)) ^ (p : ℕ × ℕ).2 := by
      rw [eisBasisFun, ModularForm.qExpansion_mcast, qExpansion_eisMonomial]
    rw [hq, wtIdx_four p.2]
    simp only [pow_one, pow_zero, mul_one]
    rw [E₄_coeff_zero, E₄_coeff_one]
    ring
  | zero =>
    have h0 : qExpansion 1 ((0 : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ)) : ℍ → ℂ) = 0 := by
      have h := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (0 : ℂ)
        (0 : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ))
      simpa using h
    rw [h0]
    simp
  | add x y _ _ hx hy =>
    have hadd : qExpansion 1 ((x + y : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ)) : ℍ → ℂ)
        = qExpansion 1 (x : ℍ → ℂ) + qExpansion 1 (y : ℍ → ℂ) :=
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL x y
    rw [hadd]
    simp only [map_add]
    rw [hx, hy]
    ring
  | smul a x _ hx =>
    have hsmul : qExpansion 1 ((a • x : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ)) : ℍ → ℂ)
        = a • qExpansion 1 (x : ℍ → ℂ) :=
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL a x
    rw [hsmul]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]
    rw [hx]
    ring

end ModularForm

namespace VOA.AffineGeneral.E8Dim

open VOA.CartanLattices VOA.LatGen VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple

noncomputable section

/-- The `E₈` root lattice as a `LatticesAndCodes` lattice (same carrier and form as `e8`). -/
def e8E : _root_.IntegralLattice where
  carrier := Fin 8 → ℤ
  bilin := Matrix.toBilin' CartanMatrix.E₈
  bilin_symm x y := LatticeLie.form_comm e8 x y

theorem e8E_isPosDef : e8E.IsPosDef := fun x hx => e8_posDef x hx

theorem e8E_isEven : e8E.IsEven := fun x => e8_even x

theorem e8E_rank : e8E.rank = 8 := Module.finrank_fin_fun ℤ

/-- The inverse of the `E₈` Cartan matrix (integral: `E₈` is unimodular). -/
def e8Inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

theorem e8Inv_mul : e8Inv * CartanMatrix.E₈ = 1 := by decide

theorem e8E_isUnimodular : e8E.IsUnimodular := by
  rw [_root_.IntegralLattice.IsUnimodular,
    ← _root_.IntegralLattice.det_eq_gram_det e8E (Pi.basisFun ℤ (Fin 8))]
  have hg : e8E.gram (Pi.basisFun ℤ (Fin 8)) = CartanMatrix.E₈ := by
    ext i j
    rw [_root_.IntegralLattice.gram_apply]
    have hb : ∀ k, (Pi.basisFun ℤ (Fin 8) k : Fin 8 → ℤ) = Pi.single k 1 := fun k => by
      rw [Pi.basisFun_apply]
    change Matrix.toBilin' CartanMatrix.E₈ (Pi.basisFun ℤ (Fin 8) i) (Pi.basisFun ℤ (Fin 8) j) = _
    rw [hb, hb]
    exact form_single _ CartanMatrix.E₈_isSymm i j
  rw [hg]
  exact Matrix.isUnit_det_of_left_inverse e8Inv_mul

/-- **The `E₈` lattice has `240` roots**, from `θ_{E₈} ∈ M₄ = ℂ E₄`. -/
theorem e8E_repCount_two : e8E.repCount 2 = 240 := by
  have hw : ((e8E.rank / 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) := by rw [e8E_rank]
  set f := e8E.thetaModularForm e8E_isPosDef e8E_isEven e8E_isUnimodular with hf
  set g : ModularForm 𝒮ℒ ((4 : ℕ) : ℤ) := ModularForm.mcast hw f with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
    rw [hg, ModularForm.qExpansion_mcast]
  have h1 := ModularForm.coeff_one_of_weight_four g
  rw [hqg] at h1
  have c0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 1 := by
    rw [hf]
    exact e8E.coeff_qExpansion_thetaModularForm_zero _ _ _
  have c1 : (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = (e8E.repCount 2 : ℂ) := by
    rw [hf, e8E.coeff_qExpansion_thetaModularForm _ _ _ 1]
    norm_num
  rw [c0, c1, mul_one] at h1
  exact_mod_cast h1

/-- The roots of `e8`, counted. -/
theorem card_roots_e8 : (normEq e8 e8_posDef 2).card = 240 := by
  rw [← e8E_repCount_two, _root_.IntegralLattice.repCount, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Finset.mem_coe, mem_normEq]
  rfl

/-- **`dim 𝔢₈ = 248`.** -/
theorem finrank_e8Lie : Module.finrank ℂ e8Lie = 248 := by
  rw [finrank_V1, card_roots_e8, show e8.rank = 8 from DeligneLatticeLie.rank_ofCartan _ _]

end

end VOA.AffineGeneral.E8Dim
