/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeadingKoszulTranslation
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Coefficients: tensoring a Weyl datum with a module

In the coset note the Koszul complex has coefficients in `gr A ⊗ B`, where `B = L_1(sl2)`
“is merely an extra vector space factor”, and also in `gr A ⊗ B ⊗ Λ(c)` in the rows of
positive ghost count. Here a `WeylDatum` over `R` and its augmentation are tensored on the
right with an arbitrary `R`-module `N`; no flatness is needed, because the hypotheses of a
Weyl datum are identities and bijectivity, both preserved by `rTensor`.

## Results

* `WeylDatum.rTensor`, `WeylDatum.Augmentation.rTensor`.
* `translatedTensorKoszulH0Equiv` (**Koszul `H₀` of `x + a` with coefficients in an
  `A`-module `N` is `N`**): `(A[x] ⊗_A N) / Σ_i (x_i + a_i) ≅ N`, with
  `p ⊗ n ↦ p(x = -a) • n` (`translatedTensorKoszulH0Equiv_tmul`).
* `translatedTensor_exists_kd_eq` (Koszul acyclicity in positive degree, with coefficients).

Everything is proved outright.
-/

namespace VOA.LeadingKoszul

open TensorProduct MvPolynomial

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable (N : Type*) [AddCommGroup N] [Module R N]

omit [LinearOrder ι] in
theorem rTensor_finsum (f : ι → P →ₗ[R] P) :
    LinearMap.rTensor N (∑ i, f i) = ∑ i, LinearMap.rTensor N (f i) := by
  simp only [← LinearMap.coe_rTensorHom, map_sum]

namespace WeylDatum

variable (W : WeylDatum R ι P)

theorem u_comp_comm (i j : ι) : (W.u i).comp (W.u j) = (W.u j).comp (W.u i) :=
  LinearMap.ext (W.u_comm i j)

theorem D_comp_comm (i j : ι) : (W.D i).comp (W.D j) = (W.D j).comp (W.D i) :=
  LinearMap.ext (W.D_comm i j)

theorem D_comp_u (i j : ι) : (W.D i).comp (W.u j) =
    (W.u j).comp (W.D i) + if i = j then LinearMap.id else 0 := by
  ext v
  rw [LinearMap.comp_apply, W.D_u, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> rfl

/-- The `Σ_i u_i D_i + c` of the tensored datum is the tensored `Σ_i u_i D_i + c`. -/
theorem rTensor_Lk (k : ℕ) :
    ∑ i, (LinearMap.rTensor N (W.u i)).comp (LinearMap.rTensor N (W.D i)) +
        ((k + 1 : ℕ) : R) • (LinearMap.id : P ⊗[R] N →ₗ[R] P ⊗[R] N) =
      LinearMap.rTensor N (W.Lk k) := by
  simp only [Lk, L, ← LinearMap.rTensor_comp, LinearMap.rTensor_add, LinearMap.rTensor_smul,
    LinearMap.rTensor_id, rTensor_finsum]

/-- **A Weyl datum tensored with a module.** -/
noncomputable def rTensor : WeylDatum R ι (P ⊗[R] N) where
  u i := LinearMap.rTensor N (W.u i)
  D i := LinearMap.rTensor N (W.D i)
  u_comm i j v := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, W.u_comp_comm, LinearMap.rTensor_comp,
      LinearMap.comp_apply]
  D_comm i j v := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, W.D_comp_comm, LinearMap.rTensor_comp,
      LinearMap.comp_apply]
  D_u i j v := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, W.D_comp_u, LinearMap.rTensor_add,
      LinearMap.add_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
    split_ifs
    · rw [LinearMap.rTensor_id, LinearMap.id_apply]
    · rw [LinearMap.rTensor_zero, LinearMap.zero_apply]
  bij k := by
    rw [W.rTensor_Lk N k]
    have : ⇑(LinearMap.rTensor N (W.Lk k)) = ⇑(LinearEquiv.rTensor N (W.Lequiv k)) := rfl
    rw [this]
    exact (LinearEquiv.rTensor N (W.Lequiv k)).bijective

theorem rTensor_L : (W.rTensor N).L = LinearMap.rTensor N W.L := by
  simp only [L, rTensor, ← LinearMap.rTensor_comp, rTensor_finsum]

variable {W}

/-- **An augmentation tensored with a module.** -/
noncomputable def Augmentation.rTensor {Q : Type*} [AddCommGroup Q] [Module R Q]
    (Aug : W.Augmentation Q) : (W.rTensor N).Augmentation (Q ⊗[R] N) where
  ε := LinearMap.rTensor N Aug.ε
  σ := LinearMap.rTensor N Aug.σ
  G := LinearMap.rTensor N Aug.G
  ε_L v := by
    rw [rTensor_L, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show Aug.ε.comp W.L = 0 from LinearMap.ext Aug.ε_L, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
  ε_σ q := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show Aug.ε.comp Aug.σ = LinearMap.id from LinearMap.ext Aug.ε_σ, LinearMap.rTensor_id,
      LinearMap.id_apply]
  split v := by
    rw [rTensor_L, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply
      (LinearMap.rTensor N Aug.σ), ← LinearMap.rTensor_comp, ← LinearMap.add_apply,
      ← LinearMap.rTensor_add,
      show W.L.comp Aug.G + Aug.σ.comp Aug.ε = LinearMap.id from LinearMap.ext Aug.split,
      LinearMap.rTensor_id, LinearMap.id_apply]

end WeylDatum

namespace Translation

variable {A : Type u} [CommRing A] [Algebra ℚ A] (a : ι → A)
variable (M : Type*) [AddCommGroup M] [Module A M]

/-- **Koszul `H₀` of `x + a` with coefficients in an `A`-module `M` is `M`.** -/
noncomputable def translatedTensorKoszulH0Equiv :
    ((MvPolynomial ι A ⊗[A] M) ⧸ ⨆ i, LinearMap.range (((translatedWeyl a).rTensor M).u i))
      ≃ₗ[A] M :=
  ((translatedAug a).rTensor M).koszulH0Equiv.trans (TensorProduct.lid A M)

theorem translatedTensorKoszulH0Equiv_tmul (p : MvPolynomial ι A) (m : M) :
    translatedTensorKoszulH0Equiv a M (Submodule.Quotient.mk (p ⊗ₜ m)) =
      eval (fun i => -a i) p • m := by
  simp only [translatedTensorKoszulH0Equiv, LinearEquiv.trans_apply,
    WeylDatum.Augmentation.koszulH0Equiv_mk]
  change TensorProduct.lid A M ((translatedAug a).ε p ⊗ₜ m) = _
  rw [translatedAug_ε, TensorProduct.lid_tmul]

/-- **Koszul acyclicity of `x + a` in positive degree, with coefficients in `M`.** -/
theorem translatedTensor_exists_kd_eq (l : ℕ) (f : Finset ι → MvPolynomial ι A ⊗[A] M)
    (hf : ∀ S, S.card ≠ l + 1 → f S = 0) (hd : ((translatedWeyl a).rTensor M).kd f = 0) :
    ∃ g, (∀ S, S.card ≠ l + 2 → g S = 0) ∧ ((translatedWeyl a).rTensor M).kd g = f :=
  ((translatedWeyl a).rTensor M).exists_kd_eq l f hf hd

end Translation

end VOA.LeadingKoszul
