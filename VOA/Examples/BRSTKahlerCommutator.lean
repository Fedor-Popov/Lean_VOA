/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodDerived

/-!
# The Kähler relation from an `sp(2)` commutator (Beem–Garner Proposition 3.8, abstractly)

Beem–Garner obtain `𝐐⁻𝐐⁺ + 𝐐⁺𝐐⁻ = 0` because the two differentials form a doublet of the
`Sp(2, ℂ)` outer automorphism of the symplectic fermions `η⁺ = b`, `η⁻ = ∂c`. Infinitesimally:
there is an even operator `Λ` (the raising operator `η⁻ ↦ η⁺` of the Lefschetz triple, a ghost
bilinear `Σ (1/n) b_{-n} b_n`) with `𝐐⁺ = [Λ, 𝐐⁻]`. Then the Kähler relation is **automatic**:

  `𝐐⁻ [Λ, 𝐐⁻] + [Λ, 𝐐⁻] 𝐐⁻ = Λ (𝐐⁻)² - (𝐐⁻)² Λ = 0`.

This file proves the abstract content of that argument for the minimal input `GoodHalf`, where
`𝐐⁺` is *derived* from `𝐐⁻` by adjunction (`GoodHalf.derivedDp`):

* `adR` (`[2R, T]`), `loPart_sub_hiPart` (`lo T - hi T = -[2R, T]`), `loPart_add_hiPart`;
* `GoodHalf.adR_adR_D` — goodness of `𝐐⁻` means `[2R, [2R, 𝐐⁻]] = 𝐐⁻`;
* `GoodHalf.derivedDp_eq_of_adjoint` — for **any** operator `E` with
  `(𝐐⁻)† = lo E - hi E`, the derived second differential is `[2R, [2R, E]]`
  (the `R`-preserving part of `E` is invisible to the adjoint);
* `GoodHalf.adR_comm_of_shift` — an operator mapping `(2R, gh)` into `(2R, gh + e)` commutes with
  the `2R` grading operator;
* `GoodHalf.derivedDp_eq_commutator` — if `Λ` preserves `2R` and `[Λ, 𝐐⁻]` satisfies the
  Beem–Garner adjoint relation `(𝐐⁻)† = lo[Λ,𝐐⁻] - hi[Λ,𝐐⁻]` (i.e. `(Q⁻)† = S⁺`,
  `(S⁻)† = -Q⁺` with `Q⁺ + S⁺ = [Λ, 𝐐⁻]`), then `derivedDp = [Λ, 𝐐⁻]`;
* `GoodHalf.kahlerAnticomm_of_commutator`, `GoodHalf.kahlerAnticomm_of_sp2` — hence the
  Kähler relation `KahlerAnticomm` holds;
* `GoodHalf.Sp2Adjoint` — the hypothesis bundled, stated **without** the grading operator
  (`Sp2Adjoint.adjoint_apply`, `Sp2Adjoint.toAdj`): `(𝐐⁻ x, y) = (x, v - u)` whenever
  `[Λ, 𝐐⁻] y = u + v` with `u`, `v` of bidegrees `(2R+1, gh-1)`, `(2R-1, gh-1)`.

and, for the conjugation datum:

* `GoodComplex.ConjData.ofRhoD` — the field `ρ_Dp` of `ConjData` is **redundant**: it follows from
  `ρ_D`, `ρ² = s` and `s ≠ 0` (`κ' = conj((κ s)⁻¹) s`);
* `GoodHalf.rho_D_of_commutator` — with `derivedDp = [Λ, 𝐐⁻]`, the relation `ρ 𝐐⁻ = κ 𝐐⁺ ρ`
  is the statement `ρ 𝐐⁻ = κ [Λ, 𝐐⁻] ρ` about the explicit operator `[Λ, 𝐐⁻]`.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open Module (finrank)

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-! ### The commutator with the grading operator -/

/-- `[2R, T]`. -/
def adR (Rop T : K →ₗ[ℂ] K) : K →ₗ[ℂ] K := Rop.comp T - T.comp Rop

theorem adR_apply (Rop T : K →ₗ[ℂ] K) (x : K) : adR Rop T x = Rop (T x) - T (Rop x) := rfl

theorem loPart_sub_hiPart (Rop T : K →ₗ[ℂ] K) :
    loPart Rop T - hiPart Rop T = -adR Rop T := by
  ext x
  simp only [loPart, hiPart, adR, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.neg_apply, LinearMap.comp_apply]
  module

theorem loPart_add_hiPart (Rop T : K →ₗ[ℂ] K) : loPart Rop T + hiPart Rop T = T := by
  rw [add_comm]; exact hiPart_add_loPart Rop T

theorem adR_neg (Rop T : K →ₗ[ℂ] K) : adR Rop (-T) = -adR Rop T := by
  ext x; simp [adR_apply]; abel

/-- If `Λ` commutes with the grading operator, `ad_R` commutes with `ad_Λ`. -/
theorem adR_commutator {Rop Λ : K →ₗ[ℂ] K} (h : Rop.comp Λ = Λ.comp Rop) (T : K →ₗ[ℂ] K) :
    adR Rop (Λ.comp T - T.comp Λ) = Λ.comp (adR Rop T) - (adR Rop T).comp Λ := by
  ext x
  have h1 : ∀ y, Rop (Λ y) = Λ (Rop y) := fun y => LinearMap.congr_fun h y
  simp only [adR_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, h1]
  abel

/-! ### The derived second differential as a double commutator -/

namespace GoodHalf

variable [FiniteDimensional ℂ K] (H : GoodHalf K) (hpos : IsPosOn H.P ⊤)

omit [FiniteDimensional ℂ K] in
/-- An operator mapping `(2R, gh)` into `(2R, gh + e)` commutes with the grading operator. -/
theorem adR_comm_of_shift {Λ : K →ₗ[ℂ] K} (e : ℤ)
    (hΛ : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), Λ x ∈ H.deg (j, g + e)) :
    (H.Rop hpos).comp Λ = Λ.comp (H.Rop hpos) := by
  apply H.linearMap_ext_deg
  rintro ⟨j, g⟩ x hx
  simp only [LinearMap.comp_apply]
  rw [H.Rop_deg hpos j g x hx, map_smul, H.Rop_deg hpos j (g + e) _ (hΛ j g x hx)]

omit [FiniteDimensional ℂ K] in
/-- **Goodness of `𝐐⁻` as a double-commutator identity**: `[2R, [2R, 𝐐⁻]] = 𝐐⁻`. -/
theorem adR_adR_D : adR (H.Rop hpos) (adR (H.Rop hpos) H.D) = H.D := by
  apply H.linearMap_ext_deg
  rintro ⟨j, g⟩ x hx
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (H.D_good (j, g) x hx)
  have hRx : H.Rop hpos x = (j : ℂ) • x := H.Rop_deg hpos j g x hx
  have hRu : H.Rop hpos u = ((j + 1 : ℤ) : ℂ) • u := H.Rop_deg hpos (j + 1) (g + 1) u hu
  have hRv : H.Rop hpos v = ((j + -1 : ℤ) : ℂ) • v := H.Rop_deg hpos (j + -1) (g + 1) v hv
  have h1 : adR (H.Rop hpos) H.D x = u - v := by
    rw [adR_apply, hRx, map_smul, ← huv, map_add, hRu, hRv]
    push_cast; module
  rw [adR_apply, h1, hRx, map_smul, h1, map_sub, hRu, hRv, ← huv]
  push_cast; module

/-- `D† = lo E - hi E` determines `D†`. -/
theorem Dadj_eq_of_adjoint (E : K →ₗ[ℂ] K)
    (hE : ∀ x y, H.P (H.D x) y = H.P x (loPart (H.Rop hpos) E y - hiPart (H.Rop hpos) E y)) :
    H.Dadj hpos = loPart (H.Rop hpos) E - hiPart (H.Rop hpos) E := by
  ext y
  apply sesq_ext_right H.P hpos
  intro x
  rw [← H.Dadj_spec hpos, hE, LinearMap.sub_apply]

/-- `derivedDp = lo D† - hi D† = -[2R, D†]`. -/
theorem derivedDp_eq_neg_adR : H.derivedDp hpos = -adR (H.Rop hpos) (H.Dadj hpos) :=
  loPart_sub_hiPart _ _

/-- **The derived `𝐐⁺` from any operator satisfying the adjoint relation**: if
`(𝐐⁻)† = lo E - hi E`, then `derivedDp = [2R, [2R, E]]`. No goodness of `E` is needed. -/
theorem derivedDp_eq_of_adjoint (E : K →ₗ[ℂ] K)
    (hE : ∀ x y, H.P (H.D x) y = H.P x (loPart (H.Rop hpos) E y - hiPart (H.Rop hpos) E y)) :
    H.derivedDp hpos = adR (H.Rop hpos) (adR (H.Rop hpos) E) := by
  rw [derivedDp_eq_neg_adR, H.Dadj_eq_of_adjoint hpos E hE, loPart_sub_hiPart, adR_neg, neg_neg]

/-- **The derived `𝐐⁺` is the `sp(2)` image of `𝐐⁻`**: if `Λ` preserves `2R` and
`[Λ, 𝐐⁻]` satisfies the Beem–Garner adjoint relation, then `derivedDp = [Λ, 𝐐⁻]`. -/
theorem derivedDp_eq_commutator {Λ : K →ₗ[ℂ] K}
    (hΛ : (H.Rop hpos).comp Λ = Λ.comp (H.Rop hpos))
    (hE : ∀ x y, H.P (H.D x) y = H.P x
      (loPart (H.Rop hpos) (Λ.comp H.D - H.D.comp Λ) y -
        hiPart (H.Rop hpos) (Λ.comp H.D - H.D.comp Λ) y)) :
    H.derivedDp hpos = Λ.comp H.D - H.D.comp Λ := by
  rw [H.derivedDp_eq_of_adjoint hpos _ hE, adR_commutator hΛ, adR_commutator hΛ,
    H.adR_adR_D hpos]

omit [FiniteDimensional ℂ K] in
/-- `𝐐⁻ [Λ, 𝐐⁻] + [Λ, 𝐐⁻] 𝐐⁻ = Λ (𝐐⁻)² - (𝐐⁻)² Λ = 0`. -/
theorem commutator_anticomm (Λ : K →ₗ[ℂ] K) :
    H.D.comp (Λ.comp H.D - H.D.comp Λ) + (Λ.comp H.D - H.D.comp Λ).comp H.D = 0 := by
  have h2 : ∀ x, H.D (H.D x) = 0 := fun x => LinearMap.congr_fun H.sq_zero x
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, h2,
    map_zero, LinearMap.zero_apply]
  abel

/-- **The Kähler relation from a commutator form of the derived `𝐐⁺`.** -/
theorem kahlerAnticomm_of_commutator {Λ : K →ₗ[ℂ] K}
    (h : H.derivedDp hpos = Λ.comp H.D - H.D.comp Λ) : H.KahlerAnticomm hpos := by
  unfold KahlerAnticomm
  rw [h]
  exact H.commutator_anticomm Λ

/-- **Beem–Garner's `Sp(2)` argument, abstractly**: a `2R`-preserving `Λ` whose commutator
with `𝐐⁻` satisfies the adjoint relation gives the Kähler relation. -/
theorem kahlerAnticomm_of_sp2 {Λ : K →ₗ[ℂ] K}
    (hΛ : (H.Rop hpos).comp Λ = Λ.comp (H.Rop hpos))
    (hE : ∀ x y, H.P (H.D x) y = H.P x
      (loPart (H.Rop hpos) (Λ.comp H.D - H.D.comp Λ) y -
        hiPart (H.Rop hpos) (Λ.comp H.D - H.D.comp Λ) y)) :
    H.KahlerAnticomm hpos :=
  H.kahlerAnticomm_of_commutator hpos (H.derivedDp_eq_commutator hpos hΛ hE)

/-! ### The hypothesis without the grading operator -/

/-- **Beem–Garner Lemma 3.16 for the `sp(2)` image**, stated without the grading operator. `Λ`
shifts the ghost number by `-2` and preserves `2R` (Beem–Garner's `Λ = Σ (1/n) η⁺_{-n} η⁺_n`
type operator); whenever `[Λ, 𝐐⁻] y = u + v` with `u` raising and `v` lowering `2R`, one has
`(𝐐⁻ x, y) = (x, v - u)`, i.e. `(Q⁻)† = S⁺` and `(S⁻)† = -Q⁺` for `Q⁺ + S⁺ = [Λ, 𝐐⁻]`. -/
structure Sp2Adjoint (H : GoodHalf K) where
  Λ : K →ₗ[ℂ] K
  shift : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), Λ x ∈ H.deg (j, g - 2)
  adjoint : ∀ (x : K) (j g : ℤ), ∀ y ∈ H.deg (j, g), ∀ u ∈ H.deg ((j, g) + shQp),
    ∀ v ∈ H.deg ((j, g) + shSp), (Λ.comp H.D - H.D.comp Λ) y = u + v →
      H.P (H.D x) y = H.P x (v - u)

namespace Sp2Adjoint

variable {H}

/-- The `sp(2)` image `[Λ, 𝐐⁻]`. -/
def E (S : Sp2Adjoint H) : K →ₗ[ℂ] K := S.Λ.comp H.D - H.D.comp S.Λ

omit [FiniteDimensional ℂ K] in
/-- `[Λ, 𝐐⁻]` is good for the second differential: `(2R, gh) ↦ (2R ± 1, gh - 1)`. -/
theorem E_good (S : Sp2Adjoint H) (j g : ℤ) (y : K) (hy : y ∈ H.deg (j, g)) :
    S.E y ∈ H.deg ((j, g) + shQp) ⊔ H.deg ((j, g) + shSp) := by
  have hD := H.D_good (j, g) y hy
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hD
  have hΛy := S.shift j g y hy
  have hD' := H.D_good (j, g - 2) _ hΛy
  obtain ⟨u', hu', v', hv', huv'⟩ := Submodule.mem_sup.mp hD'
  have hΛu := S.shift (j + 1) (g + 1) u hu
  have hΛv := S.shift (j + -1) (g + 1) v hv
  have e1 : ((j + 1, g + 1 - 2) : ℤ × ℤ) = (j, g) + shQp := by
    exact Prod.ext (by simp [shQp]) (by simp [shQp]; ring)
  have e2 : ((j + -1, g + 1 - 2) : ℤ × ℤ) = (j, g) + shSp := by
    exact Prod.ext (by simp [shSp]) (by simp [shSp]; ring)
  have e3 : ((j, g - 2) + shQm : ℤ × ℤ) = (j, g) + shQp := by
    exact Prod.ext (by simp [shQm, shQp]) (by simp [shQm, shQp]; ring)
  have e4 : ((j, g - 2) + shSm : ℤ × ℤ) = (j, g) + shSp := by
    exact Prod.ext (by simp [shSm, shSp]) (by simp [shSm, shSp]; ring)
  rw [e1] at hΛu
  rw [e2] at hΛv
  rw [e3] at hu'
  rw [e4] at hv'
  have hE : S.E y = (S.Λ u - u') + (S.Λ v - v') := by
    simp only [E, LinearMap.sub_apply, LinearMap.comp_apply, ← huv, ← huv', map_add]
    abel
  rw [hE]
  exact Submodule.add_mem_sup (Submodule.sub_mem _ hΛu hu') (Submodule.sub_mem _ hΛv hv')

omit [FiniteDimensional ℂ K] in
/-- The bundled hypothesis in the grading-operator form. -/
theorem toAdj (S : Sp2Adjoint H) (x y : K) :
    H.P (H.D x) y = H.P x (loPart (H.Rop hpos) S.E y - hiPart (H.Rop hpos) S.E y) := by
  revert y
  have key : ∀ y, H.P (H.D x) y - H.P x (loPart (H.Rop hpos) S.E y -
      hiPart (H.Rop hpos) S.E y) = 0 := by
    intro y
    refine H.forall_of_deg (fun y => H.P (H.D x) y - H.P x (loPart (H.Rop hpos) S.E y -
      hiPart (H.Rop hpos) S.E y) = 0) ?_ ?_ ?_ y
    · simp [H.P.zero_right]
    · intro y y' hy hy'
      beta_reduce at hy hy' ⊢
      rw [H.P.add_right, map_add, map_add, add_sub_add_comm, H.P.add_right]
      rw [show H.P (H.D x) y + H.P (H.D x) y' -
          (H.P x (loPart (H.Rop hpos) S.E y - hiPart (H.Rop hpos) S.E y) +
            H.P x (loPart (H.Rop hpos) S.E y' - hiPart (H.Rop hpos) S.E y')) =
          (H.P (H.D x) y - H.P x (loPart (H.Rop hpos) S.E y - hiPart (H.Rop hpos) S.E y)) +
          (H.P (H.D x) y' - H.P x (loPart (H.Rop hpos) S.E y' -
            hiPart (H.Rop hpos) S.E y')) by ring, hy, hy', add_zero]
    · rintro ⟨j, g⟩ y hy
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (S.E_good j g y hy)
      obtain ⟨h1, h2⟩ := H.split_apply hpos S.E (-1) j g hy hu hv huv.symm
      rw [h1, h2, S.adjoint x j g y hy u hu v hv huv.symm, sub_self]
  intro y
  exact sub_eq_zero.mp (key y)

omit [FiniteDimensional ℂ K] in
/-- The shift property gives commutation with the grading operator. -/
theorem rop_comm (S : Sp2Adjoint H) : (H.Rop hpos).comp S.Λ = S.Λ.comp (H.Rop hpos) :=
  H.adR_comm_of_shift hpos (-2) fun j g x hx => by
    rw [← sub_eq_add_neg]; exact S.shift j g x hx

/-- `derivedDp = [Λ, 𝐐⁻]`. -/
theorem derivedDp_eq (S : Sp2Adjoint H) : H.derivedDp hpos = S.E :=
  H.derivedDp_eq_commutator hpos (S.rop_comm hpos) (S.toAdj hpos)

/-- **The Kähler relation from the `sp(2)` adjoint relation.** -/
theorem kahlerAnticomm (S : Sp2Adjoint H) : H.KahlerAnticomm hpos :=
  H.kahlerAnticomm_of_sp2 hpos (S.rop_comm hpos) (S.toAdj hpos)

end Sp2Adjoint

end GoodHalf

/-! ### The conjugation datum: `ρ_Dp` is redundant -/

namespace GoodComplex

variable {G : GoodComplex K}

/-- **`ConjData` without the field `ρ_Dp`**, which follows from `ρ_D`, `ρ² = s` and `s ≠ 0`:
`ρ 𝐐⁺ = conj((κ s)⁻¹) s · 𝐐⁻ ρ`. -/
def ConjData.ofRhoD (B : LinearMap.BilinForm ℂ K) (ρ : K →ₗ⋆[ℂ] K) (h : SesqForm K)
    (h_eq : ∀ x y, h x y = B (ρ x) y)
    (P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * h x y)
    (ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g))
    (κ : ℂ) (hκ : κ ≠ 0) (ρ_D : ∀ x, ρ (G.D x) = κ • G.Dp (ρ x))
    (s : ℂ) (hs : s ≠ 0) (ρ_sq : ∀ x, ρ (ρ x) = s • x) : ConjData G where
  B := B
  ρ := ρ
  h := h
  h_eq := h_eq
  P_eq := P_eq
  ρ_deg := ρ_deg
  κ := κ
  κ' := (starRingEnd ℂ) (κ * s)⁻¹ * s
  hκ := hκ
  hκ' := mul_ne_zero (by simp [hκ, hs]) hs
  ρ_D := ρ_D
  ρ_Dp := by
    intro x
    have h1 : ρ (G.D (ρ x)) = (κ * s) • G.Dp x := by
      rw [ρ_D, ρ_sq, map_smul, smul_smul]
    have h2 : G.Dp x = (κ * s)⁻¹ • ρ (G.D (ρ x)) := by
      rw [h1, smul_smul, inv_mul_cancel₀ (mul_ne_zero hκ hs), one_smul]
    rw [h2, LinearMap.map_smulₛₗ, ρ_sq, smul_smul]
  s := s
  hs := hs
  ρ_sq := ρ_sq

end GoodComplex

namespace GoodHalf

variable [FiniteDimensional ℂ K] {H : GoodHalf K} {hpos : IsPosOn H.P ⊤}

/-- With `derivedDp = [Λ, 𝐐⁻]`, the conjugation relation `ρ 𝐐⁻ = κ 𝐐⁺ ρ` of `ConjData` is a
statement about the explicit operator `[Λ, 𝐐⁻]`. -/
theorem rho_D_of_commutator {Λ : K →ₗ[ℂ] K}
    (h : H.derivedDp hpos = Λ.comp H.D - H.D.comp Λ) (ρ : K →ₗ⋆[ℂ] K) (κ : ℂ)
    (hρ : ∀ x, ρ (H.D x) = κ • (Λ.comp H.D - H.D.comp Λ) (ρ x)) :
    ∀ x, ρ (H.D x) = κ • H.derivedDp hpos (ρ x) := by
  intro x; rw [h]; exact hρ x

end GoodHalf

end

end VOA.ConcreteHodge
