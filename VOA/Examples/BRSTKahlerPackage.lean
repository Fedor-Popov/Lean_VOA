/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerConj

/-!
# The Kähler relation and the conjugation datum from one Beem–Garner package

Beem–Garner prove their adjoint relations (Lemma 3.16) from the general mode-adjoint formula of
a weak graded-unitary vertex algebra (`⟨x|y⟩ = (σρ x, y)`, `σ = i^{2R}`), applied to the BRST
current `j`, together with `ρ(j) ∝ j⁺ = Λ j` (the real structure exchanges `η⁺ = b` and
`η⁻ = ∂c`). This file isolates exactly what that argument uses, as a structure on the minimal
input `GoodHalf`, and proves that it yields **both** remaining inputs of the endpoint:

`GoodHalf.Sp2Package` (with `E = [Λ, 𝐐⁻]`):
* `Λ` shifts `(2R, gh)` by `(0, -2)`;
* `P_eq`: `⟨x|y⟩ = i^{2R} B(ρ x, y)` (Beem–Garner's `(σρ x, y)`), `ρ` maps `(2R, gh)` to
  `(2R, -gh)`, `ρ² = s ≠ 0`;
* `ρ_D`: `ρ(𝐐⁻ x) = κ (-1)^{gh} E(ρ x)` — Beem–Garner's `ρ(x_n y) = (-1)^{|x||y|} ρ(x)_n ρ(y)`
  for the odd current `j`, with `ρ(j) = κ Λ(j)` and `E = (Λ j)_0 = [Λ, 𝐐⁻]`;
* `B_E`: `B(E u, v) = -(-1)^{gh u} B(u, E v)` — super-invariance of `B` for the zero mode of the
  odd weight-one quasi-primary state `Λ j`.

Proved outright:
* `GoodHalf.B_pair_zero` — `B` pairs bidegree `(j, g)` only with `(j, -g)`;
* `GoodHalf.Sp2Package.adjoint` — **Beem–Garner Lemma 3.16**: with `c = -iκ`,
  `⟨𝐐⁻ x | y⟩ = ⟨x | v - u⟩` whenever `c E y = u + v` (`u` raising, `v` lowering `2R`);
* `Sp2Package.toSp2Adjoint` (the `sp(2)` adjoint input for `Λ' = c Λ`) and
  `Sp2Package.kahlerAnticomm`;
* `Sp2Package.toSp2Conj0` — the ghost-number-zero conjugation input, with `κ₀ = κ / c = i`
  (Beem–Garner's `κ = i`);
* `leeYang_gradedUnitary_of_affine_bgPackage` — **Affine GU ⇒ Lee–Yang GU** for an arbitrary
  positive ghost form with the standard grading, from one package per weight
  (`InterpretedBGPackage`) and the downstream inputs.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open scoped TensorProduct

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-- The sesquilinear form `(ρ x, y)` of a bilinear form and an antilinear map. -/
def sesqOfBilin (B : LinearMap.BilinForm ℂ K) (ρ : K →ₗ⋆[ℂ] K) : SesqForm K where
  toFun x y := B (ρ x) y
  add_left a a' b := by simp only [map_add, LinearMap.add_apply]
  smul_left z a b := by
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  add_right a b b' := by simp only [map_add]
  smul_right z a b := by simp only [map_smul, smul_eq_mul]

@[simp] theorem sesqOfBilin_apply (B : LinearMap.BilinForm ℂ K) (ρ : K →ₗ⋆[ℂ] K) (x y : K) :
    sesqOfBilin B ρ x y = B (ρ x) y := rfl

theorem neg_one_zpow_mul_self (b : ℤ) : (-1 : ℂ) ^ b * (-1 : ℂ) ^ b = 1 := by
  rw [← mul_zpow]; norm_num

theorem neg_one_zpow_neg (b : ℤ) : (-1 : ℂ) ^ (-b) = (-1 : ℂ) ^ b := by
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

namespace GoodHalf

variable (H : GoodHalf K)

/-- **The Beem–Garner package** on the minimal input (see the module docstring). -/
structure Sp2Package where
  Λ : K →ₗ[ℂ] K
  shift : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), Λ x ∈ H.deg (j, g - 2)
  B : LinearMap.BilinForm ℂ K
  ρ : K →ₗ⋆[ℂ] K
  P_eq : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), ∀ y, H.P x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), ρ x ∈ H.deg (j, -g)
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g),
    ρ (H.D x) = (κ * (-1 : ℂ) ^ g) • (Λ.comp H.D - H.D.comp Λ) (ρ x)
  B_E : ∀ j g : ℤ, ∀ u ∈ H.deg (j, g), ∀ v,
    B ((Λ.comp H.D - H.D.comp Λ) u) v = -((-1 : ℂ) ^ g) * B u ((Λ.comp H.D - H.D.comp Λ) v)

variable {H}

/-- The commutator of `𝐐⁻` with a `(0, -2)`-shift is good for the second differential. -/
theorem commutator_good {Λ : K →ₗ[ℂ] K}
    (hΛ : ∀ j g : ℤ, ∀ x ∈ H.deg (j, g), Λ x ∈ H.deg (j, g - 2)) (j g : ℤ) (y : K)
    (hy : y ∈ H.deg (j, g)) :
    (Λ.comp H.D - H.D.comp Λ) y ∈ H.deg ((j, g) + shQp) ⊔ H.deg ((j, g) + shSp) := by
  have hD := H.D_good (j, g) y hy
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hD
  have hΛy := hΛ j g y hy
  have hD' := H.D_good (j, g - 2) _ hΛy
  obtain ⟨u', hu', v', hv', huv'⟩ := Submodule.mem_sup.mp hD'
  have hΛu := hΛ (j + 1) (g + 1) u hu
  have hΛv := hΛ (j + -1) (g + 1) v hv
  have e1 : ((j + 1, g + 1 - 2) : ℤ × ℤ) = (j, g) + shQp :=
    Prod.ext (by simp [shQp]) (by simp [shQp]; ring)
  have e2 : ((j + -1, g + 1 - 2) : ℤ × ℤ) = (j, g) + shSp :=
    Prod.ext (by simp [shSp]) (by simp [shSp]; ring)
  have e3 : ((j, g - 2) + shQm : ℤ × ℤ) = (j, g) + shQp :=
    Prod.ext (by simp [shQm, shQp]) (by simp [shQm, shQp]; ring)
  have e4 : ((j, g - 2) + shSm : ℤ × ℤ) = (j, g) + shSp :=
    Prod.ext (by simp [shSm, shSp]) (by simp [shSm, shSp]; ring)
  rw [e1] at hΛu
  rw [e2] at hΛv
  rw [e3] at hu'
  rw [e4] at hv'
  have hE : (Λ.comp H.D - H.D.comp Λ) y = (Λ u - u') + (Λ v - v') := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, ← huv, ← huv', map_add]
    abel
  rw [hE]
  exact Submodule.add_mem_sup (Submodule.sub_mem _ hΛu hu') (Submodule.sub_mem _ hΛv hv')

/-- Two homogeneous vectors of distinct bidegrees with zero sum vanish (positive form). -/
theorem eq_zero_of_add_eq_zero' (hpos : IsPosOn H.P ⊤) {a b : ℤ × ℤ} (hab : a ≠ b) {p q : K}
    (hp : p ∈ H.deg a) (hq : q ∈ H.deg b) (h : p + q = 0) : p = 0 := by
  apply eq_zero_of_sesq_self_eq_zero H.P hpos
  have : p = -q := eq_neg_of_add_eq_zero_left h
  calc H.P p p = H.P p (-q) := by rw [← this]
    _ = -H.P p q := by rw [← neg_one_smul ℂ q, H.P.smul_right]; ring
    _ = 0 := by rw [H.orth a b hab p hp q hq, neg_zero]

/-- Uniqueness of a two-term homogeneous decomposition. -/
theorem decomp_unique (hpos : IsPosOn H.P ⊤) {a b : ℤ × ℤ} (hab : a ≠ b) {p q p' q' : K}
    (hp : p ∈ H.deg a) (hq : q ∈ H.deg b) (hp' : p' ∈ H.deg a) (hq' : q' ∈ H.deg b)
    (h : p + q = p' + q') : p = p' ∧ q = q' := by
  have h0 : (p - p') + (q - q') = 0 := by rw [sub_add_sub_comm, h, sub_self]
  have h1 := H.eq_zero_of_add_eq_zero' hpos hab (Submodule.sub_mem _ hp hp')
    (Submodule.sub_mem _ hq hq') h0
  refine ⟨sub_eq_zero.mp h1, ?_⟩
  rw [h1, zero_add] at h0
  exact sub_eq_zero.mp h0

namespace Sp2Package

/-- `E = [Λ, 𝐐⁻]`. -/
def E (Pk : H.Sp2Package) : K →ₗ[ℂ] K := Pk.Λ.comp H.D - H.D.comp Pk.Λ

/-- The normalization `c = -iκ`. -/
def c (Pk : H.Sp2Package) : ℂ := -Complex.I * Pk.κ

theorem c_ne_zero (Pk : H.Sp2Package) : Pk.c ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) Pk.hκ

theorem E_good (Pk : H.Sp2Package) (j g : ℤ) (y : K) (hy : y ∈ H.deg (j, g)) :
    Pk.E y ∈ H.deg ((j, g) + shQp) ⊔ H.deg ((j, g) + shSp) :=
  H.commutator_good Pk.shift j g y hy

/-- `B` pairs bidegree `p` only with `(p.1, -p.2)`. -/
theorem B_pair_zero (Pk : H.Sp2Package) {p q : ℤ × ℤ} {w z : K}
    (hw : w ∈ H.deg p) (hz : z ∈ H.deg q) (hne : q ≠ (p.1, -p.2)) : Pk.B w z = 0 := by
  obtain ⟨c, d⟩ := p
  set w0 := (starRingEnd ℂ) Pk.s⁻¹ • Pk.ρ w with hw0
  have hρw0 : Pk.ρ w0 = w := by
    rw [hw0, LinearMap.map_smulₛₗ, Pk.ρ_sq, smul_smul]
    simp only [starRingEnd_apply, star_star]
    rw [inv_mul_cancel₀ Pk.hs, one_smul]
  have hw0d : w0 ∈ H.deg (c, -d) := Submodule.smul_mem _ _ (Pk.ρ_deg c d w hw)
  have hP := Pk.P_eq c (-d) w0 hw0d z
  rw [hρw0, H.orth _ _ (Ne.symm hne) w0 hw0d z hz] at hP
  have hI : Complex.I ^ c ≠ 0 := zpow_ne_zero _ Complex.I_ne_zero
  exact (mul_eq_zero.mp hP.symm).resolve_left hI

/-- **The pairing identities**: for `w` of bidegree `(a, e)` with `E w = h' + l'` and `y` of
bidegree `(j, g)` with `E y = U + V`, `B(h', y) = -(-1)^e B(w, V)` and
`B(l', y) = -(-1)^e B(w, U)`. -/
theorem pair_identities (Pk : H.Sp2Package) {a e j g : ℤ} {w y h' l' U V : K}
    (hw : w ∈ H.deg (a, e)) (hy : y ∈ H.deg (j, g))
    (hh : h' ∈ H.deg ((a, e) + shQp)) (hl : l' ∈ H.deg ((a, e) + shSp))
    (hU : U ∈ H.deg ((j, g) + shQp)) (hV : V ∈ H.deg ((j, g) + shSp))
    (hEw : Pk.E w = h' + l') (hEy : Pk.E y = U + V) :
    Pk.B h' y = -((-1 : ℂ) ^ e) * Pk.B w V ∧ Pk.B l' y = -((-1 : ℂ) ^ e) * Pk.B w U := by
  have hBE : Pk.B (h' + l') y = -((-1 : ℂ) ^ e) * (Pk.B w U + Pk.B w V) := by
    rw [← hEw, ← map_add, ← hEy]
    exact Pk.B_E a e w hw y
  rw [map_add, LinearMap.add_apply] at hBE
  constructor
  · by_cases hc : j = a + 1 ∧ g = 1 - e
    · obtain ⟨rfl, rfl⟩ := hc
      have h1 : Pk.B l' y = 0 := Pk.B_pair_zero hl hy (by
        intro h; simp only [shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      have h2 : Pk.B w U = 0 := Pk.B_pair_zero hw hU (by
        intro h; simp only [shQp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      rw [h1, h2, add_zero, zero_add] at hBE
      exact hBE
    · have h1 : Pk.B h' y = 0 := Pk.B_pair_zero hh hy (by
        intro h; simp only [shQp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      have h2 : Pk.B w V = 0 := Pk.B_pair_zero hw hV (by
        intro h; simp only [shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      rw [h1, h2, mul_zero]
  · by_cases hc : j = a - 1 ∧ g = 1 - e
    · obtain ⟨rfl, rfl⟩ := hc
      have h1 : Pk.B h' y = 0 := Pk.B_pair_zero hh hy (by
        intro h; simp only [shQp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      have h2 : Pk.B w V = 0 := Pk.B_pair_zero hw hV (by
        intro h; simp only [shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      rw [h1, h2, add_zero, zero_add] at hBE
      exact hBE
    · have h1 : Pk.B l' y = 0 := Pk.B_pair_zero hl hy (by
        intro h; simp only [shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      have h2 : Pk.B w U = 0 := Pk.B_pair_zero hw hU (by
        intro h; simp only [shQp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega)
      rw [h1, h2, mul_zero]

/-- `[cΛ, 𝐐⁻] = c [Λ, 𝐐⁻]`. -/
theorem smul_commutator (Pk : H.Sp2Package) :
    (Pk.c • Pk.Λ).comp H.D - H.D.comp (Pk.c • Pk.Λ) = Pk.c • Pk.E := by
  ext x
  simp only [E, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    smul_sub]

/-- **Beem–Garner Lemma 3.16 from the package**: with `c = -iκ`, `⟨𝐐⁻ x | y⟩ = ⟨x | v - u⟩`
whenever `c E y = u + v` with `u` raising and `v` lowering `2R`. -/
theorem adjoint (Pk : H.Sp2Package) (hpos : IsPosOn H.P ⊤) (x : K) (j g : ℤ) (y : K)
    (hy : y ∈ H.deg (j, g)) (u : K) (hu : u ∈ H.deg ((j, g) + shQp)) (v : K)
    (hv : v ∈ H.deg ((j, g) + shSp)) (huv : (Pk.c • Pk.E) y = u + v) :
    H.P (H.D x) y = H.P x (v - u) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := Submodule.mem_sup.mp (Pk.E_good j g y hy)
  have hne : (j, g) + shQp ≠ (j, g) + shSp := by
    intro h; simp only [shQp, shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega
  have hcUV : u + v = Pk.c • U + Pk.c • V := by
    rw [← huv, LinearMap.smul_apply, ← hUV, smul_add]
  obtain ⟨rfl, rfl⟩ := H.decomp_unique hpos hne hu hv (Submodule.smul_mem _ _ hU)
    (Submodule.smul_mem _ _ hV) hcUV
  refine H.forall_of_deg (fun x => H.P (H.D x) y = H.P x (Pk.c • V - Pk.c • U)) ?_ ?_ ?_ x
  · simp [H.P.zero_left]
  · intro x x' hx hx'
    beta_reduce at hx hx' ⊢
    rw [map_add, H.P.add_left, H.P.add_left, hx, hx']
  · rintro ⟨a, b⟩ x hx
    have hw : Pk.ρ x ∈ H.deg (a, -b) := Pk.ρ_deg a b x hx
    obtain ⟨q, hq, r, hr, hqr⟩ := Submodule.mem_sup.mp (H.D_good (a, b) x hx)
    have hq' : q ∈ H.deg (a + 1, b + 1) := hq
    have hr' : r ∈ H.deg (a + -1, b + 1) := hr
    obtain ⟨h', hh, l', hl, hhl⟩ := Submodule.mem_sup.mp (Pk.E_good a (-b) (Pk.ρ x) hw)
    have hρq : Pk.ρ q ∈ H.deg ((a, -b) + shQp) := by
      have h0 := Pk.ρ_deg (a + 1) (b + 1) q hq'
      have e : ((a, -b) + shQp : ℤ × ℤ) = (a + 1, -(b + 1)) :=
        Prod.ext (by simp [shQp]) (by simp [shQp]; ring)
      rw [e]; exact h0
    have hρr : Pk.ρ r ∈ H.deg ((a, -b) + shSp) := by
      have h0 := Pk.ρ_deg (a + -1) (b + 1) r hr'
      have e : ((a, -b) + shSp : ℤ × ℤ) = (a + -1, -(b + 1)) :=
        Prod.ext (by simp [shSp]) (by simp [shSp]; ring)
      rw [e]; exact h0
    have hneQS : (a, -b) + shQp ≠ (a, -b) + shSp := by
      intro h; simp only [shQp, shSp, Prod.mk_add_mk, Prod.mk.injEq] at h; omega
    have hρD : Pk.ρ q + Pk.ρ r = (Pk.κ * (-1 : ℂ) ^ b) • h' + (Pk.κ * (-1 : ℂ) ^ b) • l' := by
      rw [← map_add, hqr, Pk.ρ_D a b x hx, ← smul_add, hhl]
      rfl
    obtain ⟨e1, e2⟩ := H.decomp_unique hpos hneQS hρq hρr (Submodule.smul_mem _ _ hh)
      (Submodule.smul_mem _ _ hl) hρD
    obtain ⟨p1, p2⟩ := Pk.pair_identities hw hy hh hl hU hV hhl.symm hUV.symm
    have hL : H.P (H.D x) y = Complex.I ^ (a + 1) * Pk.B (Pk.ρ q) y +
        Complex.I ^ (a + -1) * Pk.B (Pk.ρ r) y := by
      rw [← hqr, H.P.add_left, Pk.P_eq (a + 1) (b + 1) q hq' y,
        Pk.P_eq (a + -1) (b + 1) r hr' y]
    rw [hL, e1, e2, Pk.P_eq a b x hx]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_sub]
    rw [p1, p2, neg_one_zpow_neg, zpow_add₀ Complex.I_ne_zero, zpow_add₀ Complex.I_ne_zero,
      zpow_one, zpow_neg_one, Complex.inv_I]
    have ht := neg_one_zpow_mul_self b
    unfold c
    linear_combination (-(Complex.I ^ a) * Complex.I * Pk.κ * Pk.B (Pk.ρ x) V +
      Complex.I ^ a * Complex.I * Pk.κ * Pk.B (Pk.ρ x) U) * ht

/-- **The `sp(2)` adjoint input from the package**, for `Λ' = c Λ`. -/
def toSp2Adjoint (Pk : H.Sp2Package) (hpos : IsPosOn H.P ⊤) : H.Sp2Adjoint where
  Λ := Pk.c • Pk.Λ
  shift := fun j g x hx => Submodule.smul_mem _ _ (Pk.shift j g x hx)
  adjoint := fun x j g y hy u hu v hv huv =>
    Pk.adjoint hpos x j g y hy u hu v hv (by rw [← Pk.smul_commutator]; exact huv)

theorem toSp2Adjoint_E (Pk : H.Sp2Package) (hpos : IsPosOn H.P ⊤) :
    (Pk.toSp2Adjoint hpos).E = Pk.c • Pk.E := Pk.smul_commutator

/-- **The Kähler relation from the package.** -/
theorem kahlerAnticomm [FiniteDimensional ℂ K] (Pk : H.Sp2Package) (hpos : IsPosOn H.P ⊤) :
    H.KahlerAnticomm hpos :=
  (Pk.toSp2Adjoint hpos).kahlerAnticomm hpos

/-- **The ghost-number-zero conjugation input from the package**, with `κ₀ = i`, for any good
complex with the same form, grading and differential. -/
def toSp2Conj0 (Pk : H.Sp2Package) (hpos : IsPosOn H.P ⊤) (G : GoodComplex K)
    (hP : G.P = H.P) (hdeg : G.deg = H.deg) (hD : G.D = H.D) :
    Sp2Conj0 G (Pk.toSp2Adjoint hpos).E where
  B := Pk.B
  ρ := Pk.ρ
  h := sesqOfBilin Pk.B Pk.ρ
  h_eq := fun _ _ => rfl
  P_eq := fun j g x hx y => by
    rw [hP]; rw [hdeg] at hx; exact Pk.P_eq j g x hx y
  ρ_deg := fun j g x hx => by
    rw [hdeg] at hx ⊢; exact Pk.ρ_deg j g x hx
  κ := Complex.I
  hκ := Complex.I_ne_zero
  ρ_D0 := fun j x hx => by
    rw [hdeg] at hx
    rw [hD, Pk.ρ_D j 0 x hx, toSp2Adjoint_E, LinearMap.smul_apply, smul_smul, zpow_zero,
      mul_one]
    congr 1
    unfold c
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  s := Pk.s
  hs := Pk.hs
  ρ_sq := Pk.ρ_sq

end Sp2Package

end GoodHalf

/-! ### The interpreted complex -/

section Interpreted

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- **OPEN input: the Beem–Garner package for the actual relative complex**, at every weight:
`Λ`, the invariant bilinear form `B`, the conjugation `ρ`, `P_eq`, `ρ² = s`, the twisted
intertwining `ρ 𝐐⁻ = κ (-1)^{gh} [Λ, 𝐐⁻] ρ` and super-skewness of `[Λ, 𝐐⁻]` for `B`. -/
abbrev InterpretedBGPackage : Type :=
  ∀ n : ℤ, (interpretedHalf Gh hA hB hG hZ hD n).Sp2Package

variable {Gh hA hB hG hZ hD}

/-- The `sp(2)` adjoint input from the package. -/
def InterpretedBGPackage.sp2 (Pk : InterpretedBGPackage Gh hA hB hG hZ hD) :
    InterpretedSp2 Gh hA hB hG hZ hD :=
  fun n => (Pk n).toSp2Adjoint (interpretedHalf_pos Gh hA hB hG hZ hD n)

/-- **`InterpretedKahlerAnticomm` from the package.** -/
theorem InterpretedBGPackage.kahlerAnticomm (Pk : InterpretedBGPackage Gh hA hB hG hZ hD) :
    InterpretedKahlerAnticomm Gh hA hB hG hZ hD :=
  interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD Pk.sp2

/-- **The ghost-number-zero conjugation input from the package.** -/
def InterpretedBGPackage.conj0 (Pk : InterpretedBGPackage Gh hA hB hG hZ hD) (n : ℤ) hp :
    Sp2Conj0 (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD Pk.sp2)) n hp) (Pk.sp2 n).E :=
  (Pk n).toSp2Conj0 (interpretedHalf_pos Gh hA hB hG hZ hD n) _ rfl rfl rfl

end Interpreted

/-- **Affine GU ⇒ Lee–Yang GU from one Beem–Garner package per weight**, for an arbitrary
positive ghost form with the standard grading. Both the Kähler relation and the conjugation
datum are derived from the package. `#print axioms`-clean, conditional on: `hA` (the
hypothesis), `hB` (unitarity of `L_1`), `hG` (ghost positivity), `hs` (standard ghost grading),
`Pk` (the package), and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgPackage
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (Pk : InterpretedBGPackage Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (symbols : LeadingInvariantSymbolDimension (sp2Kahler hA hB hG Gh hs Pk.sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0))
    (creationAdjoint : HarmonicCreationAdjoint (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0))
    (wordsReal : HarmonicWordsReal (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_sp2_conj0 hA hB hG Gh hs Pk.sp2 Pk.conj0 symbols character
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
