/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerPackage

/-!
# The Beem–Garner package with the corrected super-skewness constant

`GoodHalf.Sp2Package` asks for `ρ² = s` (one scalar on every bidegree) **and** for the
super-skewness `B(E u, v) = -(-1)^{gh u} B(u, E v)`. For the actual Lee–Yang relative complex
these two clauses are **incompatible** (numerical certificate at weight `2`, recorded in the report
of this layer): the intertwining `ρ_D` forces `ρ² = κ² · |·|²`-type ratios between the vacuum and
the one-ghost states, so `ρ² = s` forces `κ` real, and then `B_E` fails by exactly a factor `i`.
Beem–Garner's own conjugation squares to the parity automorphism (`ρ ∘ ρ = (-1)^F`); twisting it by
`i^{gh}` makes the square one scalar but multiplies the skewness constant by `i`.

This file states the package with the constant that the actual complex satisfies,

  `B(E u, v) = i (-1)^{gh u} B(u, E v)`,

and proves that it yields the same downstream inputs as `Sp2Package`:

* `GoodHalf.Sp2PackageI.adjoint` — **Beem–Garner Lemma 3.16** with `c = -κ`:
  `⟨𝐐⁻ x | y⟩ = ⟨x | v - u⟩` whenever `c E y = u + v` (`u` raising, `v` lowering `2R`);
* `Sp2PackageI.toSp2Adjoint`, `Sp2PackageI.toSp2Conj0` (with `κ₀ = -1`);
* `InterpretedBGPackageI` (one corrected package per weight) and
  `leeYang_gradedUnitary_of_affine_bgPackageI` — **Affine GU ⇒ Lee–Yang GU** from it.

Numerically (truncated model of the actual complex, relative weights `2, 3, 4`), with `κ = 1`,
`ρ² = 1`
and the explicit ghost conjugation of `GhostConjFock`, `ρ_D` and this `B_E` hold to machine
precision. Everything in this file is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open scoped TensorProduct

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

namespace GoodHalf

variable (H : GoodHalf K)

/-- **The Beem–Garner package with the corrected skewness constant** `i (-1)^{gh}`. -/
structure Sp2PackageI where
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
    B ((Λ.comp H.D - H.D.comp Λ) u) v =
      Complex.I * (-1 : ℂ) ^ g * B u ((Λ.comp H.D - H.D.comp Λ) v)

variable {H}

namespace Sp2PackageI

/-- `E = [Λ, 𝐐⁻]`. -/
def E (Pk : H.Sp2PackageI) : K →ₗ[ℂ] K := Pk.Λ.comp H.D - H.D.comp Pk.Λ

/-- The normalization `c = -κ`. -/
def c (Pk : H.Sp2PackageI) : ℂ := -Pk.κ

theorem c_ne_zero (Pk : H.Sp2PackageI) : Pk.c ≠ 0 := neg_ne_zero.mpr Pk.hκ

theorem E_good (Pk : H.Sp2PackageI) (j g : ℤ) (y : K) (hy : y ∈ H.deg (j, g)) :
    Pk.E y ∈ H.deg ((j, g) + shQp) ⊔ H.deg ((j, g) + shSp) :=
  H.commutator_good Pk.shift j g y hy

/-- `B` pairs bidegree `p` only with `(p.1, -p.2)`. -/
theorem B_pair_zero (Pk : H.Sp2PackageI) {p q : ℤ × ℤ} {w z : K}
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

/-- **The pairing identities** for the corrected constant. -/
theorem pair_identities (Pk : H.Sp2PackageI) {a e j g : ℤ} {w y h' l' U V : K}
    (hw : w ∈ H.deg (a, e)) (hy : y ∈ H.deg (j, g))
    (hh : h' ∈ H.deg ((a, e) + shQp)) (hl : l' ∈ H.deg ((a, e) + shSp))
    (hU : U ∈ H.deg ((j, g) + shQp)) (hV : V ∈ H.deg ((j, g) + shSp))
    (hEw : Pk.E w = h' + l') (hEy : Pk.E y = U + V) :
    Pk.B h' y = Complex.I * (-1 : ℂ) ^ e * Pk.B w V ∧
      Pk.B l' y = Complex.I * (-1 : ℂ) ^ e * Pk.B w U := by
  have hBE : Pk.B (h' + l') y = Complex.I * (-1 : ℂ) ^ e * (Pk.B w U + Pk.B w V) := by
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
theorem smul_commutator (Pk : H.Sp2PackageI) :
    (Pk.c • Pk.Λ).comp H.D - H.D.comp (Pk.c • Pk.Λ) = Pk.c • Pk.E := by
  ext x
  simp only [E, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    smul_sub]

/-- **Beem–Garner Lemma 3.16 from the corrected package**: with `c = -κ`,
`⟨𝐐⁻ x | y⟩ = ⟨x | v - u⟩` whenever `c E y = u + v` with `u` raising and `v` lowering `2R`. -/
theorem adjoint (Pk : H.Sp2PackageI) (hpos : IsPosOn H.P ⊤) (x : K) (j g : ℤ) (y : K)
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
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    unfold c
    linear_combination (Complex.I ^ a * Pk.κ * (-Pk.B (Pk.ρ x) V + Pk.B (Pk.ρ x) U)) * ht +
      (Complex.I ^ a * Pk.κ * ((-1 : ℂ) ^ b * (-1 : ℂ) ^ b) *
        (Pk.B (Pk.ρ x) V - Pk.B (Pk.ρ x) U)) * hI2

/-- **The `sp(2)` adjoint input from the corrected package**, for `Λ' = c Λ`. -/
def toSp2Adjoint (Pk : H.Sp2PackageI) (hpos : IsPosOn H.P ⊤) : H.Sp2Adjoint where
  Λ := Pk.c • Pk.Λ
  shift := fun j g x hx => Submodule.smul_mem _ _ (Pk.shift j g x hx)
  adjoint := fun x j g y hy u hu v hv huv =>
    Pk.adjoint hpos x j g y hy u hu v hv (by rw [← Pk.smul_commutator]; exact huv)

theorem toSp2Adjoint_E (Pk : H.Sp2PackageI) (hpos : IsPosOn H.P ⊤) :
    (Pk.toSp2Adjoint hpos).E = Pk.c • Pk.E := Pk.smul_commutator

/-- **The ghost-number-zero conjugation input from the corrected package**, with
`κ₀ = -1`. -/
def toSp2Conj0 (Pk : H.Sp2PackageI) (hpos : IsPosOn H.P ⊤) (G : GoodComplex K)
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
  κ := -1
  hκ := by norm_num
  ρ_D0 := fun j x hx => by
    rw [hdeg] at hx
    rw [hD, Pk.ρ_D j 0 x hx, toSp2Adjoint_E, LinearMap.smul_apply, smul_smul, zpow_zero,
      mul_one]
    congr 1
    unfold c
    ring
  s := Pk.s
  hs := Pk.hs
  ρ_sq := Pk.ρ_sq

end Sp2PackageI

end GoodHalf

/-! ### The interpreted complex -/

section Interpreted

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- **The corrected Beem–Garner package for the actual relative complex**, at every weight. -/
abbrev InterpretedBGPackageI : Type :=
  ∀ n : ℤ, (interpretedHalf Gh hA hB hG hZ hD n).Sp2PackageI

variable {Gh hA hB hG hZ hD}

/-- The `sp(2)` adjoint input from the corrected package. -/
def InterpretedBGPackageI.sp2 (Pk : InterpretedBGPackageI Gh hA hB hG hZ hD) :
    InterpretedSp2 Gh hA hB hG hZ hD :=
  fun n => (Pk n).toSp2Adjoint (interpretedHalf_pos Gh hA hB hG hZ hD n)

/-- The ghost-number-zero conjugation input from the corrected package. -/
def InterpretedBGPackageI.conj0 (Pk : InterpretedBGPackageI Gh hA hB hG hZ hD) (n : ℤ) hp :
    Sp2Conj0 (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD Pk.sp2)) n hp) (Pk.sp2 n).E :=
  (Pk n).toSp2Conj0 (interpretedHalf_pos Gh hA hB hG hZ hD n) _ rfl rfl rfl

end Interpreted

/-- **Affine GU ⇒ Lee–Yang GU from one corrected Beem–Garner package per weight**.
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB`, `hG`, `hs`, `Pk` (the
corrected package) and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgPackageI
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
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
