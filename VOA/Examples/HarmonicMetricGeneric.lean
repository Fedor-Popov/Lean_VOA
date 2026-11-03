/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GhostConjPackage
import VOA.Examples.LeeYangShortcutHodge

/-!
# Harmonic representatives can be replaced by arbitrary closed representatives

Generic layer for the three harmonic-metric inputs of the Lee–Yang shortcut. For a good complex
with a bilinear form `B` and conjugation `ρ` satisfying `P = i^{2R} B(ρ ·, ·)`, `ρ² = s`, and the
**all-ghost-number** intertwining `ρ 𝐐⁻ = μ_g 𝐐⁺ ρ` (which the corrected Beem–Garner package
provides), we prove:

* `harm_le_iSup_harmDeg` — every harmonic vector is a sum of bihomogeneous harmonic vectors;
* `AllGhostConj.B_harm_D` — `B(v, 𝐐⁻ w) = 0` for harmonic `v`;
* `AllGhostConj.B_D_closed` — `B(𝐐⁻ z, x) = 0` for closed `x` (any `z`);
* `AllGhostConj.B_eq_of_classes` — if harmonic `v, v'` represent the classes of closed `x, x'`,
  then `B(v, v') = B(x, x')`;
* `AllGhostConj.rho_fix_of_class` — if harmonic `v` represents the class of a closed `x` with
  `ρ x = x`, then `ρ v = v`;
* `harmonicClassLift_sub_mem_range` — the harmonic lift of the class of a cycle differs from the
  cycle by a boundary.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.LeeYangTransferAssembly
open LeeYangShortcut

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-! ### Harmonic vectors are sums of bihomogeneous harmonic vectors -/

theorem harm_le_iSup_harmDeg (C : KahlerComplex K) {v : K} (hv : v ∈ C.harm) :
    v ∈ ⨆ a, C.harmDeg a := by
  classical
  have hv' : v ∈ iSup C.deg := C.span ▸ Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv'
  clear hv'
  induction s using Finset.induction_on generalizing v with
  | empty =>
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
      subst hs; exact Submodule.zero_mem _
  | insert a s has ih =>
      rw [Finset.iSup_insert] at hs
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hs
      have hyA : y ∈ C.degOn {a} := C.deg_le_degOn (Set.mem_singleton a) hy
      have hzA : z ∈ C.degOn ({a} : Set (ℤ × ℤ))ᶜ := by
        refine (iSup₂_le fun b hb => C.deg_le_degOn ?_ : (⨆ b ∈ s, C.deg b) ≤ _) hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl; exact has hb
      obtain ⟨hyh, hzh⟩ := C.harm_split {a} hyA hzA hv
      refine Submodule.add_mem _ ?_ (ih hzh hz)
      exact (le_iSup C.harmDeg a) ⟨hyh, hy⟩

/-! ### The abstract all-ghost conjugation datum -/

/-- **A form and conjugation on a good complex, intertwining the two differentials at every ghost
number.** `ρ 𝐐⁻ = μ_g 𝐐⁺ ρ` on bidegree `(j, g)`. -/
structure AllGhostConj (G : GoodComplex K) where
  B : LinearMap.BilinForm ℂ K
  ρ : K →ₗ⋆[ℂ] K
  P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g)
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x
  μ : ℤ → ℂ
  hμ : ∀ g, μ g ≠ 0
  ρ_D : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ (G.D x) = μ g • G.Dp (ρ x)

namespace AllGhostConj

variable {G : GoodComplex K} (R : AllGhostConj G)

theorem I_zpow_ne_zero (j : ℤ) : Complex.I ^ j ≠ 0 := zpow_ne_zero _ Complex.I_ne_zero

/-- `ρ` is invertible: `ρ (s̄⁻¹ ρ y) = y`. -/
theorem ρ_inv (y : K) : R.ρ ((starRingEnd ℂ) R.s⁻¹ • R.ρ y) = y := by
  rw [LinearMap.map_smulₛₗ, R.ρ_sq, smul_smul]
  simp only [starRingEnd_apply, star_star]
  rw [inv_mul_cancel₀ R.hs, one_smul]

theorem ρ_injective {x : K} (h : R.ρ x = 0) : x = 0 := by
  have : R.s • x = 0 := by rw [← R.ρ_sq, h, map_zero]
  exact (smul_eq_zero.mp this).resolve_left R.hs

/-- `ρ` of a bihomogeneous harmonic vector is harmonic. -/
theorem ρ_harmDeg {j g : ℤ} {v : K} (hv : v ∈ G.toKahler.harmDeg (j, g)) :
    R.ρ v ∈ G.toKahler.harmDeg (j, -g) := by
  obtain ⟨hvh, hvd⟩ := hv
  change v ∈ G.deg (j, g) at hvd
  obtain ⟨hD, hDp⟩ := G.D_Dp_of_harm hvh
  have hρd : R.ρ v ∈ G.deg (j, -g) := R.ρ_deg j g v hvd
  have h1 : G.D (R.ρ v) = 0 := by
    apply R.ρ_injective
    rw [R.ρ_D j (-g) _ hρd, R.ρ_sq, map_smul, hDp, smul_zero, smul_zero]
  have h2 : G.Dp (R.ρ v) = 0 := by
    have := R.ρ_D j g v hvd
    rw [hD, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (R.hμ g)
  exact ⟨G.mem_harm_of_D_Dp hρd h1 h2, hρd⟩

/-- `ρ` preserves the harmonic space. -/
theorem ρ_harm {v : K} (hv : v ∈ G.toKahler.harm) : R.ρ v ∈ G.toKahler.harm := by
  have hmem := harm_le_iSup_harmDeg G.toKahler hv
  refine Submodule.iSup_induction G.toKahler.harmDeg (motive := fun v => R.ρ v ∈ G.toKahler.harm)
    hmem ?_ (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  rintro ⟨j, g⟩ x hx
  exact (R.ρ_harmDeg hx).1

/-- **Right slot.** A harmonic vector is `B`-orthogonal to every `𝐐⁻`-exact vector. -/
theorem B_harm_D {v : K} (hv : v ∈ G.toKahler.harm) (w : K) : R.B v (G.D w) = 0 := by
  have hmem := harm_le_iSup_harmDeg G.toKahler hv
  refine Submodule.iSup_induction G.toKahler.harmDeg (motive := fun v => R.B v (G.D w) = 0)
    hmem ?_ (by beta_reduce; rw [map_zero, LinearMap.zero_apply])
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
  rintro ⟨j, g⟩ x hx
  set u := (starRingEnd ℂ) R.s⁻¹ • R.ρ x with hu
  have hu_h : u ∈ G.toKahler.harmDeg (j, -g) :=
    Submodule.smul_mem _ _ (R.ρ_harmDeg hx)
  have hρu : R.ρ u = x := R.ρ_inv x
  have hP := R.P_eq j (-g) u hu_h.2 (G.D w)
  have h0 : G.P u (G.D w) = 0 := by
    have := G.toKahler.P_harm_D u w hu_h.1
    rwa [G.toKahler_D] at this
  rw [h0, hρu] at hP
  exact (mul_eq_zero.mp hP.symm).resolve_left (I_zpow_ne_zero j)

/-- **Left slot.** Every `𝐐⁻`-exact vector is `B`-orthogonal to every closed vector. -/
theorem B_D_closed {x : K} (hx : G.D x = 0) (z : K) : R.B (G.D z) x = 0 := by
  refine G.forall_of_deg (fun z => R.B (G.D z) x = 0)
    (by beta_reduce; rw [map_zero, map_zero, LinearMap.zero_apply])
    (fun z z' hz hz' => by
      beta_reduce at hz hz' ⊢; rw [map_add, map_add, LinearMap.add_apply, hz, hz', add_zero])
    ?_ z
  rintro ⟨j, g⟩ z hz
  beta_reduce
  have hρz : R.ρ z ∈ G.deg (j, -g) := R.ρ_deg j g z hz
  set t : ℂ := (starRingEnd ℂ) R.s⁻¹ * R.μ g with ht
  set q := G.Qp (R.ρ z) with hq
  set r := G.Sp (R.ρ z) with hr
  have hqd : t • q ∈ G.deg (j + 1, -g + -1) :=
    Submodule.smul_mem _ _ (G.Qp_deg (j, -g) _ hρz)
  have hrd : t • r ∈ G.deg (j + -1, -g + -1) :=
    Submodule.smul_mem _ _ (G.Sp_deg (j, -g) _ hρz)
  have hDz : G.D z = R.ρ (t • q) + R.ρ (t • r) := by
    rw [← map_add, ← smul_add, hq, hr, ← LinearMap.add_apply, G.Qp_add_Sp, ht, ← smul_smul,
      ← R.ρ_D j g z hz, R.ρ_inv]
  have hPq := R.P_eq _ _ _ hqd x
  have hPr := R.P_eq _ _ _ hrd x
  -- `P(Q⁺ y, x) = -c P(y, S⁻ x)` and `P(S⁺ y, x) = c P(y, Q⁻ x)`.
  have hAq : G.P q x = -(G.c : ℂ) * G.P (R.ρ z) (G.Sm x) := G.toKahler.adj_Qp (R.ρ z) x
  have hAr : G.P r x = (G.c : ℂ) * G.P (R.ρ z) (G.Qm x) := G.toKahler.adj_Sp (R.ρ z) x
  have hsum : G.P (R.ρ z) (G.Qm x) + G.P (R.ρ z) (G.Sm x) = 0 := by
    rw [← G.P.add_right, ← LinearMap.add_apply, G.Qm_add_Sm, hx, G.P.zero_right]
  have hkey : Complex.I ^ (j + 1) * (R.B (R.ρ (t • q)) x + R.B (R.ρ (t • r)) x) = 0 := by
    have e : Complex.I ^ (j + 1) = Complex.I ^ (2 : ℤ) * Complex.I ^ (j + -1) := by
      rw [← zpow_add₀ Complex.I_ne_zero]; ring_nf
    have hI2 : Complex.I ^ (2 : ℤ) = -1 := by
      rw [zpow_two, Complex.I_mul_I]
    rw [mul_add, ← hPq, e, mul_assoc, ← hPr, hI2, G.P.smul_left, G.P.smul_left, hAq, hAr]
    linear_combination (-(starRingEnd ℂ) t * (G.c : ℂ)) * hsum
  rw [hDz, map_add, LinearMap.add_apply]
  exact (mul_eq_zero.mp hkey).resolve_left (I_zpow_ne_zero _)

/-- **The form on harmonic representatives equals the form on any closed representatives.** -/
theorem B_eq_of_classes {v v' x x' : K} (hv : v ∈ G.toKahler.harm)
    (hx' : G.D x' = 0) (hvx : v - x ∈ LinearMap.range G.D)
    (hvx' : v' - x' ∈ LinearMap.range G.D) : R.B v v' = R.B x x' := by
  obtain ⟨z, hz⟩ := hvx
  obtain ⟨w, hw⟩ := hvx'
  have e1 : v' = x' + G.D w := by rw [hw]; abel
  have e2 : v = x + G.D z := by rw [hz]; abel
  rw [e1, map_add, R.B_harm_D hv w, add_zero, e2, map_add, LinearMap.add_apply,
    R.B_D_closed hx' z, add_zero]

/-- `ρ` of an exact vector is `𝐐⁺`-exact. -/
theorem ρ_D_mem_range (z : K) : R.ρ (G.D z) ∈ LinearMap.range G.Dp := by
  refine G.forall_of_deg (fun z => R.ρ (G.D z) ∈ LinearMap.range G.Dp)
    (by beta_reduce; rw [map_zero, map_zero]; exact Submodule.zero_mem _)
    (fun z z' hz hz' => by
      beta_reduce at hz hz' ⊢; rw [map_add, map_add]; exact Submodule.add_mem _ hz hz')
    ?_ z
  rintro ⟨j, g⟩ z hz
  beta_reduce
  rw [R.ρ_D j g z hz, ← map_smul]
  exact LinearMap.mem_range_self _ _

/-- A harmonic vector of the form `𝐐⁺ y - 𝐐⁻ z` vanishes. -/
theorem harm_eq_zero_of_Dp_sub_D {d y z : K} (hd : d ∈ G.toKahler.harm)
    (h : d = G.Dp y - G.D z) : d = 0 := by
  obtain ⟨h1, h2, _, _⟩ := (G.toKahler.mem_harm_iff d).mp hd
  change G.Qm d = 0 at h1
  change G.Sm d = 0 at h2
  apply G.toKahler.eq_zero_of_self
  have hDz : G.P d (G.D z) = 0 := by
    have := G.toKahler.P_harm_D d z hd
    rwa [G.toKahler_D] at this
  have hQp : G.P d (G.Qp y) = 0 := by
    have := G.toKahler.herm d (G.Qp y)
    change (starRingEnd ℂ) (G.P (G.Qp y) d) = G.P d (G.Qp y) at this
    rw [← this]
    have e := G.toKahler.adj_Qp y d
    change G.P (G.Qp y) d = -(G.c : ℂ) * G.P y (G.Sm d) at e
    rw [e, h2, G.P.zero_right, mul_zero, map_zero]
  have hSp : G.P d (G.Sp y) = 0 := by
    have := G.toKahler.herm d (G.Sp y)
    change (starRingEnd ℂ) (G.P (G.Sp y) d) = G.P d (G.Sp y) at this
    rw [← this]
    have e := G.toKahler.adj_Sp y d
    change G.P (G.Sp y) d = (G.c : ℂ) * G.P y (G.Qm d) at e
    rw [e, h1, G.P.zero_right, mul_zero, map_zero]
  change G.P d d = 0
  have hdd : G.P d d = G.P d (G.Dp y) - G.P d (G.D z) := by
    have e := G.toKahler.P_sub_right d (G.Dp y) (G.D z)
    rw [← h] at e
    exact e
  rw [hdd, hDz, ← G.Qp_add_Sp, LinearMap.add_apply, G.P.add_right, hQp, hSp]
  ring

/-- **Reality passes from a closed representative to the harmonic one.** -/
theorem rho_fix_of_class {v x : K} (hv : v ∈ G.toKahler.harm)
    (hvx : v - x ∈ LinearMap.range G.D) (hρx : R.ρ x = x) : R.ρ v = v := by
  obtain ⟨z, hz⟩ := hvx
  obtain ⟨y, hy⟩ := R.ρ_D_mem_range z
  have e : v = x + G.D z := by rw [hz]; abel
  have hd := harm_eq_zero_of_Dp_sub_D (G := G) (d := R.ρ v - v) (y := y) (z := z)
    (Submodule.sub_mem _ (R.ρ_harm hv) hv) (by
      conv_lhs => rw [e]
      rw [map_add, hρx, hy]; abel)
  exact sub_eq_zero.mp hd

end AllGhostConj

/-! ### The corrected Beem–Garner package gives the all-ghost datum -/

namespace GoodHalf.Sp2PackageI

variable {H : GoodHalf K}

/-- The all-ghost conjugation datum of a corrected package, on any good complex with the same
form, grading and differential, whose second differential is `c E`. -/
def toAllGhostConj (Pk : H.Sp2PackageI) (hpos : IsPosOn H.P ⊤) (G : GoodComplex K)
    (hP : G.P = H.P) (hdeg : G.deg = H.deg) (hD : G.D = H.D)
    (hDp : G.Dp = (Pk.toSp2Adjoint hpos).E) : AllGhostConj G where
  B := Pk.B
  ρ := Pk.ρ
  P_eq := fun j g x hx y => by
    rw [hP]; rw [hdeg] at hx; exact Pk.P_eq j g x hx y
  ρ_deg := fun j g x hx => by
    rw [hdeg] at hx ⊢; exact Pk.ρ_deg j g x hx
  s := Pk.s
  hs := Pk.hs
  ρ_sq := Pk.ρ_sq
  μ := fun g => Pk.κ * (-1 : ℂ) ^ g * Pk.c⁻¹
  hμ := fun g => mul_ne_zero (mul_ne_zero Pk.hκ (zpow_ne_zero _ (by norm_num)))
    (inv_ne_zero Pk.c_ne_zero)
  ρ_D := fun j g x hx => by
    rw [hdeg] at hx
    rw [hD, Pk.ρ_D j g x hx, hDp, toSp2Adjoint_E, LinearMap.smul_apply, smul_smul,
      mul_assoc, inv_mul_cancel₀ Pk.c_ne_zero, mul_one]
    rfl

end GoodHalf.Sp2PackageI

/-! ### Harmonic lifts differ from cycles by boundaries -/

theorem harmonicClassLift_sub_mem_range [FiniteDimensional ℂ K] {U : Type*} [AddCommGroup U]
    [Module ℂ U] (C : KahlerComplex K) (g : U →ₗ[ℂ] LinearMap.ker C.D) (x : U) :
    ((harmonicClassLift C (cycleClassOfCycles C.D g) x : C.harm) : K) - (g x : K) ∈
      LinearMap.range C.D := by
  set v := harmonicClassLift C (cycleClassOfCycles C.D g) x with hv
  have h : harmonicToCohomology C.D C.Dadj v = cycleClassOfCycles C.D g x :=
    (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).apply_symm_apply _
  have h' := (Submodule.Quotient.eq _).mp h
  exact h'

end

end VOA.ConcreteHodge
