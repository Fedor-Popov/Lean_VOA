/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GradedUnitaryCohomologyTransfer
import VOA.Core.InternalGradingOperator

/-!
# From a good differential to the Kähler package (Beem–Garner Lemma 3.16, linear-algebra half)

Third layer of the concrete Beem–Garner instantiation. `KahlerComplex` takes the four
`ℜ`-homogeneous pieces `Q⁻, S⁻, Q⁺, S⁺` and *four* adjoint relations as data. Here they are
produced from what a concrete BRST complex actually provides:

* a positive form `P` and a `P`-orthogonal spanning bigrading `deg` by `(2R, gh)`;
* the two bold differentials `𝐐⁻ = D` and `𝐐⁺ = Dp`;
* **goodness** (Beem–Garner Definition 3.12, in the form used in Lemma 3.16): `D` has *no*
  `ℜ`-preserving component — it maps `deg a` into `deg (a + (1,1)) ⊔ deg (a + (-1,1))`, and `Dp`
  maps `deg a` into `deg (a + (1,-1)) ⊔ deg (a + (-1,-1))`;
* a **single** adjoint relation `(𝐐⁻)† = c (S⁺ - Q⁺)` (Beem–Garner Eq. (3.5));
* `(𝐐⁻)² = 0` and `𝐐⁻𝐐⁺ + 𝐐⁺𝐐⁻ = 0`.

The pieces are *defined* from the grading operator `Rop` (`2R` on `deg (2R, gh)`) by
`hiPart T = ½ (T + [Rop, T])`, `loPart T = ½ (T - [Rop, T])`; goodness makes them the
`R`-raising and `R`-lowering components. The four adjoint relations of `KahlerComplex` are then
*derived* from the single bold one by degree splitting.

* `GoodGeometry` — the input structure (no positivity), with the derived pieces `Qm, Sm, Qp, Sp`,
  their degree properties and the derived adjoint relations `adj_Qm`, `adj_Sm`.
* `GoodComplex` (= `GoodGeometry` + positivity) and `GoodComplex.toKahler`, with
  `toKahler_D : D = 𝐐⁻`.
* The grading operator `Rop` is a field; `ConcreteHodgeGU.degOperator` shows that a positive
  orthogonal bigrading always has one, so it is not extra data in practice.

Everything here is proved outright from the listed hypotheses. Nothing here proves goodness or
the adjoint relation for the concrete relative complex; those are the inputs of
`ConcreteHodgeAssembly`.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open Module (finrank)

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-- The `R`-raising part `½ (T + [Rop, T])` of an operator with `R`-shifts `±1/2`. -/
def hiPart (Rop T : K →ₗ[ℂ] K) : K →ₗ[ℂ] K :=
  (1 / 2 : ℂ) • (T + Rop.comp T - T.comp Rop)

/-- The `R`-lowering part `½ (T - [Rop, T])`. -/
def loPart (Rop T : K →ₗ[ℂ] K) : K →ₗ[ℂ] K :=
  (1 / 2 : ℂ) • (T - Rop.comp T + T.comp Rop)

theorem hiPart_add_loPart (Rop T : K →ₗ[ℂ] K) : hiPart Rop T + loPart Rop T = T := by
  ext x
  simp only [hiPart, loPart, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]
  module

/-- If `T x = u + v` with `u` of `2R`-degree `j+1` and `v` of `2R`-degree `j-1`, and `x` of degree
`j`, then `hiPart T x = u` and `loPart T x = v`. -/
theorem hiPart_loPart_apply (Rop T : K →ₗ[ℂ] K) (j : ℤ) {x u v : K}
    (hx : Rop x = (j : ℂ) • x) (hu : Rop u = ((j + 1 : ℤ) : ℂ) • u)
    (hv : Rop v = ((j - 1 : ℤ) : ℂ) • v) (hT : T x = u + v) :
    hiPart Rop T x = u ∧ loPart Rop T x = v := by
  have h1 : Rop (T x) = ((j + 1 : ℤ) : ℂ) • u + ((j - 1 : ℤ) : ℂ) • v := by
    rw [hT, map_add, hu, hv]
  have h2 : T (Rop x) = (j : ℂ) • (u + v) := by rw [hx, map_smul, hT]
  push_cast at h1
  constructor
  · simp only [hiPart, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [h1, h2, hT]
    module
  · simp only [loPart, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [h1, h2, hT]
    module

/-- **A good BRST complex at one conformal weight, before positivity**: the data a concrete
instantiation supplies. See the module docstring for the dictionary with Beem–Garner. -/
structure GoodGeometry (K : Type u) [AddCommGroup K] [Module ℂ K] where
  /-- The modified Hermitian form. -/
  P : SesqForm K
  /-- The bigrading by `(2R, ghost number)`. -/
  deg : ℤ × ℤ → Submodule ℂ K
  span : iSup deg = ⊤
  orth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0
  /-- The `2R` grading operator. -/
  Rop : K →ₗ[ℂ] K
  Rop_deg : ∀ j g : ℤ, ∀ x ∈ deg (j, g), Rop x = (j : ℂ) • x
  /-- `𝐐⁻`. -/
  D : K →ₗ[ℂ] K
  /-- `𝐐⁺`. -/
  Dp : K →ₗ[ℂ] K
  /-- **Goodness**: `𝐐⁻` has no `ℜ`-preserving component and raises the ghost number by one. -/
  D_good : ∀ a, ∀ x ∈ deg a, D x ∈ deg (a + shQm) ⊔ deg (a + shSm)
  /-- `𝐐⁺` has no `ℜ`-preserving component and lowers the ghost number by one. -/
  Dp_good : ∀ a, ∀ x ∈ deg a, Dp x ∈ deg (a + shQp) ⊔ deg (a + shSp)
  /-- The sign `ε_{-+}`. -/
  c : ℝ
  c_sq : c * c = 1
  /-- **Beem–Garner Eq. (3.5)**: `(𝐐⁻)† = c (S⁺ - Q⁺)`. -/
  adj : ∀ x y, P (D x) y = (c : ℂ) * P x (loPart Rop Dp y - hiPart Rop Dp y)
  sq_zero : D.comp D = 0
  anticomm : D.comp Dp + Dp.comp D = 0

/-- **A good BRST complex**: a good geometry whose form is positive definite (weak graded
unitarity). -/
structure GoodComplex (K : Type u) [AddCommGroup K] [Module ℂ K] extends GoodGeometry K where
  /-- Weak graded unitarity: `P` is positive definite. -/
  pos : IsPosOn P ⊤

namespace GoodGeometry

variable (G : GoodGeometry K)

theorem P_sub_right (x y z : K) : G.P x (y - z) = G.P x y - G.P x z := by
  rw [sub_eq_add_neg, G.P.add_right, ← neg_one_smul ℂ z, G.P.smul_right]; ring

/-- Splitting an operator with `2R`-shifts `±1` and ghost shift `e` into its two parts. -/
theorem parts_mem (T : K →ₗ[ℂ] K) (e : ℤ)
    (hT : ∀ a, ∀ x ∈ G.deg a, T x ∈ G.deg (a + (1, e)) ⊔ G.deg (a + (-1, e)))
    (a : ℤ × ℤ) {x : K} (hx : x ∈ G.deg a) :
    hiPart G.Rop T x ∈ G.deg (a + (1, e)) ∧ loPart G.Rop T x ∈ G.deg (a + (-1, e)) := by
  obtain ⟨j, g⟩ := a
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hT _ x hx)
  have hu' : G.Rop u = ((j + 1 : ℤ) : ℂ) • u := G.Rop_deg (j + 1) (g + e) u hu
  have hv' : G.Rop v = ((j - 1 : ℤ) : ℂ) • v := by
    have := G.Rop_deg (j + -1) (g + e) v hv
    rw [this]; congr 2
  obtain ⟨h1, h2⟩ := hiPart_loPart_apply G.Rop T j (G.Rop_deg j g x hx) hu' hv' huv.symm
  rw [h1, h2]
  exact ⟨hu, hv⟩

/-- `Q⁻`. -/
def Qm : K →ₗ[ℂ] K := hiPart G.Rop G.D
/-- `S⁻`. -/
def Sm : K →ₗ[ℂ] K := loPart G.Rop G.D
/-- `Q⁺`. -/
def Qp : K →ₗ[ℂ] K := hiPart G.Rop G.Dp
/-- `S⁺`. -/
def Sp : K →ₗ[ℂ] K := loPart G.Rop G.Dp

theorem Qm_add_Sm : G.Qm + G.Sm = G.D := hiPart_add_loPart _ _
theorem Qp_add_Sp : G.Qp + G.Sp = G.Dp := hiPart_add_loPart _ _

theorem Qm_deg (a : ℤ × ℤ) (x : K) (hx : x ∈ G.deg a) : G.Qm x ∈ G.deg (a + shQm) :=
  (G.parts_mem G.D 1 G.D_good a hx).1
theorem Sm_deg (a : ℤ × ℤ) (x : K) (hx : x ∈ G.deg a) : G.Sm x ∈ G.deg (a + shSm) :=
  (G.parts_mem G.D 1 G.D_good a hx).2
theorem Qp_deg (a : ℤ × ℤ) (x : K) (hx : x ∈ G.deg a) : G.Qp x ∈ G.deg (a + shQp) :=
  (G.parts_mem G.Dp (-1) G.Dp_good a hx).1
theorem Sp_deg (a : ℤ × ℤ) (x : K) (hx : x ∈ G.deg a) : G.Sp x ∈ G.deg (a + shSp) :=
  (G.parts_mem G.Dp (-1) G.Dp_good a hx).2

/-- Induction over the spanning bigraded pieces. -/
theorem forall_of_deg (Φ : K → Prop) (h0 : Φ 0) (hadd : ∀ x x', Φ x → Φ x' → Φ (x + x'))
    (hdeg : ∀ a, ∀ x ∈ G.deg a, Φ x) (x : K) : Φ x := by
  have hx : x ∈ iSup G.deg := G.span ▸ Submodule.mem_top
  exact Submodule.iSup_induction G.deg (motive := Φ) hx hdeg h0 hadd

/-- Extend an identity between two sesquilinear-type expressions from homogeneous pairs. -/
theorem eq_of_deg (F H : K → K → ℂ)
    (hF0 : ∀ y, F 0 y = 0) (hH0 : ∀ y, H 0 y = 0) (hF0' : ∀ x, F x 0 = 0)
    (hH0' : ∀ x, H x 0 = 0)
    (hFl : ∀ x x' y, F (x + x') y = F x y + F x' y)
    (hHl : ∀ x x' y, H (x + x') y = H x y + H x' y)
    (hFr : ∀ x y y', F x (y + y') = F x y + F x y')
    (hHr : ∀ x y y', H x (y + y') = H x y + H x y')
    (hdeg : ∀ a b, ∀ x ∈ G.deg a, ∀ y ∈ G.deg b, F x y = H x y) (x y : K) : F x y = H x y := by
  revert y
  refine G.forall_of_deg (fun x => ∀ y, F x y = H x y) (fun y => by rw [hF0, hH0])
    (fun x x' hx hx' y => by beta_reduce at hx hx' ⊢; rw [hFl, hHl, hx, hx']) ?_ x
  intro a x hx
  refine G.forall_of_deg (fun y => F x y = H x y) (by beta_reduce; rw [hF0', hH0'])
    (fun y y' hy hy' => by beta_reduce at hy hy' ⊢; rw [hFr, hHr, hy, hy']) ?_
  intro b y hy
  exact hdeg a b x hx y hy

/-- `(Q⁻)† = c S⁺`, derived from the single bold relation by degree splitting. -/
theorem adj_Qm (x y : K) : G.P (G.Qm x) y = (G.c : ℂ) * G.P x (G.Sp y) := by
  refine G.eq_of_deg (fun x y => G.P (G.Qm x) y) (fun x y => (G.c : ℂ) * G.P x (G.Sp y))
    (fun y => by simp only [map_zero, G.P.zero_left])
    (fun y => by simp only [G.P.zero_left, mul_zero])
    (fun x => by simp only [G.P.zero_right])
    (fun x => by simp only [map_zero, G.P.zero_right, mul_zero])
    (fun x x' y => by simp only [map_add, G.P.add_left])
    (fun x x' y => by simp only [G.P.add_left, mul_add])
    (fun x y y' => by simp only [G.P.add_right])
    (fun x y y' => by simp only [map_add, G.P.add_right, mul_add]) ?_ x y
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ x hx y hy
  have hQm := G.Qm_deg _ x hx
  have hSm := G.Sm_deg _ x hx
  have hQp := G.Qp_deg _ y hy
  have hSp := G.Sp_deg _ y hy
  have hD : G.D x = G.Qm x + G.Sm x := by rw [← G.Qm_add_Sm]; rfl
  have hadj := G.adj x y
  change G.P (G.D x) y = (G.c : ℂ) * G.P x (G.Sp y - G.Qp y) at hadj
  rw [hD, G.P.add_left, G.P_sub_right] at hadj
  by_cases hb : b1 = a1 + 1 ∧ b2 = a2 + 1
  · have h1 : G.P (G.Sm x) y = 0 := G.orth _ _ (by
      simp only [shSm, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hSm _ hy
    have h2 : G.P x (G.Qp y) = 0 := G.orth _ _ (by
      simp only [shQp, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hx _ hQp
    rw [h1, h2, add_zero, sub_zero] at hadj
    exact hadj
  · have h1 : G.P (G.Qm x) y = 0 := G.orth _ _ (by
      simp only [shQm, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hQm _ hy
    have h2 : G.P x (G.Sp y) = 0 := G.orth _ _ (by
      simp only [shSp, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hx _ hSp
    change G.P (G.Qm x) y = (G.c : ℂ) * G.P x (G.Sp y)
    rw [h1, h2, mul_zero]

/-- `(S⁻)† = -c Q⁺`, derived from the single bold relation by degree splitting. -/
theorem adj_Sm (x y : K) : G.P (G.Sm x) y = -(G.c : ℂ) * G.P x (G.Qp y) := by
  refine G.eq_of_deg (fun x y => G.P (G.Sm x) y) (fun x y => -(G.c : ℂ) * G.P x (G.Qp y))
    (fun y => by simp only [map_zero, G.P.zero_left])
    (fun y => by simp only [G.P.zero_left, mul_zero])
    (fun x => by simp only [G.P.zero_right])
    (fun x => by simp only [map_zero, G.P.zero_right, mul_zero])
    (fun x x' y => by simp only [map_add, G.P.add_left])
    (fun x x' y => by simp only [G.P.add_left, mul_add])
    (fun x y y' => by simp only [G.P.add_right])
    (fun x y y' => by simp only [map_add, G.P.add_right, mul_add]) ?_ x y
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ x hx y hy
  have hQm := G.Qm_deg _ x hx
  have hSm := G.Sm_deg _ x hx
  have hQp := G.Qp_deg _ y hy
  have hSp := G.Sp_deg _ y hy
  have hD : G.D x = G.Qm x + G.Sm x := by rw [← G.Qm_add_Sm]; rfl
  have hadj := G.adj x y
  change G.P (G.D x) y = (G.c : ℂ) * G.P x (G.Sp y - G.Qp y) at hadj
  rw [hD, G.P.add_left, G.P_sub_right] at hadj
  by_cases hb : b1 = a1 - 1 ∧ b2 = a2 + 1
  · have h1 : G.P (G.Qm x) y = 0 := G.orth _ _ (by
      simp only [shQm, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hQm _ hy
    have h2 : G.P x (G.Sp y) = 0 := G.orth _ _ (by
      simp only [shSp, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hx _ hSp
    rw [h1, h2, zero_add, zero_sub] at hadj
    change G.P (G.Sm x) y = -(G.c : ℂ) * G.P x (G.Qp y)
    rw [hadj]; ring
  · have h1 : G.P (G.Sm x) y = 0 := G.orth _ _ (by
      simp only [shSm, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hSm _ hy
    have h2 : G.P x (G.Qp y) = 0 := G.orth _ _ (by
      simp only [shQp, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]; omega) _ hx _ hQp
    change G.P (G.Sm x) y = -(G.c : ℂ) * G.P x (G.Qp y)
    rw [h1, h2, mul_zero]

end GoodGeometry

namespace GoodComplex

variable (G : GoodComplex K)

/-- **The Kähler package of a good complex.** -/
def toKahler : KahlerComplex K where
  P := G.P
  pos := G.pos
  deg := G.deg
  span := G.span
  orth := G.orth
  Qm := G.Qm
  Sm := G.Sm
  Qp := G.Qp
  Sp := G.Sp
  Qm_deg := G.Qm_deg
  Sm_deg := G.Sm_deg
  Qp_deg := G.Qp_deg
  Sp_deg := G.Sp_deg
  c := G.c
  c_sq := G.c_sq
  adj_Qm := G.adj_Qm
  adj_Sm := G.adj_Sm
  sq_zero := by rw [G.Qm_add_Sm]; exact G.sq_zero
  anticomm := by rw [G.Qm_add_Sm, G.Qp_add_Sp]; exact G.anticomm

/-- The bold differential of the Kähler package is the given `𝐐⁻`. -/
theorem toKahler_D : G.toKahler.D = G.D := G.Qm_add_Sm

end GoodComplex

end

end VOA.ConcreteHodge
