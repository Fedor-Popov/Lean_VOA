/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteHodgeGU
import VOA.Examples.ConcreteHodgeTensor

/-!
# The second differential is derived, not data (Beem–Garner Lemma 3.16, adjoint half)

`GoodGeometry` (in `ConcreteHodgeSplit`) takes the second bold differential `𝐐⁺` as a free
field `Dp`, constrained by goodness, the single adjoint relation `(𝐐⁻)† = c (S⁺ - Q⁺)` and the
anticommutation `𝐐⁻𝐐⁺ + 𝐐⁺𝐐⁻ = 0`. For a *positive* form this is redundant data: the adjoint
relation determines `𝐐⁺` from `𝐐⁻`.

Here, in finite dimension and for a positive form `P` with a `P`-orthogonal spanning bigrading
by `(2R, gh)`:

* `exists_sesqAdjoint`, `sesqAdjoint`: every operator has a `P`-adjoint
  (`P (T x) y = P x (T† y)`), built from an orthonormal basis; `sesq_ext_right`: it is unique.
* `mem_sup_of_orth`: a vector `P`-orthogonal to all pieces except two lies in their sum.
* `GoodHalf` — the **minimal input**: form, bigrading, `𝐐⁻ = D`, goodness of `D` (no
  `ℜ`-preserving component) and `D² = 0`. No second differential, no adjoint relation.
* `GoodHalf.derivedDp`: `𝐐⁺ := lo(D†) - hi(D†)`, i.e. `Q⁺ = -hi(D†)`, `S⁺ = lo(D†)`.
  `derivedDp_good` (goodness of `𝐐⁺`, *proved* from goodness of `D` by adjunction) and
  `adj_derived` (the Beem–Garner relation `(𝐐⁻)† = S⁺ - Q⁺`, *proved*, with `c = 1`).
* `GoodHalf.KahlerAnticomm` — the only remaining relation, `𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0` for the derived
  `𝐐⁺`. `GoodHalf.toGoodGeometry`: a `GoodGeometry` from `GoodHalf` + positivity +
  `KahlerAnticomm`.
* `GoodGeometry.Dp_eq_smul_derived` and `GoodGeometry.kahlerAnticomm`: for **any**
  `GoodGeometry` with a positive form, its `Dp` is `c •` the derived one, so it satisfies
  `KahlerAnticomm`. Hence the reduced input is *equivalent* to the old one
  (`exists_goodGeometry_iff`): nothing is assumed that the old interface did not assume.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open Module (finrank)

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-! ### Sums in sesquilinear forms -/

theorem sesq_sum_left {ι : Type*} (P : SesqForm K) (s : Finset ι) (f : ι → K) (y : K) :
    P (∑ i ∈ s, f i) y = ∑ i ∈ s, P (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P.zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, P.add_left, ih]

theorem sesq_sum_right {ι : Type*} (P : SesqForm K) (s : Finset ι) (x : K) (f : ι → K) :
    P x (∑ i ∈ s, f i) = ∑ i ∈ s, P x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P.zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, P.add_right, ih]

theorem sesq_sub_left (P : SesqForm K) (x x' y : K) : P (x - x') y = P x y - P x' y := by
  rw [sub_eq_add_neg, P.add_left, ← neg_one_smul ℂ x', P.smul_left]; simp; ring

theorem sesq_sub_right' (P : SesqForm K) (x y y' : K) : P x (y - y') = P x y - P x y' := by
  rw [sub_eq_add_neg, P.add_right, ← neg_one_smul ℂ y', P.smul_right]; ring

/-! ### Adjoints for a positive form -/

section Adjoint

/-- The linear functional `y ↦ P v y`. -/
def sesqRight (P : SesqForm K) (v : K) : K →ₗ[ℂ] ℂ where
  toFun y := P v y
  map_add' := P.add_right v
  map_smul' c y := by rw [P.smul_right]; rfl

@[simp] theorem sesqRight_apply (P : SesqForm K) (v y : K) : sesqRight P v y = P v y := rfl

/-- Uniqueness of the right argument for a positive form. -/
theorem sesq_ext_right (P : SesqForm K) (hP : IsPosOn P ⊤) {u v : K}
    (h : ∀ x, P x u = P x v) : u = v := by
  have h0 : P (u - v) (u - v) = 0 := by
    rw [sesq_sub_right', h (u - v), sub_self]
  exact sub_eq_zero.mp (eq_zero_of_sesq_self_eq_zero P hP h0)

variable [FiniteDimensional ℂ K]

/-- **Every operator has a `P`-adjoint** for a positive form, in finite dimension. -/
theorem exists_sesqAdjoint (P : SesqForm K) (hP : IsPosOn P ⊤) (T : K →ₗ[ℂ] K) :
    ∃ T' : K →ₗ[ℂ] K, ∀ x y, P (T x) y = P x (T' y) := by
  obtain ⟨n, b, hb⟩ := exists_orthonormal_basis P hP
  refine ⟨∑ i, (sesqRight P (T (b i))).smulRight (b i), fun x y => ?_⟩
  have hPb : ∀ i, P x (b i) = (starRingEnd ℂ) (b.repr x i) := by
    intro i
    conv_lhs => rw [← b.sum_repr x]
    rw [sesq_sum_left]
    simp only [P.smul_left, hb]
    simp
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, sesq_sum_left, LinearMap.sum_apply, sesq_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, P.smul_left, LinearMap.smulRight_apply, P.smul_right, hPb, sesqRight_apply,
    mul_comm]

/-- The `P`-adjoint of `T`. -/
def sesqAdjoint (P : SesqForm K) (hP : IsPosOn P ⊤) (T : K →ₗ[ℂ] K) : K →ₗ[ℂ] K :=
  Classical.choose (exists_sesqAdjoint P hP T)

theorem sesqAdjoint_spec (P : SesqForm K) (hP : IsPosOn P ⊤) (T : K →ₗ[ℂ] K) (x y : K) :
    P (T x) y = P x (sesqAdjoint P hP T y) :=
  Classical.choose_spec (exists_sesqAdjoint P hP T) x y

end Adjoint

/-! ### Orthogonality detects membership -/

section Orth

variable (P : SesqForm K) (deg : ℤ × ℤ → Submodule ℂ K)

theorem sesq_iSup_left (y : K) (h : ∀ c, ∀ x ∈ deg c, P x y = 0) :
    ∀ x ∈ iSup deg, P x y = 0 := by
  intro x hx
  exact Submodule.iSup_induction deg (motive := fun x => P x y = 0) hx h (P.zero_left y)
    (fun x x' h h' => by beta_reduce at h h' ⊢; rw [P.add_left, h, h', add_zero])

/-- A vector orthogonal to every piece except `deg a`, `deg b` lies in `deg a ⊔ deg b`. -/
theorem mem_sup_of_orth (hpos : IsPosOn P ⊤)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0) (hspan : iSup deg = ⊤)
    (a b : ℤ × ℤ) (w : K) (hw : ∀ c, c ≠ a → c ≠ b → ∀ x ∈ deg c, P x w = 0) :
    w ∈ deg a ⊔ deg b := by
  classical
  let S' : ℤ × ℤ → Submodule ℂ K := fun c => if c = a ∨ c = b then ⊥ else deg c
  have hcover : (⊤ : Submodule ℂ K) ≤ (deg a ⊔ deg b) ⊔ iSup S' := by
    rw [← hspan]
    refine iSup_le fun c => ?_
    by_cases hc : c = a ∨ c = b
    · rcases hc with rfl | rfl
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
    · refine le_sup_of_le_right (le_trans ?_ (le_iSup S' c))
      simp only [S', if_neg hc, le_refl]
  obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.mp (hcover (Submodule.mem_top (x := w)))
  -- `s'` is orthogonal to `w` and to `s`.
  have hS'gen : ∀ c, ∀ x ∈ S' c, (∀ z ∈ deg a ⊔ deg b, P x z = 0) ∧ P x w = 0 := by
    intro c x hx
    by_cases hc : c = a ∨ c = b
    · simp only [S', if_pos hc, Submodule.mem_bot] at hx
      subst hx
      exact ⟨fun z _ => P.zero_left z, P.zero_left w⟩
    · simp only [S', if_neg hc] at hx
      push Not at hc
      refine ⟨fun z hz => ?_, hw c hc.1 hc.2 x hx⟩
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz
      rw [P.add_right, horth c a hc.1 x hx z1 hz1, horth c b hc.2 x hx z2 hz2, add_zero]
  have hw' : P s' w = 0 :=
    sesq_iSup_left P S' w (fun c x hx => (hS'gen c x hx).2) s' hs'
  have hs's : P s' s = 0 :=
    sesq_iSup_left P S' s (fun c x hx => (hS'gen c x hx).1 s hs) s' hs'
  have h0 : P s' s' = 0 := by
    have : s' = w - s := by rw [← hss]; abel
    rw [show P s' s' = P s' (w - s) by rw [← this], sesq_sub_right', hw', hs's, sub_zero]
  have hz : s' = 0 := eq_zero_of_sesq_self_eq_zero P hpos h0
  rw [← hss, hz, add_zero]
  exact hs

end Orth

/-! ### The minimal input and the derived second differential -/

/-- **The minimal Lemma 3.16 input**: a form, an orthogonal spanning `(2R, gh)` bigrading, and a
good square-zero `𝐐⁻`. There is no second differential and no adjoint relation. -/
structure GoodHalf (K : Type u) [AddCommGroup K] [Module ℂ K] where
  P : SesqForm K
  deg : ℤ × ℤ → Submodule ℂ K
  span : iSup deg = ⊤
  orth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0
  /-- `𝐐⁻`. -/
  D : K →ₗ[ℂ] K
  /-- **Goodness**: no `ℜ`-preserving component; ghost number raised by one. -/
  D_good : ∀ a, ∀ x ∈ deg a, D x ∈ deg (a + shQm) ⊔ deg (a + shSm)
  sq_zero : D.comp D = 0

namespace GoodHalf

variable [FiniteDimensional ℂ K] (H : GoodHalf K) (hpos : IsPosOn H.P ⊤)

/-- The `2R` grading operator. -/
def Rop : K →ₗ[ℂ] K := degOperator H.P H.deg hpos H.orth H.span

omit [FiniteDimensional ℂ K] in
theorem Rop_deg (j g : ℤ) (x : K) (hx : x ∈ H.deg (j, g)) : H.Rop hpos x = (j : ℂ) • x :=
  degOperator_deg H.P H.deg hpos H.orth H.span j g x hx

/-- `D†`. -/
def Dadj : K →ₗ[ℂ] K := sesqAdjoint H.P hpos H.D

theorem Dadj_spec (x y : K) : H.P (H.D x) y = H.P x (H.Dadj hpos y) :=
  sesqAdjoint_spec H.P hpos H.D x y

/-- `D†` lowers the ghost number by one and shifts `2R` by `±1`. -/
theorem Dadj_good (a : ℤ × ℤ) (y : K) (hy : y ∈ H.deg a) :
    H.Dadj hpos y ∈ H.deg (a + shQp) ⊔ H.deg (a + shSp) := by
  apply mem_sup_of_orth H.P H.deg hpos H.orth H.span
  intro c hc1 hc2 x hx
  rw [← H.Dadj_spec hpos]
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (H.D_good c x hx)
  rw [← huv, H.P.add_left]
  have h1 : c + shQm ≠ a := by
    intro h; apply hc2; rw [← h]; bideg
  have h2 : c + shSm ≠ a := by
    intro h; apply hc1; rw [← h]; bideg
  rw [H.orth _ _ h1 u hu y hy, H.orth _ _ h2 v hv y hy, add_zero]

omit [FiniteDimensional ℂ K] in
/-- Splitting a `±1`-shift operator at a homogeneous vector. -/
theorem split_apply (T : K →ₗ[ℂ] K) (e : ℤ) (j g : ℤ) {y u v : K} (hy : y ∈ H.deg (j, g))
    (hu : u ∈ H.deg ((j, g) + (1, e))) (hv : v ∈ H.deg ((j, g) + (-1, e)))
    (hT : T y = u + v) :
    hiPart (H.Rop hpos) T y = u ∧ loPart (H.Rop hpos) T y = v := by
  have hu' : H.Rop hpos u = ((j + 1 : ℤ) : ℂ) • u := H.Rop_deg hpos (j + 1) (g + e) u hu
  have hv' : H.Rop hpos v = ((j - 1 : ℤ) : ℂ) • v := by
    have := H.Rop_deg hpos (j + -1) (g + e) v hv
    rw [this]; congr 2
  exact hiPart_loPart_apply (H.Rop hpos) T j (H.Rop_deg hpos j g y hy) hu' hv' hT

/-- **The derived second differential** `𝐐⁺ := lo(D†) - hi(D†)`. -/
def derivedDp : K →ₗ[ℂ] K :=
  loPart (H.Rop hpos) (H.Dadj hpos) - hiPart (H.Rop hpos) (H.Dadj hpos)

/-- Componentwise description of `D†` and `𝐐⁺` at a homogeneous vector. -/
theorem derived_components (j g : ℤ) (y : K) (hy : y ∈ H.deg (j, g)) :
    ∃ u ∈ H.deg ((j, g) + shQp), ∃ v ∈ H.deg ((j, g) + shSp),
      H.Dadj hpos y = u + v ∧ H.derivedDp hpos y = v - u := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (H.Dadj_good hpos (j, g) y hy)
  obtain ⟨h1, h2⟩ := H.split_apply hpos (H.Dadj hpos) (-1) j g hy hu hv huv.symm
  refine ⟨u, hu, v, hv, huv.symm, ?_⟩
  simp only [derivedDp, LinearMap.sub_apply, h1, h2]

theorem derivedDp_good (a : ℤ × ℤ) (y : K) (hy : y ∈ H.deg a) :
    H.derivedDp hpos y ∈ H.deg (a + shQp) ⊔ H.deg (a + shSp) := by
  obtain ⟨j, g⟩ := a
  obtain ⟨u, hu, v, hv, -, hD⟩ := H.derived_components hpos j g y hy
  rw [hD, show v - u = -u + v by abel]
  exact Submodule.add_mem_sup (Submodule.neg_mem _ hu) hv

omit [FiniteDimensional ℂ K] in
/-- Induction over the spanning pieces. -/
theorem forall_of_deg (Φ : K → Prop) (h0 : Φ 0) (hadd : ∀ x x', Φ x → Φ x' → Φ (x + x'))
    (hdeg : ∀ a, ∀ x ∈ H.deg a, Φ x) (x : K) : Φ x := by
  have hx : x ∈ iSup H.deg := H.span ▸ Submodule.mem_top
  exact Submodule.iSup_induction H.deg (motive := Φ) hx hdeg h0 hadd

omit [FiniteDimensional ℂ K] in
/-- Two linear maps agreeing on every piece are equal. -/
theorem linearMap_ext_deg {T T' : K →ₗ[ℂ] K} (h : ∀ a, ∀ x ∈ H.deg a, T x = T' x) : T = T' := by
  ext x
  exact H.forall_of_deg (fun x => T x = T' x) (by simp)
    (fun x x' hx hx' => by beta_reduce at hx hx' ⊢; rw [map_add, map_add, hx, hx']) h x

/-- `lo(𝐐⁺) - hi(𝐐⁺) = D†`. -/
theorem lo_sub_hi_derived :
    loPart (H.Rop hpos) (H.derivedDp hpos) - hiPart (H.Rop hpos) (H.derivedDp hpos) =
      H.Dadj hpos := by
  apply H.linearMap_ext_deg
  rintro ⟨j, g⟩ y hy
  obtain ⟨u, hu, v, hv, hA, hD⟩ := H.derived_components hpos j g y hy
  have hD' : H.derivedDp hpos y = -u + v := by rw [hD]; abel
  obtain ⟨h1, h2⟩ := H.split_apply hpos (H.derivedDp hpos) (-1) j g hy
    (Submodule.neg_mem _ hu) hv hD'
  rw [LinearMap.sub_apply, h1, h2, hA]
  abel

/-- **Beem–Garner Eq. (3.5) for the derived `𝐐⁺`**: `(𝐐⁻)† = S⁺ - Q⁺` (sign `c = 1`). -/
theorem adj_derived (x y : K) :
    H.P (H.D x) y = ((1 : ℝ) : ℂ) * H.P x (loPart (H.Rop hpos) (H.derivedDp hpos) y -
      hiPart (H.Rop hpos) (H.derivedDp hpos) y) := by
  rw [Complex.ofReal_one, one_mul, ← LinearMap.sub_apply, H.lo_sub_hi_derived hpos]
  exact H.Dadj_spec hpos x y

/-- **The only remaining Kähler relation**: `𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0` for the derived `𝐐⁺`. -/
def KahlerAnticomm : Prop :=
  H.D.comp (H.derivedDp hpos) + (H.derivedDp hpos).comp H.D = 0

/-- **A good geometry from the minimal input**, positivity and the Kähler relation. -/
def toGoodGeometry (hK : H.KahlerAnticomm hpos) : GoodGeometry K where
  P := H.P
  deg := H.deg
  span := H.span
  orth := H.orth
  Rop := H.Rop hpos
  Rop_deg := H.Rop_deg hpos
  D := H.D
  Dp := H.derivedDp hpos
  D_good := H.D_good
  Dp_good := H.derivedDp_good hpos
  c := 1
  c_sq := by norm_num
  adj := H.adj_derived hpos
  sq_zero := H.sq_zero
  anticomm := hK

@[simp] theorem toGoodGeometry_P (hK : H.KahlerAnticomm hpos) :
    (H.toGoodGeometry hpos hK).P = H.P := rfl
@[simp] theorem toGoodGeometry_D (hK : H.KahlerAnticomm hpos) :
    (H.toGoodGeometry hpos hK).D = H.D := rfl
@[simp] theorem toGoodGeometry_deg (hK : H.KahlerAnticomm hpos) :
    (H.toGoodGeometry hpos hK).deg = H.deg := rfl

end GoodHalf

/-! ### The reduction is exact -/

namespace GoodGeometry

variable [FiniteDimensional ℂ K] (G : GoodGeometry K)

/-- The minimal input underlying a good geometry. -/
def toHalf : GoodHalf K where
  P := G.P
  deg := G.deg
  span := G.span
  orth := G.orth
  D := G.D
  D_good := G.D_good
  sq_zero := G.sq_zero

variable (hpos : IsPosOn G.P ⊤)

omit [FiniteDimensional ℂ K] in
theorem Rop_eq : G.Rop = G.toHalf.Rop hpos := by
  apply G.toHalf.linearMap_ext_deg
  rintro ⟨j, g⟩ x hx
  rw [G.Rop_deg j g x hx, G.toHalf.Rop_deg hpos j g x hx]

/-- For a positive form, the `Dp` of any good geometry is `c •` the derived one. -/
theorem Dp_eq_smul_derived : G.Dp = (G.c : ℂ) • G.toHalf.derivedDp hpos := by
  have hR := G.Rop_eq hpos
  -- `D† = c (lo Dp - hi Dp)`.
  have hadj : G.toHalf.Dadj hpos =
      (G.c : ℂ) • (loPart G.Rop G.Dp - hiPart G.Rop G.Dp) := by
    ext y
    apply sesq_ext_right G.P hpos
    intro x
    change G.P x (G.toHalf.Dadj hpos y) = G.P x ((G.c : ℂ) • (loPart G.Rop G.Dp y -
      hiPart G.Rop G.Dp y))
    have hs := G.toHalf.Dadj_spec hpos x y
    change G.P (G.D x) y = G.P x _ at hs
    rw [← hs, G.P.smul_right]
    exact G.adj x y
  apply G.toHalf.linearMap_ext_deg
  rintro ⟨j, g⟩ y hy
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (G.Dp_good (j, g) y hy)
  obtain ⟨h1, h2⟩ := G.toHalf.split_apply hpos G.Dp (-1) j g hy hu hv huv.symm
  have hAy : G.toHalf.Dadj hpos y = (G.c : ℂ) • (v - u) := by
    rw [hadj, LinearMap.smul_apply, LinearMap.sub_apply, hR, h1, h2]
  -- split `D† y = (-c u) + (c v)`
  have hAy' : G.toHalf.Dadj hpos y = (-(G.c : ℂ)) • u + (G.c : ℂ) • v := by
    rw [hAy]; module
  obtain ⟨k1, k2⟩ := G.toHalf.split_apply hpos (G.toHalf.Dadj hpos) (-1) j g hy
    (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv) hAy'
  change G.Dp y = (G.c : ℂ) • (loPart _ (G.toHalf.Dadj hpos) y - hiPart _ (G.toHalf.Dadj hpos) y)
  rw [k1, k2, ← huv]
  have hc : (G.c : ℂ) * (G.c : ℂ) = 1 := by exact_mod_cast G.c_sq
  rw [smul_sub, smul_smul, smul_smul, mul_neg, hc]
  module

/-- **Every good geometry with a positive form satisfies the reduced Kähler relation.** -/
theorem kahlerAnticomm : G.toHalf.KahlerAnticomm hpos := by
  have hc : (G.c : ℂ) * (G.c : ℂ) = 1 := by exact_mod_cast G.c_sq
  have hDp : G.toHalf.derivedDp hpos = (G.c : ℂ) • G.Dp := by
    rw [G.Dp_eq_smul_derived hpos, smul_smul, hc, one_smul]
  change G.D.comp (G.toHalf.derivedDp hpos) + (G.toHalf.derivedDp hpos).comp G.D = 0
  rw [hDp, LinearMap.comp_smul, LinearMap.smul_comp, ← smul_add, G.anticomm, smul_zero]

end GoodGeometry

/-- **Exactness of the reduction**: for the minimal input with a positive form, a
`GoodGeometry` extending it exists iff the reduced Kähler relation holds. -/
theorem GoodHalf.exists_goodGeometry_iff [FiniteDimensional ℂ K] (H : GoodHalf K)
    (hpos : IsPosOn H.P ⊤) :
    (∃ G : GoodGeometry K, G.toHalf = H) ↔ H.KahlerAnticomm hpos := by
  constructor
  · rintro ⟨G, rfl⟩
    exact G.kahlerAnticomm hpos
  · intro hK
    exact ⟨H.toGoodGeometry hpos hK, rfl⟩

end

end VOA.ConcreteHodge
