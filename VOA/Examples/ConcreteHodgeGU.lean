/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteHodgeSplit

/-!
# The grading operator and the conjugation datum of a good complex

Fourth layer of the concrete Beem–Garner instantiation.

* `deg_iSupIndep`, `deg_isInternal`: a `P`-orthogonal spanning family of subspaces, for a positive
  `P`, is an internal direct sum. `degOperator` is its `2R` grading operator, and
  `degOperator_deg` its defining property, so the field `Rop` of `GoodComplex` is never extra data.
* `GoodComplex.guData` (**the `GUData` of Beem–Garner Theorem 4.1**): from an antilinear `ρ` that
  maps bidegree `(2R, g)` to `(2R, -g)`, intertwines the two bold differentials up to nonzero
  scalars (`ρ 𝐐⁻ = κ 𝐐⁺ ρ`, `ρ 𝐐⁺ = κ' 𝐐⁻ ρ`; Beem–Garner use `κ = i`), and squares to a
  nonzero scalar (`ρ² = s`), the fields `ρ_maps` and `ρ_onto` of `GUData` are *proved*.
  The relation `P = i^{2R} (ρ x, y)` (`P_eq`) is the remaining input, and it is an identity
  between two explicitly given forms.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open Module (finrank)

noncomputable section

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-! ### The grading operator -/

section DegOperator

variable (P : SesqForm K) (deg : ℤ × ℤ → Submodule ℂ K)

/-- Pairwise `P`-orthogonal subspaces, for positive `P`, are independent. -/
theorem deg_iSupIndep (hpos : IsPosOn P ⊤)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0) : iSupIndep deg := by
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero P hpos
  refine Submodule.iSup_induction (fun b => ⨆ (_ : b ≠ a), deg b)
    (motive := fun y => P x y = 0) hx' ?_ (P.zero_right x)
    (fun y y' h h' => by beta_reduce at h h' ⊢; rw [P.add_right, h, h', add_zero])
  intro b y hy
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, P.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact horth a b (Ne.symm hba) x hx y hy

theorem deg_isInternal (hpos : IsPosOn P ⊤)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0) (hspan : iSup deg = ⊤) :
    DirectSum.IsInternal deg :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (deg_iSupIndep P deg hpos horth)
    hspan

/-- The `2R` grading operator of a positive orthogonal bigrading. -/
def degOperator (hpos : IsPosOn P ⊤)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0) (hspan : iSup deg = ⊤) :
    K →ₗ[ℂ] K :=
  internalWeightOperator deg (deg_isInternal P deg hpos horth hspan) (fun a => (a.1 : ℂ))

theorem degOperator_deg (hpos : IsPosOn P ⊤)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0) (hspan : iSup deg = ⊤)
    (j g : ℤ) (x : K) (hx : x ∈ deg (j, g)) :
    degOperator P deg hpos horth hspan x = (j : ℂ) • x :=
  Module.End.mem_eigenspace_iff.mp
    (grading_le_eigenspace_internalWeightOperator deg _ (fun a => (a.1 : ℂ)) (j, g) hx)

end DegOperator

/-! ### The conjugation datum -/

namespace GoodComplex

variable (G : GoodComplex K)

/-- Two homogeneous vectors of distinct bidegrees with zero sum both vanish. -/
theorem eq_zero_of_add_eq_zero {a b : ℤ × ℤ} (hab : a ≠ b) {u v : K} (hu : u ∈ G.deg a)
    (hv : v ∈ G.deg b) (h : u + v = 0) : u = 0 := by
  apply eq_zero_of_sesq_self_eq_zero G.P G.pos
  have : u = -v := eq_neg_of_add_eq_zero_left h
  calc G.P u u = G.P u (-v) := by rw [← this]
    _ = -G.P u v := by rw [← neg_one_smul ℂ v, G.P.smul_right]; ring
    _ = 0 := by rw [G.orth a b hab u hu v hv, neg_zero]

/-- A homogeneous vector killed by `𝐐⁻` is killed by `Q⁻` and `S⁻` separately. -/
theorem Qm_Sm_eq_zero {a : ℤ × ℤ} {x : K} (hx : x ∈ G.deg a) (hD : G.D x = 0) :
    G.Qm x = 0 ∧ G.Sm x = 0 := by
  have hsum : G.Qm x + G.Sm x = 0 := by rw [← LinearMap.add_apply, G.Qm_add_Sm, hD]
  have hne : a + shQm ≠ a + shSm := by
    intro h; have := congrArg Prod.fst h; simp at this
  have h1 := G.eq_zero_of_add_eq_zero hne (G.Qm_deg a x hx) (G.Sm_deg a x hx) hsum
  refine ⟨h1, ?_⟩
  rw [h1, zero_add] at hsum; exact hsum

/-- A homogeneous vector killed by `𝐐⁺` is killed by `Q⁺` and `S⁺` separately. -/
theorem Qp_Sp_eq_zero {a : ℤ × ℤ} {x : K} (hx : x ∈ G.deg a) (hD : G.Dp x = 0) :
    G.Qp x = 0 ∧ G.Sp x = 0 := by
  have hsum : G.Qp x + G.Sp x = 0 := by rw [← LinearMap.add_apply, G.Qp_add_Sp, hD]
  have hne : a + shQp ≠ a + shSp := by
    intro h; have := congrArg Prod.fst h; simp at this
  have h1 := G.eq_zero_of_add_eq_zero hne (G.Qp_deg a x hx) (G.Sp_deg a x hx) hsum
  refine ⟨h1, ?_⟩
  rw [h1, zero_add] at hsum; exact hsum

/-- Harmonic vectors (for the Kähler package) are killed by both bold differentials. -/
theorem D_Dp_of_harm {x : K} (hx : x ∈ G.toKahler.harm) : G.D x = 0 ∧ G.Dp x = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := (G.toKahler.mem_harm_iff x).mp hx
  change G.Qm x = 0 at h1
  change G.Sm x = 0 at h2
  change G.Qp x = 0 at h3
  change G.Sp x = 0 at h4
  refine ⟨?_, ?_⟩
  · rw [← G.Qm_add_Sm, LinearMap.add_apply, h1, h2, add_zero]
  · rw [← G.Qp_add_Sp, LinearMap.add_apply, h3, h4, add_zero]

/-- A homogeneous vector killed by both bold differentials is harmonic. -/
theorem mem_harm_of_D_Dp {a : ℤ × ℤ} {x : K} (hx : x ∈ G.deg a) (hD : G.D x = 0)
    (hDp : G.Dp x = 0) : x ∈ G.toKahler.harm := by
  obtain ⟨h1, h2⟩ := G.Qm_Sm_eq_zero hx hD
  obtain ⟨h3, h4⟩ := G.Qp_Sp_eq_zero hx hDp
  exact (G.toKahler.mem_harm_iff x).mpr ⟨h1, h2, h3, h4⟩

variable {G}

/-- The conjugation hypotheses of Beem–Garner Theorem 4.1, at one conformal weight. -/
structure ConjData (G : GoodComplex K) where
  /-- The invariant bilinear form at this weight. -/
  B : LinearMap.BilinForm ℂ K
  /-- The antilinear conjugation. -/
  ρ : K →ₗ⋆[ℂ] K
  /-- The sesquilinear form `(ρ x, y)`. -/
  h : SesqForm K
  h_eq : ∀ x y, h x y = B (ρ x) y
  /-- `⟨x|y⟩ = i^{2R} (ρ x, y)`. -/
  P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * h x y
  /-- `ρ` preserves `R` and reverses the ghost number. -/
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g)
  κ : ℂ
  κ' : ℂ
  hκ : κ ≠ 0
  hκ' : κ' ≠ 0
  /-- `ρ 𝐐⁻ = κ 𝐐⁺ ρ`. -/
  ρ_D : ∀ x, ρ (G.D x) = κ • G.Dp (ρ x)
  /-- `ρ 𝐐⁺ = κ' 𝐐⁻ ρ`. -/
  ρ_Dp : ∀ x, ρ (G.Dp x) = κ' • G.D (ρ x)
  /-- `ρ² = s`, `s ≠ 0`. -/
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x

variable (G)

theorem ρ_maps (R : ConjData G) (j : ℤ) (x : K) (hx : x ∈ G.toKahler.harmDeg (j, 0)) :
    R.ρ x ∈ G.toKahler.harmDeg (j, 0) := by
  obtain ⟨hxh, hxd⟩ := hx
  change x ∈ G.deg (j, 0) at hxd
  obtain ⟨hD, hDp⟩ := G.D_Dp_of_harm hxh
  have hρd : R.ρ x ∈ G.deg (j, 0) := by
    have := R.ρ_deg j 0 x hxd; rwa [neg_zero] at this
  have h1 : G.D (R.ρ x) = 0 := by
    have := R.ρ_Dp x
    rw [hDp, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left R.hκ'
  have h2 : G.Dp (R.ρ x) = 0 := by
    have := R.ρ_D x
    rw [hD, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left R.hκ
  exact ⟨G.mem_harm_of_D_Dp hρd h1 h2, hρd⟩

theorem ρ_onto (R : ConjData G) (j : ℤ) (y : K) (hy : y ∈ G.toKahler.harmDeg (j, 0)) :
    ∃ x ∈ G.toKahler.harmDeg (j, 0), R.ρ x = y := by
  refine ⟨(starRingEnd ℂ) R.s⁻¹ • R.ρ y,
    Submodule.smul_mem _ _ (G.ρ_maps R j y hy), ?_⟩
  rw [LinearMap.map_smulₛₗ, R.ρ_sq, smul_smul]
  simp only [starRingEnd_apply, star_star]
  rw [inv_mul_cancel₀ R.hs, one_smul]

/-- **The `GUData` of the Kähler package**, from the conjugation hypotheses. -/
def guData (R : ConjData G) : GUData G.toKahler where
  B := R.B
  ρ := R.ρ
  h := R.h
  h_eq := R.h_eq
  P_eq := R.P_eq
  ρ_maps := G.ρ_maps R
  ρ_onto := G.ρ_onto R

/-- **Beem–Garner Theorem 4.1 for a good complex**: on the orthogonal layers of the harmonic
flag, the sign-corrected form `(-1)^p (ρ x, y)` is positive. -/
theorem layer_signed_pos (R : ConjData G) {L : ℤ} (p : ℕ) (hL : L ≤ 2 * (p : ℤ)) :
    IsPosOn (signedForm R.h p) ((G.guData R).layer L (2 * (p : ℤ))) :=
  (G.guData R).layer_signed_pos p hL

/-- **The harmonic bound for a good complex**: classes with a ghost-number-`g` representative
supported on `2R ∈ S` number at most `Σ_{j ∈ S} dim H(Q⁻)_{(j,g)}`. -/
theorem finrank_cohomFilt_row_le_lead [FiniteDimensional ℂ K] (S : Finset ℤ) (g : ℤ) :
    finrank ℂ (G.toKahler.cohomFilt (KahlerComplex.rowSet S g)) ≤
      ∑ j ∈ S, finrank ℂ (G.toKahler.leadCohom (j, g)) :=
  G.toKahler.finrank_cohomFilt_row_le_lead S g

end GoodComplex

end

end VOA.ConcreteHodge
