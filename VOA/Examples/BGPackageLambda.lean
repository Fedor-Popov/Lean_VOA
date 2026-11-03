/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageGlobal

/-!
# The `Sp(2)` raising operator `Λ` of Beem–Garner, constructed

Beem–Garner's `Λ` rotates `η⁻ = ∂c` into `η⁺ = b`. On the actual three-pair ghost space it is

  `Λ_N = Σ_{m = 1}^{N} (1/m) Σ_{a, b} K^{ab} b^a_{(-m)} b^b_{(m)}`,

with `K^{ab}` the **inverse** Killing form in the Chevalley basis (`casimir`: `K^{ef} = K^{fe} = 1`,
`K^{hh} = 1/2`, i.e. the Casimir tensor `e ⊗ f + f ⊗ e + ½ h ⊗ h`). On weight-`N` states the
terms with `m > N` vanish, so `Λ_N` is Beem–Garner's operator there. The BRST-space operator is
`lamBRST n = id ⊗ Λ_{n.toNat}`.

Proved here (all outright):
* `casimir_invariant` — the `sl₂`-invariance of the Casimir tensor (and the colour-uniform
  Killing form is **not** invariant: `killing_not_invariant`).
* `casimir_comm` (generic, any `ℂ`-algebra): a Casimir contraction of two adjoint families
  commutes with any operator acting on both families by the adjoint action.
* `lamG_comm_antiMode_zero`, `lamG_comm_ghostCurrent` — `Λ` commutes with the antighost zero
  modes and with the ghost current zero modes (from the actual CAR and the actual ghost OPE).
* `lamBRST_mem_relativeWeight` — `Λ` preserves every relative weight space.
* `lamBRST_shift` — `Λ` shifts the interpreted `(2R, gh)` grading by `(0, -2)` for every
  standard ghost grading.
* the package with `Λ` fixed to `lamBRST` is `BGReducedData` (`BGPackageReduced`).
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### The Casimir tensor -/

/-- The inverse Killing form in the Chevalley basis `(e, f, h) = (0, 1, 2)`. -/
def casimir (a b : Fin 3) : ℂ :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else if a = 2 ∧ b = 2 then 1 / 2 else 0

theorem casimir_symm (a b : Fin 3) : casimir a b = casimir b a := by
  fin_cases a <;> fin_cases b <;> rfl

/-- **`sl₂`-invariance of the Casimir tensor**: `Σ_y K^{py} f_{ayq} + Σ_x K^{xq} f_{axp} = 0`. -/
theorem casimir_invariant (a p q : Fin 3) :
    ∑ y, casimir p y * fabc a y q + ∑ x, casimir x q * fabc a x p = 0 := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp [casimir, fabc]

/-- The colour-uniform Killing form `κ` is **not** the invariant contraction of the `b`'s. -/
theorem killing_not_invariant :
    ∑ y, kappa 0 y * fabc 0 y 2 + ∑ x, kappa x 2 * fabc 0 x 0 ≠ 0 := by
  norm_num [kappa, fabc, Fin.sum_univ_three]

/-! ### Generic algebra -/

section Generic

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The Casimir contraction of two families. -/
def casContract (X Y : Fin 3 → A) : A := ∑ p, ∑ q, casimir p q • (X p * Y q)

/-- **A Casimir contraction of two adjoint families commutes with the adjoint generator.** -/
theorem casimir_comm (J : A) (X Y : Fin 3 → A) (a : Fin 3)
    (hX : ∀ c, J * X c = X c * J + ∑ i, fabc a c i • X i)
    (hY : ∀ c, J * Y c = Y c * J + ∑ i, fabc a c i • Y i) :
    J * casContract X Y = casContract X Y * J := by
  have key : ∀ p q, J * (X p * Y q) = X p * Y q * J +
      ((∑ i, fabc a p i • X i) * Y q + X p * ∑ i, fabc a q i • Y i) := by
    intro p q
    rw [← mul_assoc, hX, add_mul, mul_assoc (X p) J, hY, mul_add, ← mul_assoc]
    abel
  have hsum : ∑ p, ∑ q, casimir p q •
      ((∑ i, fabc a p i • X i) * Y q + X p * ∑ i, fabc a q i • Y i) = 0 := by
    have h1 : ∀ p q, casimir p q •
        ((∑ i, fabc a p i • X i) * Y q + X p * ∑ i, fabc a q i • Y i) =
        ∑ i, (casimir p q * fabc a p i) • (X i * Y q) +
          ∑ i, (casimir p q * fabc a q i) • (X p * Y i) := by
      intro p q
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_add,
        Finset.smul_sum, smul_smul]
    simp only [h1, Finset.sum_add_distrib]
    have h2 : ∑ p, ∑ q, ∑ i, (casimir p q * fabc a p i) • (X i * Y q) =
        ∑ i, ∑ q, (∑ p, casimir p q * fabc a p i) • (X i * Y q) := by
      simp only [Fin.sum_univ_three, add_smul]; abel
    have h3 : ∑ p, ∑ q, ∑ i, (casimir p q * fabc a q i) • (X p * Y i) =
        ∑ p, ∑ i, (∑ q, casimir p q * fabc a q i) • (X p * Y i) := by
      simp only [Fin.sum_univ_three, add_smul]; abel
    rw [h2, h3, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [← add_smul]
    have e : ∑ x, casimir x q * fabc a x p + ∑ y, casimir p y * fabc a y q = 0 := by
      rw [add_comm]; exact casimir_invariant a p q
    rw [e, zero_smul]
  calc J * casContract X Y = ∑ p, ∑ q, casimir p q • (J * (X p * Y q)) := by
        simp only [casContract, Finset.mul_sum, mul_smul_comm]
    _ = ∑ p, ∑ q, casimir p q • (X p * Y q * J +
          ((∑ i, fabc a p i • X i) * Y q + X p * ∑ i, fabc a q i • Y i)) := by
        simp only [key]
    _ = casContract X Y * J + ∑ p, ∑ q, casimir p q •
          ((∑ i, fabc a p i • X i) * Y q + X p * ∑ i, fabc a q i • Y i) := by
        simp only [casContract, smul_add, Finset.sum_add_distrib, Finset.sum_mul,
          smul_mul_assoc]
    _ = casContract X Y * J := by rw [hsum, add_zero]

omit [Algebra ℂ A] in
/-- A product of two elements anticommuting with `Z` commutes with `Z`. -/
theorem comm_of_anticomm {Z X Y : A} (hX : Z * X + X * Z = 0) (hY : Z * Y + Y * Z = 0) :
    Z * (X * Y) = X * Y * Z := by
  have hX' : Z * X = -(X * Z) := eq_neg_of_add_eq_zero_left hX
  have hY' : Z * Y = -(Y * Z) := eq_neg_of_add_eq_zero_left hY
  rw [← mul_assoc, hX', neg_mul, mul_assoc, hY', mul_neg, neg_neg, mul_assoc]

theorem casContract_comm_of_anticomm (Z : A) (X Y : Fin 3 → A)
    (hX : ∀ c, Z * X c + X c * Z = 0) (hY : ∀ c, Z * Y c + Y c * Z = 0) :
    Z * casContract X Y = casContract X Y * Z := by
  unfold casContract
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    comm_of_anticomm (hX _) (hY _)]

end Generic

/-! ### The ghost operator -/

/-- The antighost mode `b^a_{(m)}` on the three pairs. -/
abbrev antiMode (a : Fin 3) (m : ℤ) : Module.End ℂ Sl2GhostSpace := gMode a 0 m

/-- One level of `Λ`: `Σ K^{ab} b^a_{(-m)} b^b_{(m)}`. -/
def lamTerm (m : ℤ) : Module.End ℂ Sl2GhostSpace :=
  casContract (fun a => antiMode a (-m)) (fun b => antiMode b m)

/-- **Beem–Garner's `Λ` on the ghost space**, truncated at level `N`. -/
def lamG (N : ℕ) : Module.End ℂ Sl2GhostSpace :=
  ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℂ)) • lamTerm m

/-- **Beem–Garner's `Λ` on the BRST space at weight `n`.** -/
def lamBRST (n : ℤ) : Module.End ℂ BRSTSpace :=
  TensorProduct.map LinearMap.id (lamG n.toNat)

theorem antiMode_anticomm (a b : Fin 3) (m n : ℤ) :
    antiMode a m * antiMode b n + antiMode b n * antiMode a m = 0 :=
  bGhost_modes_anticomm a b m n

/-- `Λ` commutes with the antighost zero modes. -/
theorem lamG_comm_antiMode_zero (c : Fin 3) (N : ℕ) :
    antiMode c 0 * lamG N = lamG N * antiMode c 0 := by
  unfold lamG
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact casContract_comm_of_anticomm _ _ _ (fun a => antiMode_anticomm c a 0 (-m))
    (fun b => antiMode_anticomm c b 0 m)

/-- The ghost current zero mode acts on the antighost modes by the adjoint action. -/
theorem ghostCurrent_antiMode (a c : Fin 3) (m : ℤ) :
    mode (ghostCurrentField a) 0 * antiMode c m =
      antiMode c m * mode (ghostCurrentField a) 0 + ∑ i, fabc a c i • antiMode i m := by
  have h := translationCovariant_sl2GhostSVA.mode_commutator_bound (bGhost_odd c)
    (ghostCurrent_even a) 1 (fun j hj => bGhost_high_ghostCurrent c a j (by omega)) m 0
  simp only [koszul_zero_right, one_smul, Finset.sum_range_one, gBinom_zero, Nat.cast_zero,
    sub_zero, add_zero, one_smul] at h
  rw [bGhost_zero_ghostCurrent c a] at h
  have e : mode (sl2GhostSVA.Y (-∑ i : Fin 3, fabc a c i • bGhost i)) m =
      -∑ i, fabc a c i • antiMode i m := by
    simp only [Fin.sum_univ_three, map_neg, map_add, map_smul, mode_neg, mode_add, mode_smul]
    rfl
  rw [e] at h
  change antiMode c m * mode (ghostCurrentField a) 0 -
    mode (ghostCurrentField a) 0 * antiMode c m = _ at h
  rw [← sub_eq_zero]
  have h' := congrArg Neg.neg h
  rw [neg_neg] at h'
  rw [← h']
  abel

/-- `Λ` commutes with the ghost current zero modes. -/
theorem lamG_comm_ghostCurrent (a : Fin 3) (N : ℕ) :
    mode (ghostCurrentField a) 0 * lamG N = lamG N * mode (ghostCurrentField a) 0 := by
  unfold lamG
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact casimir_comm _ _ _ a (fun c => ghostCurrent_antiMode a c (-m))
    (fun c => ghostCurrent_antiMode a c m)

/-- `Λ` preserves the ghost weight grading. -/
theorem lamG_mem_grading (N : ℕ) {h : ℂ} {y : Sl2GhostSpace}
    (hy : y ∈ sl2GhostSVA.grading h) : lamG N y ∈ sl2GhostSVA.grading h := by
  have hb : ∀ (a : Fin 3) (m : ℤ) {h : ℂ} {y : Sl2GhostSpace}, y ∈ sl2GhostSVA.grading h →
      antiMode a m y ∈ sl2GhostSVA.grading (h - m) := by
    intro a m h y hy
    have := sl2GhostSVA.grading_mode (bGhost a) (bGhost_weight a) y hy m
    rwa [show (1 : ℂ) + h - (m : ℂ) - 1 = h - m by ring] at this
  unfold lamG
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  unfold lamTerm casContract
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  refine Submodule.smul_mem _ _ ?_
  have := hb p (-m) (hb q m hy)
  rwa [show h - ((m : ℤ) : ℂ) - ((-(m : ℤ) : ℤ) : ℂ) = h by push_cast; ring] at this

/-! ### `Λ` on the BRST space -/

theorem lamBRST_tmul (n : ℤ) (x : MatterSpace) (y : Sl2GhostSpace) :
    lamBRST n (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] lamG n.toNat y := by
  simp [lamBRST]

/-- `Λ` commutes with the antighost zero modes on the BRST space. -/
theorem lamBRST_antighostZero (n : ℤ) (c : Fin 3) (z : BRSTSpace) :
    antighostZero matterSVA c (lamBRST n z) = lamBRST n (antighostZero matterSVA c z) := by
  rw [antighostZero_eq]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [lamBRST, TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      exact LinearMap.congr_fun (lamG_comm_antiMode_zero c n.toNat) y
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-- `Λ` commutes with the total current zero modes on the BRST space. -/
theorem lamBRST_totalCurrentZero (n : ℤ) (a : Fin 3) (z : BRSTSpace) :
    totalCurrentZero leeYangMatterAction.toAffineSl2Action a (lamBRST n z) =
      lamBRST n (totalCurrentZero leeYangMatterAction.toAffineSl2Action a z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [lamBRST_tmul, totalCurrentZero_tmul, totalCurrentZero_tmul, map_add, lamBRST_tmul,
        lamBRST_tmul]
      congr 2
      exact LinearMap.congr_fun (lamG_comm_ghostCurrent a n.toNat) y
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-- `Λ` preserves the relative carrier. -/
theorem lamBRST_mem_relativeCarrier (n : ℤ) {z : BRSTSpace}
    (hz : z ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action) :
    lamBRST n z ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action := by
  rw [mem_relativeCarrier] at hz ⊢
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [lamBRST_totalCurrentZero, hz.1 a, map_zero]
  · rw [lamBRST_antighostZero, hz.2 a, map_zero]

/-- `Λ` preserves the BRST weight grading. -/
theorem lamBRST_mem_grading (n : ℤ) {h : ℂ} {z : BRSTSpace} (hz : z ∈ brstSVA.grading h) :
    lamBRST n z ∈ brstSVA.grading h := by
  change z ∈ TensorVA.tenGrading matterSVA sl2GhostSVA h at hz
  change lamBRST n z ∈ TensorVA.tenGrading matterSVA sl2GhostSVA h
  refine TensorVA.tenGrading_induction matterSVA sl2GhostSVA
    (motive := fun z => lamBRST n z ∈ TensorVA.tenGrading matterSVA sl2GhostSVA h)
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ hz
  intro h₁ x hx y hy
  rw [lamBRST_tmul]
  exact TensorVA.tmul_mem_tenGrading matterSVA sl2GhostSVA hx (lamG_mem_grading _ hy)

/-- **`Λ` preserves every relative weight space.** -/
theorem lamBRST_mem_relativeWeight (n : ℤ) {z : BRSTSpace} (hz : z ∈ relativeWeight n) :
    lamBRST n z ∈ relativeWeight n :=
  ⟨lamBRST_mem_relativeCarrier n hz.1, lamBRST_mem_grading n hz.2⟩

/-! ### The `(0, -2)` shift -/

/-- The fine shift of `Λ`: `2R` unchanged, ghost number `-2`, weight unchanged, no `c₀`. -/
def lamShiftF : KF := (((0, -2), 0), 0)

theorem lamTerm_shift_eq (m : ℕ) (hm : 1 ≤ m) :
    ghShiftF 0 (-(m : ℤ) - 1) + ghShiftF 0 (-(-(m : ℤ)) - 1) = lamShiftF := by
  have h1 : ¬ (0 ≤ -(m : ℤ) - 1) := by omega
  have h2 : 0 ≤ -(-(m : ℤ)) - 1 := by omega
  have e1 : (-(-(m : ℤ) - 1) - 1).toNat = m := by omega
  have e2 : (-(-(m : ℤ)) - 1).toNat = m - 1 := by omega
  have hne : ((m, (0 : Fin 2) + 1) : ℕ × Fin 2) ≠ (0, 1) := by
    intro h; simp only [Prod.mk.injEq] at h; omega
  have hne' : ((m - 1, (0 : Fin 2)) : ℕ × Fin 2) ≠ (0, 1) := by
    intro h; simp only [Prod.mk.injEq] at h; exact absurd h.2 (by decide)
  simp only [ghShiftF, if_neg h1, if_pos h2, e1, e2, modeIdxF, if_neg hne, if_neg hne',
    modeIdx, modeR, ghCharge, ghModeWt, ghWt]
  simp only [lamShiftF, Prod.neg_mk, Prod.mk_add_mk, neg_zero, add_zero]
  refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) rfl
  · simp
  · simp
  · simp only
    have : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    simp [this]

/-- `Λ` shifts the fine ghost grading by `lamShiftF`. -/
theorem lamG_shiftF (N : ℕ) (k : KF) {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) :
    lamG N y ∈ ghostDegF (k + lamShiftF) := by
  unfold lamG
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  unfold lamTerm casContract
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  refine Submodule.smul_mem _ _ ?_
  have h1 := ghostModeF_mem q 0 (m : ℤ) hy
  have h2 := ghostModeF_mem p 0 (-(m : ℤ)) h1
  rwa [add_assoc, lamTerm_shift_eq m hm1] at h2

/-- `Λ` shifts the fine BRST grading by `lamShiftF`. -/
theorem lamBRST_shiftF (n : ℤ) (k : KF) {z : BRSTSpace} (hz : z ∈ brstDegF k) :
    lamBRST n z ∈ brstDegF (k + lamShiftF) := by
  have := tensorDeg_map_shift matterF ghostDegF LinearMap.id (lamG n.toNat) 0 lamShiftF
    (fun i x hx => by rw [add_zero]; exact hx) (fun i y hy => lamG_shiftF _ i hy) k z hz
  rwa [zero_add] at this

/-- **`Λ` shifts the interpreted `(2R, gh)` grading by `(0, -2)`**, for every standard ghost
grading. -/
theorem lamBRST_shift {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd)
    (n j g : ℤ) (h : ℂ) {z : BRSTSpace} (hz : z ∈ brstDeg Gh ((j, g), h)) :
    lamBRST n z ∈ brstDeg Gh ((j, g - 2), h) := by
  rw [brstDeg_std hs] at hz ⊢
  have hz' := brstDeg_le_coarsenF unitWeight _ hz
  refine Submodule.iSup_induction _ (motive := fun z =>
    lamBRST n z ∈ brstDeg (ghostRGrading unitWeight) ((j, g - 2), h)) hz' ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun y =>
    lamBRST n y ∈ brstDeg (ghostRGrading unitWeight) ((j, g - 2), h)) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hk y hy
  have h1 := brstDegF_le_brstDeg unitWeight _ (lamBRST_shiftF n k hy)
  have e : fstF (k + lamShiftF) = ((j, g - 2), h) := by
    rw [map_add, hk]
    change ((j, g), h) + (((0, -2), 0) : (ℤ × ℤ) × ℂ) = _
    simp only [Prod.mk_add_mk, add_zero]
    congr 2
  rwa [e] at h1

end

end VOA.ConcreteHodge
