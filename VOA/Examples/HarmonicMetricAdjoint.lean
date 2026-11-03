/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.HarmonicMetricReal
import VOA.Examples.HarmonicMetricVacuum

/-!
# The coset creation modes are adjoint on the explicit representatives

For `B_{AB} = B_A ⊗ B_B` on `A ⊗ B` and coset vectors `x, y`:

* `ambient_mode_eq`, `BAB_ambient_adj` — the ambient Virasoro modes `L^A_n ⊗ 1 + 1 ⊗ L^B_n` are
  `B_{AB}`-adjoint to the modes at `-n` (from the invariance of the two simple affine forms);
* `creationSpan` — the span of all diagonal-current creation coefficients `J^a_{(-1-m)} w`;
  it is `B_{AB}`-orthogonal to the coset (current skewness, `BAB_creationSpan_coset`), stable
  under translation and under `x_{(-1)}` for coset `x`, and contains the diagonal Sugawara vector;
* `BAB_sugawara_neg_coset` — `B_{AB}(S_{(n)} x, y) = 0` for `n ≤ -1`, since
  `S_{(n)} x = x_{(-1)} S_{(n)} |0⟩` and `S_{(n)}|0⟩` is a translate of `S`;
* `BAB_coset_creation_adj` — `B_{AB}(L^C_{-i-2} x, y) = B_{AB}(x, L^C_{i+2} y)`;
* `repCreationAdjoint_proved : RepCreationAdjoint`.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Coset
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open AffineVOA
open scoped TensorProduct

noncomputable section


/-! ### Adjoint operators on a tensor product -/

theorem tensorB_adj_rTensor_lTensor {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (BV : LinearMap.BilinForm ℂ V) (BW : LinearMap.BilinForm ℂ W)
    (A A' : Module.End ℂ V) (C C' : Module.End ℂ W)
    (hA : ∀ x x', BV (A x) x' = BV x (A' x')) (hC : ∀ y y', BW (C y) y' = BW y (C' y'))
    (u v : V ⊗[ℂ] W) :
    (BV.tmul BW) ((A.rTensor W + C.lTensor V) u) v =
      (BV.tmul BW) u ((A'.rTensor W + C'.lTensor V) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' =>
      simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
      linear_combination hu + hu'
  | tmul x y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
          simp only [map_add, LinearMap.add_apply] at hv hv' ⊢
          linear_combination hv + hv'
      | tmul x' y' =>
          simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
            map_add, LinearMap.add_apply, bilinTmul_tmul, hA, hC]

/-- `B_A ⊗ B_B`. -/
abbrev BAB : LinearMap.BilinForm ℂ (ASpace ⊗[ℂ] BSpace) := affineForm.form.tmul bForm.form

/-! ### The ambient Virasoro modes -/

theorem bSpace_parity_zero (y : BSpace) : y ∈ BSVA.parity 0 := by
  change y ∈ (ParityGrading.even BSpace).parity 0
  rw [ParityGrading.even_parity_zero]
  exact Submodule.mem_top

theorem ambient_mode_eq (n : ℤ) (z : ASpace ⊗[ℂ] BSpace) :
    mode (abSVA.Y ambientConformal) (n + 1) z =
      ((AVOA.L n).rTensor BSpace + (BVOA.L n).lTensor ASpace) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add]
  | tmul x y =>
      change mode (TensorVA.tenY ASVA BSVA (AVOA.conformalVector ⊗ₜ[ℂ] BSVA.vacuum +
        ASVA.vacuum ⊗ₜ[ℂ] BVOA.conformalVector)) (n + 1) (x ⊗ₜ[ℂ] y) = _
      rw [map_add, mode_add, LinearMap.add_apply, mode_apply, mode_apply, tenY_left_unit,
        tenY_right_unit_even ASVA BSVA (bSpace_parity_zero _)]
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      rw [VertexOperatorAlgebra.L_def, VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def,
        ← PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, mode_apply,
        mode_apply]
      rfl

theorem BAB_ambient_adj (n : ℤ) (u v : ASpace ⊗[ℂ] BSpace) :
    BAB (mode (abSVA.Y ambientConformal) (n + 1) u) v =
      BAB u (mode (abSVA.Y ambientConformal) (-n + 1) v) := by
  rw [ambient_mode_eq, ambient_mode_eq]
  exact tensorB_adj_rTensor_lTensor _ _ _ _ _ _ (affineForm.virasoro_adj n)
    (bForm.virasoro_adj n) u v

/-! ### Diagonal-current creation span -/

/-- The diagonal current coefficient `J^a_{(-1-m)}` on `A ⊗ B`. -/
abbrev Jd (a : Fin 3) (m : ℤ) : Module.End ℂ (ASpace ⊗[ℂ] BSpace) :=
  abSVA.Y (diagonalAction.current a) m

theorem Jd_mode_eq (a : Fin 3) (n : ℤ) (z : ASpace ⊗[ℂ] BSpace) :
    mode (abSVA.Y (diagonalAction.current a)) n z =
      ((aMode a n).rTensor BSpace + (bMode a n).lTensor ASpace) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add]
  | tmul x y =>
      have h := tensorCurrentMode_tmul aAction.toAffineSl2Action bAction.toAffineSl2Action a n x y
      exact h

theorem BAB_Jd_skew (a : Fin 3) (n : ℤ) (u v : ASpace ⊗[ℂ] BSpace) :
    BAB (mode (abSVA.Y (diagonalAction.current a)) n u) v =
      -BAB u (mode (abSVA.Y (diagonalAction.current a)) (-n) v) := by
  rw [Jd_mode_eq, Jd_mode_eq]
  exact tensorB_add_rTensor_lTensor _ _ _ _ _ _ (aMode_adj a n) (bCompactUnitary.skew a n) u v

/-- The span of the diagonal-current creation coefficients. -/
def creationSpan : Submodule ℂ (ASpace ⊗[ℂ] BSpace) :=
  Submodule.span ℂ {z | ∃ (a : Fin 3) (m : ℕ) (w : ASpace ⊗[ℂ] BSpace), z = Jd a m w}

theorem Jd_mem_creationSpan (a : Fin 3) (m : ℕ) (w : ASpace ⊗[ℂ] BSpace) :
    Jd a m w ∈ creationSpan :=
  Submodule.subset_span ⟨a, m, w, rfl⟩

theorem BAB_creationSpan_coset {z : ASpace ⊗[ℂ] BSpace} (hz : z ∈ creationSpan)
    {y : ASpace ⊗[ℂ] BSpace} (hy : y ∈ cosetSubspace diagonalAction.toAffineSl2Action) :
    BAB z y = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have e : Jd a m w = mode (abSVA.Y (diagonalAction.current a)) (-(m : ℤ) - 1) w := by
        rw [mode_apply, show -(-(m : ℤ) - 1) - 1 = m by ring]
      rw [e, BAB_Jd_skew, hy a _ (by omega), map_zero, neg_zero]
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem T_mem_creationSpan {z : ASpace ⊗[ℂ] BSpace} (hz : z ∈ creationSpan) :
    diagonalAction.translation.T z ∈ creationSpan := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have h := diagonalAction.translation.comm_Ycoeff (diagonalAction.current a) m
      rw [LieRing.of_associative_ring_bracket] at h
      have h' := LinearMap.congr_fun h w
      rw [← Int.cast_smul_eq_zsmul ℂ] at h'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h'
      have e : diagonalAction.translation.T (Jd a m w) =
          Jd a m (diagonalAction.translation.T w) +
            (((m : ℤ) + 1 : ℤ) : ℂ) • Jd a ((m : ℤ) + 1) w := by
        rw [← h']; abel
      rw [e]
      refine Submodule.add_mem _ (Jd_mem_creationSpan _ _ _) (Submodule.smul_mem _ _ ?_)
      exact_mod_cast Jd_mem_creationSpan a (m + 1) w
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem coset_mem_creationSpan {x : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace diagonalAction.toAffineSl2Action) {z : ASpace ⊗[ℂ] BSpace}
    (hz : z ∈ creationSpan) : mode (abSVA.Y x) (-1) z ∈ creationSpan := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have h := current_mode_coset_mode_commute diagonalAction.toAffineSl2Action
        diagonalAction.translation hx a (-(m : ℤ) - 1) (-1)
      have h' := LinearMap.congr_fun h w
      rw [Module.End.mul_apply, Module.End.mul_apply, mode_apply (abSVA.Y _) (-(m : ℤ) - 1),
        show -(-(m : ℤ) - 1) - 1 = m by ring] at h'
      change mode (abSVA.Y x) (-1) (abSVA.Y (diagonalAction.current a) m w) ∈ creationSpan
      rw [← h']
      exact Jd_mem_creationSpan _ _ _
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem diagonalSugawara_mem : diagonalSugawara ∈ creationSpan := by
  change (2 * ((-4 / 3 : ℂ) + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode (abSVA.Y (diagonalAction.current b)) (-1)
        (diagonalAction.current c) ∈ creationSpan
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ ?_)
  rw [mode_apply, show -(-1 : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num]
  exact Jd_mem_creationSpan _ _ _

theorem sugawara_vacuum_mem (m : ℕ) :
    abSVA.Y diagonalSugawara m abSVA.vacuum ∈ creationSpan := by
  induction m with
  | zero =>
      have h := (abSVA.creation diagonalSugawara).1
      rw [mode_apply, show -(-1 : ℤ) - 1 = 0 by norm_num] at h
      rw [Nat.cast_zero, h]
      exact diagonalSugawara_mem
  | succ m ih =>
      have h := diagonalAction.translation.comm_Ycoeff diagonalSugawara m
      rw [LieRing.of_associative_ring_bracket] at h
      have h' := LinearMap.congr_fun h abSVA.vacuum
      rw [← Int.cast_smul_eq_zsmul ℂ] at h'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        diagonalAction.translation.vacuum_zero, map_zero, sub_zero] at h'
      have hT := T_mem_creationSpan ih
      rw [h'] at hT
      have hne : (((m : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (m : ℤ) + 1 ≠ 0)
      have := Submodule.smul_mem creationSpan ((((m : ℤ) + 1 : ℤ) : ℂ)⁻¹) hT
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      exact_mod_cast this

/-- **The negative Sugawara modes of a coset vector are orthogonal to the coset.** -/
theorem BAB_sugawara_neg_coset {x y : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace diagonalAction.toAffineSl2Action)
    (hy : y ∈ cosetSubspace diagonalAction.toAffineSl2Action) (m : ℕ) :
    BAB (mode (abSVA.Y diagonalSugawara) (-(m : ℤ) - 1) x) y = 0 := by
  have hc := sugawara_mode_coset_mode_commute diagonalAction.toAffineSl2Action
    diagonalAction.translation hx (-(m : ℤ) - 1) (-1)
  have h := LinearMap.congr_fun hc abSVA.vacuum
  simp only [Module.End.mul_apply, (abSVA.creation x).1] at h
  change BAB (mode (abSVA.Y (sugawaraState diagonalAction.toAffineSl2Action)) _ x) y = 0
  rw [h]
  apply BAB_creationSpan_coset _ hy
  apply coset_mem_creationSpan hx
  have := sugawara_vacuum_mem m
  rwa [mode_apply, show -(-(m : ℤ) - 1) - 1 = m by ring]

/-- **Coset creation modes are adjoint to annihilation modes on the coset.** -/
theorem BAB_coset_creation_adj (i : ℕ) {x y : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace diagonalAction.toAffineSl2Action)
    (hy : y ∈ cosetSubspace diagonalAction.toAffineSl2Action) :
    BAB (mode (abSVA.Y cosetOmega) (-(i : ℤ) - 1) x) y =
      BAB x (mode (abSVA.Y cosetOmega) ((i : ℤ) + 3) y) := by
  rw [cosetOmega, map_sub, mode_sub, mode_sub, LinearMap.sub_apply, LinearMap.sub_apply,
    map_sub, LinearMap.sub_apply, map_sub]
  have h1 := BAB_sugawara_neg_coset hx hy (i + 0)
  rw [show -((i + 0 : ℕ) : ℤ) - 1 = -(i : ℤ) - 1 by push_cast; ring] at h1
  have h2 : mode (abSVA.Y diagonalSugawara) ((i : ℤ) + 3) y = 0 :=
    sugawara_mode_coset diagonalAction.toAffineSl2Action diagonalAction.translation hy _
      (by omega)
  rw [h1, h2, map_zero, sub_zero, sub_zero]
  have h3 := BAB_ambient_adj (-(i : ℤ) - 2) x y
  rw [show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring,
    show -(-(i : ℤ) - 2) + 1 = (i : ℤ) + 3 by ring] at h3
  exact h3

/-! ### The explicit representatives -/

theorem ghBBRST_repVec (p q : ASpace ⊗[ℂ] BSpace) :
    ghBBRST ((p ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum)
        ((q ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = BAB p q := by
  rw [← gvac_eq, ghBBRST, bilinTmul_tmul, ghostB_gvac, mul_one, matterB, bilinTmul_tmul,
    show auxiliaryForm.form USVA.vacuum USVA.vacuum = 1 from
      universalForm_normalized (-11 / 3) uNoncritical, mul_one]

theorem virasoroToCoset_Lop_val (n : ℤ) (u : VirUniv leeYangC) :
    ((virasoroToCoset (Lop leeYangC n u) : CosetSpace) : ASpace ⊗[ℂ] BSpace) =
      mode (abSVA.Y cosetOmega) (n + 1) (virasoroToCoset u : CosetSpace) := by
  rw [show virasoroToCoset (Lop leeYangC n u) = cosetVOA.L n (virasoroToCoset u) from
    conformalEval_L cosetVOA rfl _ _]
  rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetMode_coe]
  rfl

/-- **`RepCreationAdjoint` is proved.** -/
theorem repCreationAdjoint_proved : RepCreationAdjoint := by
  intro i u v
  rw [repVec, repVec, repVec, repVec, cosetToComplex_apply, cosetToComplex_apply,
    cosetToComplex_apply, cosetToComplex_apply, ghBBRST_repVec, ghBBRST_repVec,
    virasoroToCoset_Lop_val, virasoroToCoset_Lop_val,
    show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring, show (i : ℤ) + 2 + 1 = (i : ℤ) + 3 by ring]
  exact BAB_coset_creation_adj i (virasoroToCoset u).2 (virasoroToCoset v).2

end

end VOA.ConcreteHodge
