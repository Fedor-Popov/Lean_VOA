/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualGhost0
import VOA.Examples.BGPackageTensor

/-!
# The symbol maps on the antighost-free blocks

On the antighost-free blocks of the actual relative complex at `(2r, 0)` and `(2r + 1, 1)`:

* the vacuum extraction `extM`, `ext0` (from a functional `vacφ` with `vacφ gvac = 1`);
* `π₀ x = PiR (ev (extM x))` and `π₁ y (c, k) = PiR (ev (extM (b^c_{(k)} y)))`.

Everything is proved outright from `hA`.
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open VOA.SymbolModel VOA.CyclicEval AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### The vacuum functional -/

theorem gvac_ne_zero : gvac ≠ 0 := by
  rw [gvac_eq]; exact sl2GhostSVA_vacuum_ne_zero

/-- A functional with `vacφ gvac = 1`. -/
def vacφ : Module.Dual ℂ Sl2GhostSpace :=
  Classical.choose (Module.Projective.exists_dual_eq_one ℂ gvac_ne_zero)

theorem vacφ_gvac : vacφ gvac = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ gvac_ne_zero)

/-- The projection onto the vacuum line along `ker vacφ`. -/
def Pvac : Module.End ℂ Sl2GhostSpace := LinearMap.smulRight vacφ gvac

theorem Pvac_apply (g : Sl2GhostSpace) : Pvac g = vacφ g • gvac := rfl

theorem Pvac_of_mem {g : Sl2GhostSpace} (hg : g ∈ ℂ ∙ gvac) : Pvac g = g := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hg
  rw [Pvac_apply, map_smul, vacφ_gvac, smul_eq_mul, mul_one]

/-- The matter coefficient of the vacuum: `m ⊗ g ↦ vacφ(g) m`. -/
def extM : BRSTSpace →ₗ[ℂ] MatterSpace :=
  (TensorProduct.rid ℂ MatterSpace).toLinearMap ∘ₗ TensorProduct.map LinearMap.id vacφ

theorem extM_tmul (m : MatterSpace) (g : Sl2GhostSpace) : extM (m ⊗ₜ[ℂ] g) = vacφ g • m := by
  simp [extM]

theorem map_Pvac_eq (v : BRSTSpace) :
    TensorProduct.map LinearMap.id Pvac v = extM v ⊗ₜ[ℂ] gvac := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, TensorProduct.add_tmul]
  | tmul m g =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, Pvac_apply, extM_tmul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-! ### Ghost pieces of the antighost-free blocks -/

theorem ghostDegF_eq_zero_of {k : KF} (hb : b2 k = 0) (hc : c2 k = 0) (hk : k ≠ 0) :
    ∀ y ∈ ghostDegF k, y = 0 := by
  refine ghostDegF_induction k (fun y => y = 0) rfl (fun x y hx hy => by rw [hx, hy, add_zero])
    (fun c x hx => by rw [hx, smul_zero]) ?_
  intro l0 l1 l2 hsum
  have hb' := hb
  have hc' := hc
  rw [← hsum, map_add, map_add, b2_wordIdxF, b2_wordIdxF, b2_wordIdxF] at hb'
  rw [← hsum, map_add, map_add, c2_wordIdxF, c2_wordIdxF, c2_wordIdxF] at hc'
  have e0 := nb_add_ncnt l0
  have e1 := nb_add_ncnt l1
  have e2 := nb_add_ncnt l2
  have h0 : l0 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have h1 : l1 = [] := List.eq_nil_of_length_eq_zero (by omega)
  have h2 : l2 = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst h0 h1 h2
  exfalso; apply hk; rw [← hsum]; simp [wordIdxF]

theorem matterDeg_ghost_eq_bot {i : (ℤ × ℤ) × ℂ} (hi : i.1.2 ≠ 0) : matterDeg i = ⊥ :=
  tensorDeg_eq_bot_of (fun i : (ℤ × ℤ) × ℂ => i.1.2 = 0) (fun a b ha hb => by
      simp only [Prod.fst_add, Prod.snd_add]; omega) _ _
    (fun _ h => tensorDeg_eq_bot_of (fun i : (ℤ × ℤ) × ℂ => i.1.2 = 0) (fun a b ha hb => by
        simp only [Prod.fst_add, Prod.snd_add]; omega) _ _
      (fun _ h => layerDeg_ghost _ _ _ h) (fun _ h => trivialDeg_ghost _ h) h)
    (fun _ h => layerDeg_ghost _ _ _ h) hi

/-- Facts about a nonzero matter factor of a joint piece. -/
theorem matterB_facts {j1 : KF × ℤ} {m : MatterSpace} (hm : m ∈ KoszulConcrete.matterB j1)
    (h0 : m ≠ 0) : j1.2 = 0 ∧ j1.1.2 = 0 ∧ j1.1.1.1.2 = 0 ∧ m ∈ matterDeg j1.1.1 := by
  unfold KoszulConcrete.matterB matterF at hm
  split_ifs at hm with h1 h2
  · refine ⟨h1, h2, ?_, hm⟩
    by_contra h
    rw [matterDeg_ghost_eq_bot h, Submodule.mem_bot] at hm
    exact h0 hm
  all_goals exact absurd ((Submodule.mem_bot ℂ).mp hm) h0

theorem b2_c2_gh (k : KF) : c2 k = b2 k + 2 * k.1.1.2 := by simp; ring

/-- **The vacuum form of the antighost-free, ghost-number-zero joint pieces.** -/
theorem vacForm_blockB {j : KF × ℤ} (h2 : j.2 = 0) (hgh : j.1.1.1.2 = 0) :
    ∀ v ∈ KoszulConcrete.blockB j,
      TensorProduct.map LinearMap.id Pvac v = v ∧ extM v ∈ matterDeg j.1.1 := by
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j
    (fun v => TensorProduct.map LinearMap.id Pvac v = v ∧ extM v ∈ matterDeg j.1.1)
    ⟨map_zero _, by rw [map_zero]; exact Submodule.zero_mem _⟩
    (fun x y hx hy => ⟨by rw [map_add, hx.1, hy.1], by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩)
    (fun c x hx => ⟨by rw [map_smul, hx.1], by rw [map_smul]; exact Submodule.smul_mem _ c hx.2⟩) ?_
  intro b m hm g hg
  by_cases hm0 : m = 0
  · subst hm0; simp
  obtain ⟨hb2, -, hbgh, hmD⟩ := matterB_facts hm hm0
  unfold KoszulConcrete.ghostB at hg
  split_ifs at hg with hgb
  · have hb0 : b2 (j - b).1 = 0 := by rw [hgb]; simp [h2, hb2]
    have hgh0 : (j - b).1.1.1.2 = 0 := by simp [hgh, hbgh]
    have hc0 : c2 (j - b).1 = 0 := by rw [b2_c2_gh, hb0, hgh0]; ring
    refine ⟨?_, ?_⟩
    · rw [TensorProduct.map_tmul, LinearMap.id_apply, Pvac_of_mem (ghostDegF_le_vac hb0 hc0 g hg)]
    · rw [extM_tmul]
      by_cases hk : (j - b).1 = 0
      · have : b.1 = j.1 := by
          have := congrArg Prod.fst (show (j - b) = (0, (j - b).2) from Prod.ext hk rfl)
          simp only [Prod.fst_sub] at this
          exact (sub_eq_zero.mp this).symm
        rw [← this]
        exact Submodule.smul_mem _ _ hmD
      · rw [ghostDegF_eq_zero_of hb0 hc0 hk g hg, map_zero, zero_smul]
        exact Submodule.zero_mem _
  · rw [Submodule.mem_bot] at hg
    subst hg
    simp

/-- The `c`-mode `c^c_{-kk}` annihilator `b^c_{(kk)}` as an `An`. -/
abbrev bAn (c : Fin 3) (kk : ℕ) : Module.End ℂ Sl2GhostSpace := ConcreteHodge.An c (kk, 1)

theorem bAn_mem_ghostDegF (c : Fin 3) (kk : ℕ) {k : KF} {y : Sl2GhostSpace}
    (hy : y ∈ ghostDegF k) : bAn c kk y ∈ ghostDegF (k - modeIdxF (kk, 1)) := by
  have h := ghostModeF_mem c 0 (kk : ℤ) hy
  have e : ghShiftF 0 (-(kk : ℤ) - 1) = -modeIdxF (kk, 1) := by
    unfold ghShiftF
    rw [if_neg (by omega)]
    congr 2
    refine Prod.ext ?_ rfl
    simp only
    omega
  rw [e, ← sub_eq_add_neg] at h
  exact h

theorem b2_modeIdxF_c (kk : ℕ) : b2 (modeIdxF (kk, 1)) = 0 := by rw [b2_modeIdxF]; rfl

theorem c2_modeIdxF_c (kk : ℕ) : c2 (modeIdxF (kk, 1)) = 2 := by rw [c2_modeIdxF]; rfl

/-- **The one-`c` form**: on the antighost-free, ghost-number-one joint pieces of weight
`≤ N`, `Σ_{c, kk ≤ N} c_{-kk} b_{(kk)}` is the identity, and every `b_{(kk)}` lands in the vacuum
form, with matter index lowered by `((1, 1), kk)`. -/
theorem oneC_blockB (N : ℕ) {j : KF × ℤ} (h2 : j.2 = 0) (hgh : j.1.1.1.2 = 1) {n0 : ℤ}
    (hn0 : j.1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    ∀ v ∈ KoszulConcrete.blockB j, TensorProduct.map LinearMap.id (NT (Tc N)) v = v := by
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j
    (fun v => TensorProduct.map LinearMap.id (NT (Tc N)) v = v) (map_zero _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx]) ?_
  intro b m hm g hg
  by_cases hm0 : m = 0
  · subst hm0; simp
  obtain ⟨hb2, -, hbgh, hmD⟩ := matterB_facts hm hm0
  obtain ⟨wm, hwm⟩ := matterB_nat hm hm0
  unfold KoszulConcrete.ghostB at hg
  split_ifs at hg with hgb
  · have hb0 : b2 (j - b).1 = 0 := by rw [hgb]; simp [h2, hb2]
    have hgh1 : (j - b).1.1.1.2 = 1 := by simp [hgh, hbgh]
    have hc2 : c2 (j - b).1 = 2 * 1 := by rw [b2_c2_gh, hb0, hgh1]; ring
    rw [TensorProduct.map_tmul, LinearMap.id_apply, Nc_ghostDegF N hc2 ?_ g hg, Int.cast_one,
      one_smul]
    intro w hw
    have : (w : ℂ) = (n0 : ℂ) - (wm : ℂ) := by
      rw [hw]; simp only [Prod.fst_sub, Prod.snd_sub, hn0, ← hwm]
    have h' : (w : ℤ) = n0 - wm := by exact_mod_cast this
    omega
  · rw [Submodule.mem_bot] at hg
    subst hg
    simp

theorem bAn_blockB (c : Fin 3) {kk : ℕ} (hkk : 1 ≤ kk) {j : KF × ℤ} (h2 : j.2 = 0)
    (hgh : j.1.1.1.2 = 1) :
    ∀ v ∈ KoszulConcrete.blockB j,
      TensorProduct.map LinearMap.id Pvac (TensorProduct.map LinearMap.id (bAn c kk) v) =
        TensorProduct.map LinearMap.id (bAn c kk) v ∧
      extM (TensorProduct.map LinearMap.id (bAn c kk) v) ∈
        matterDeg (j.1.1 - ((1, 1), (kk : ℂ))) := by
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j
    (fun v => TensorProduct.map LinearMap.id Pvac (TensorProduct.map LinearMap.id (bAn c kk) v) =
        TensorProduct.map LinearMap.id (bAn c kk) v ∧
      extM (TensorProduct.map LinearMap.id (bAn c kk) v) ∈
        matterDeg (j.1.1 - ((1, 1), (kk : ℂ))))
    ⟨by simp, by simp⟩
    (fun x y hx hy => ⟨by rw [map_add, map_add, hx.1, hy.1], by
      rw [map_add, map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩)
    (fun c' x hx => ⟨by rw [map_smul, map_smul, hx.1], by
      rw [map_smul, map_smul]; exact Submodule.smul_mem _ c' hx.2⟩) ?_
  intro b m hm g hg
  by_cases hm0 : m = 0
  · subst hm0; simp
  obtain ⟨hb2, -, hbgh, hmD⟩ := matterB_facts hm hm0
  unfold KoszulConcrete.ghostB at hg
  split_ifs at hg with hgb
  · have hb0 : b2 (j - b).1 = 0 := by rw [hgb]; simp [h2, hb2]
    have hgh1 : (j - b).1.1.1.2 = 1 := by simp [hgh, hbgh]
    have hc2 : c2 (j - b).1 = 2 := by rw [b2_c2_gh, hb0, hgh1]; ring
    have hg' := bAn_mem_ghostDegF c kk hg
    have hb0' : b2 ((j - b).1 - modeIdxF (kk, 1)) = 0 := by
      rw [map_sub, hb0, b2_modeIdxF_c, sub_zero]
    have hc0' : c2 ((j - b).1 - modeIdxF (kk, 1)) = 0 := by
      rw [map_sub, hc2, c2_modeIdxF_c, sub_self]
    refine ⟨?_, ?_⟩
    · rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        Pvac_of_mem (ghostDegF_le_vac hb0' hc0' _ hg')]
    · rw [TensorProduct.map_tmul, LinearMap.id_apply, extM_tmul]
      by_cases hk : (j - b).1 - modeIdxF (kk, 1) = 0
      · have hidx : b.1.1 = j.1.1 - ((1, 1), (kk : ℂ)) := by
          have h1 := congrArg Prod.fst hk
          simp only [Prod.fst_sub, Prod.fst_zero] at h1
          rw [sub_eq_zero] at h1
          have h3 : (modeIdxF (kk, 1)).1 = ((1, 1), (kk : ℂ)) := by
            simp [modeIdxF, modeIdx, modeR, ghCharge, ghModeWt, ghWt]
            omega
          rw [h3] at h1
          rw [← h1]; abel
        rw [← hidx]
        exact Submodule.smul_mem _ _ hmD
      · rw [ghostDegF_eq_zero_of hb0' hc0' hk _ hg', map_zero, zero_smul]
        exact Submodule.zero_mem _
  · rw [Submodule.mem_bot] at hg
    subst hg
    simp

/-! ### The positive modes on the matter space: components -/

section PosComp

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The `R`-lowering shift of a positive mode. -/
abbrev emn (n : ℕ) : (ℤ × ℤ) × ℂ := ((-2, 0), (((-(n : ℤ)) : ℤ) : ℂ))

theorem modePred_nonneg_cases (n : ℕ) :
    ∀ δ, modePred (n : ℤ) δ → δ = e0n n ∨ δ = emn n := by
  intro δ h
  obtain ⟨d, rfl, h1, h2⟩ := modePred_nonneg h
  rcases (show d = 0 ∨ d = -1 by omega) with rfl | rfl
  · left; simp
  · right; simp

theorem e0n_ne_emn (n : ℕ) : e0n n ≠ emn n := by
  intro h; have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h; simp at this

theorem aMode_sub_aPos_mem' (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : ASpace}
    (hx : x ∈ aDeg i) : aMode c n x - aPos hA c n x ∈ aDeg (i + emn n) := by
  rw [aPos_of_mem hA c n hx]
  exact sub_iproj_mem_of_two (aDeg_isInternal hA) (modePred_nonneg_cases n) (e0n_ne_emn n)
    (aMode_shifts hA c n i x hx)

theorem uPos_of_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    uPos c n x = uP (i + e0n n) (uMode c n x) := by
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    apply PhiU.injective
    rw [PhiU_uPos]
    have e : layerIndex t m + e0n n = layerIndex t (m - n) := by
      simp only [layerIndex, e0n, Prod.mk_add_mk, add_zero]; push_cast; ring_nf
    rw [e, PhiU_uP_nonneg c n hx]
  · push Not at hi
    rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hx
    rw [hx, map_zero, map_zero, map_zero]

theorem uMode_sub_uPos_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : USpace}
    (hx : x ∈ uDeg i) : uMode c n x - uPos c n x ∈ uDeg (i + emn n) := by
  rw [uPos_of_mem c n hx]
  exact sub_iproj_mem_of_two uDeg_isInternal (modePred_nonneg_cases n) (e0n_ne_emn n)
    (uMode_shifts _ _ i x hx)

theorem uPos_mem (c : Fin 3) (n : ℕ) {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    uPos c n x ∈ uDeg (i + e0n n) := by
  rw [uPos_of_mem c n hx]; exact iproj_mem _ _ _

theorem neg_cast_e (n : ℕ) : (((-(n : ℤ)) : ℤ) : ℂ) = ((-(n : ℤ) : ℤ) : ℂ) := rfl

/-- `mPos` preserves `R`; `mMode - mPos` lowers it by one. -/
theorem mPos_mem (c : Fin 3) (n : ℕ) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, mPos hA c n m ∈ matterDeg (i + e0n n) := by
  intro m hm
  rw [mPos, LinearMap.add_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · have hin : ∀ i, ∀ z ∈ tensorDeg aDeg bDeg i,
        TensorProduct.map (aPos hA c n) LinearMap.id z ∈ tensorDeg aDeg bDeg (i + e0n n) := by
      intro i z hz
      have h := tensorDeg_map_shift aDeg bDeg (aPos hA c n) LinearMap.id (e0n n) 0
        (fun i x hx => aPos_mem hA c n hx) (fun i y hy => by rwa [add_zero]) i z hz
      rwa [add_zero] at h
    have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg _ LinearMap.id (e0n n) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have hin : ∀ i, ∀ z ∈ tensorDeg aDeg bDeg i,
        TensorProduct.map LinearMap.id (bMode c n) z ∈ tensorDeg aDeg bDeg (i + e0n n) := by
      intro i z hz
      have h := tensorDeg_map_shift aDeg bDeg LinearMap.id (bMode c n) 0 (e0n n)
        (fun i x hx => by rwa [add_zero]) (fun i y hy => bMode_mem c n hy) i z hz
      rwa [zero_add] at h
    have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg _ LinearMap.id (e0n n) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg LinearMap.id (uPos c n) 0 (e0n n)
      (fun i z hz => by rwa [add_zero]) (fun i y hy => uPos_mem c n hy) i m hm
    rwa [zero_add] at h

theorem mMode_sub_mPos_mem (c : Fin 3) (n : ℕ) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, mMode c n m - mPos hA c n m ∈ matterDeg (i + emn n) := by
  intro m hm
  have hsplit : mMode c n - mPos hA c n =
      TensorProduct.map (TensorProduct.map (aMode c n - aPos hA c n)
        (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ USpace) +
      TensorProduct.map (LinearMap.id : Module.End ℂ (ASpace ⊗[ℂ] BSpace))
        (uMode c n - uPos c n) := by
    have e1 : TensorProduct.map (TensorProduct.map (aMode c n - aPos hA c n)
        (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ USpace) =
        TensorProduct.map (TensorProduct.map (aMode c n)
          (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ USpace) -
          TensorProduct.map (TensorProduct.map (aPos hA c n) (LinearMap.id : Module.End ℂ BSpace))
          (LinearMap.id : Module.End ℂ USpace) := by
      change LinearMap.rTensor USpace (LinearMap.rTensor BSpace (aMode c n - aPos hA c n)) =
        LinearMap.rTensor USpace (LinearMap.rTensor BSpace (aMode c n)) -
          LinearMap.rTensor USpace (LinearMap.rTensor BSpace (aPos hA c n))
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_sub]
    have e2 : TensorProduct.map (LinearMap.id : Module.End ℂ (ASpace ⊗[ℂ] BSpace))
        (uMode c n - uPos c n) =
        TensorProduct.map LinearMap.id (uMode c n) - TensorProduct.map LinearMap.id (uPos c n) := by
      change LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uMode c n - uPos c n) =
        LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uMode c n) -
          LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uPos c n)
      rw [LinearMap.lTensor_sub]
    rw [mMode, matterMode_eq, mPos, e1, e2]
    abel
  rw [← LinearMap.sub_apply, hsplit, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have hin : ∀ i, ∀ z ∈ tensorDeg aDeg bDeg i,
        TensorProduct.map (aMode c n - aPos hA c n) LinearMap.id z ∈
          tensorDeg aDeg bDeg (i + emn n) := by
      intro i z hz
      have h := tensorDeg_map_shift aDeg bDeg (aMode c n - aPos hA c n) LinearMap.id (emn n) 0
        (fun i x hx => aMode_sub_aPos_mem' hA c n hx) (fun i y hy => by rwa [add_zero]) i z hz
      rwa [add_zero] at h
    have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg _ LinearMap.id (emn n) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg LinearMap.id
      (uMode c n - uPos c n) 0 (emn n) (fun i z hz => by rwa [add_zero])
      (fun i y hy => uMode_sub_uPos_mem c n hy) i m hm
    rwa [zero_add] at h

/-- On the zero modes, `mPos` is the full mode. -/
theorem mPos_zero (c : Fin 3) (m : MatterSpace) : mPos hA c 0 m = mMode c 0 m := by
  have hA0 : aPos hA c 0 = aMode c 0 := by
    apply linearMap_ext_internal (aDeg_isInternal hA)
    intro i x hx
    rw [aPos_of_mem hA c 0 hx]
    have h := aZeroModesPreserveLayers c i x hx
    have e : i + e0n 0 = i := by simp
    rw [e]
    exact iproj_of_mem_same _ h
  have hU0 : uPos c 0 = uMode c 0 := by
    refine LinearMap.ext fun x => PhiU.injective ?_
    rw [PhiU_uPos, PhiU_uMode_zero]
  rw [mPos, mMode, matterMode_eq, hA0, hU0]
  rfl

end PosComp

/-! ### Uniqueness of the block decomposition, and the antighost shifts -/

/-- The joint pieces of a block index. -/
def Tsup (T : (ℤ × ℤ) × ℤ) : Submodule ℂ BRSTSpace :=
  ⨆ (j : KF × ℤ) (_ : bIdx j = T), KoszulConcrete.blockB j

section Uniq

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

include hA in
theorem eq_of_Tsup {T : (ℤ × ℤ) × ℤ} {u1 u2 : BRSTSpace} (h1 : u1 ∈ Tsup T) (h2 : u2 ∈ Tsup T)
    (h12 : u1 - u2 ∈ NTp T) : u1 = u2 := by
  refine eq_of_iproj_eq (hIB hA) fun j => ?_
  by_cases hj : bIdx j = T
  · by_cases hc : j.1.2 < 0
    · have a1 := iproj_mem (hIB hA) j u1
      have a2 := iproj_mem (hIB hA) j u2
      rw [blockB_eq_bot_of_c0 (by omega), Submodule.mem_bot] at a1 a2
      rw [a1, a2]
    · have e := iproj_eq_zero_of_mem_iSup (hIB hA) _ h12 (by
        rintro (h | h)
        · exact h hj
        · exact hc h)
      rwa [map_sub, sub_eq_zero] at e
  · rw [iproj_eq_zero_of_mem_iSup (hIB hA) _ h1 hj, iproj_eq_zero_of_mem_iSup (hIB hA) _ h2 hj]

end Uniq

theorem bAn_mem_ghostB (c : Fin 3) (kk : ℕ) (i : KF × ℤ) :
    ∀ y ∈ KoszulConcrete.ghostB i, bAn c kk y ∈
      KoszulConcrete.ghostB (i + (-modeIdxF (kk, 1), 0)) := by
  intro y hy
  unfold KoszulConcrete.ghostB at hy ⊢
  split_ifs at hy with h
  · have hb : b2 (i + (-modeIdxF (kk, 1), 0)).1 = 2 * (i + (-modeIdxF (kk, 1), 0)).2 := by
      simp only [Prod.fst_add, Prod.snd_add, map_add, map_neg, h, b2_modeIdxF_c]; ring
    rw [if_pos hb]
    have h2 := bAn_mem_ghostDegF c kk hy
    rwa [sub_eq_add_neg] at h2
  · rw [Submodule.mem_bot] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _

theorem bAnB_mem_blockB (c : Fin 3) (kk : ℕ) (j : KF × ℤ) :
    ∀ z ∈ KoszulConcrete.blockB j, TensorProduct.map LinearMap.id (bAn c kk) z ∈
      KoszulConcrete.blockB (j + (-modeIdxF (kk, 1), 0)) := by
  intro z hz
  have h := tensorDeg_map_shift KoszulConcrete.matterB KoszulConcrete.ghostB LinearMap.id
    (bAn c kk) 0 (-modeIdxF (kk, 1), 0) (fun i x hx => by rwa [add_zero])
    (bAn_mem_ghostB c kk) j z hz
  rwa [zero_add] at h

theorem bIdx_bAn {kk : ℕ} (hkk : 1 ≤ kk) (j : KF × ℤ) :
    bIdx (j + (-modeIdxF (kk, 1), 0)) = bIdx j - (shQm, 0) := by
  have hm : (modeIdxF (kk, 1)).1.1 = (1, 1) := by
    simp [modeIdxF, modeIdx, modeR, ghCharge]; omega
  simp only [bIdx, Prod.fst_add, Prod.snd_add, Prod.fst_neg, hm, add_zero, shQm]
  simp [sub_eq_add_neg]

theorem c0_bAn {kk : ℕ} (hkk : 1 ≤ kk) (j : KF × ℤ) :
    (j + (-modeIdxF (kk, 1), 0)).1.2 = j.1.2 := by
  have : (modeIdxF (kk, 1)).2 = 0 := by simp [modeIdxF]; omega
  simp [this]

theorem bAnB_Tsup (c : Fin 3) {kk : ℕ} (hkk : 1 ≤ kk) {T : (ℤ × ℤ) × ℤ} {v : BRSTSpace}
    (hv : v ∈ Tsup T) : TensorProduct.map LinearMap.id (bAn c kk) v ∈ Tsup (T - (shQm, 0)) := by
  refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.map LinearMap.id (bAn c kk) v
    ∈ Tsup (T - (shQm, 0))) hv ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.map LinearMap.id (bAn c kk) v
    ∈ Tsup (T - (shQm, 0))) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hj z hz
  exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (by rw [bIdx_bAn hkk, hj])
    (bAnB_mem_blockB c kk j z hz))

theorem bAnB_NTp (c : Fin 3) {kk : ℕ} (hkk : 1 ≤ kk) {T : (ℤ × ℤ) × ℤ} {v : BRSTSpace}
    (hv : v ∈ NTp T) : TensorProduct.map LinearMap.id (bAn c kk) v ∈ NTp (T - (shQm, 0)) := by
  refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.map LinearMap.id (bAn c kk) v
    ∈ NTp (T - (shQm, 0))) hv ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v => TensorProduct.map LinearMap.id (bAn c kk) v
    ∈ NTp (T - (shQm, 0))) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hj z hz
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ?_ (bAnB_mem_blockB c kk j z hz))
  rcases hj with h | h
  · left; rw [bIdx_bAn hkk]; intro e; exact h (by simpa using e)
  · right; rw [c0_bAn hkk]; exact h

/-! ### The antighost modes on `d_CE` -/

theorem gvac_mem_ghostB : gvac ∈ KoszulConcrete.ghostB 0 := by
  unfold KoszulConcrete.ghostB
  rw [if_pos (by simp)]
  have h0 : stWordSF [] ∈ fockDegF 0 := by
    have := stWordSF_mem_fockDegF []
    simpa [wordIdxF] using this
  have h := tmul_mem_tensorDeg pairDegF fockDegF
    (tmul_mem_tensorDeg fockDegF fockDegF h0 h0) h0
  simpa using h

theorem tmul_gvac_mem (j1 : KF × ℤ) {m : MatterSpace} (hm : m ∈ KoszulConcrete.matterB j1) :
    m ⊗ₜ[ℂ] gvac ∈ KoszulConcrete.blockB j1 := by
  have h := tmul_mem_tensorDeg KoszulConcrete.matterB KoszulConcrete.ghostB hm gvac_mem_ghostB
  rwa [add_zero] at h

theorem matterDeg_mem_matterB {i : (ℤ × ℤ) × ℂ} {m : MatterSpace} (hm : m ∈ matterDeg i) :
    m ∈ KoszulConcrete.matterB ((i, 0), 0) := by
  unfold KoszulConcrete.matterB matterF
  rw [if_pos rfl, if_pos rfl]
  exact hm

section CE

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

theorem bAnB_vac (c : Fin 3) (kk : ℕ) (m : MatterSpace) :
    TensorProduct.map LinearMap.id (bAn c kk) (m ⊗ₜ[ℂ] gvac) = 0 := by
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  have : bAn c kk gvac = 0 := gMode_gvac c 0 (Int.natCast_nonneg kk)
  rw [this, TensorProduct.tmul_zero]

theorem bAnB_Q_vac (c : Fin 3) (kk : ℕ) (m : MatterSpace) :
    TensorProduct.map LinearMap.id (bAn c kk)
        (semiInfiniteQ leeYangMatterAction.toAffineSl2Action (m ⊗ₜ[ℂ] gvac)) =
      mMode c kk m ⊗ₜ[ℂ] gvac := by
  have h := LinearMap.congr_fun (brstQ_bB c kk) (m ⊗ₜ[ℂ] gvac)
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  have hb : bB c kk = TensorProduct.map LinearMap.id (bAn c kk) := rfl
  rw [hb, bAnB_vac, map_zero, zero_add, JT_eq, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul] at h
  have hg : ghostJ c kk gvac = 0 := by
    rw [gvac_eq]
    exact (sl2GhostSVA.creation (ghostCurrent c)).2 kk (Int.natCast_nonneg kk)
  rw [hg, TensorProduct.tmul_zero, add_zero] at h
  exact h

/-- **The antighost mode `b_{(kk)}` on the `d_CE`-component**: if `z` is the
`(a + shQm, 0)`-block component of `Q (m ⊗ |0⟩)`, then `b_{(kk)} z = J^{c,(0)}_{kk} m ⊗ |0⟩`. -/
theorem bAnB_dCE (c : Fin 3) {kk : ℕ} (hkk : 1 ≤ kk) {a : ℤ × ℤ} {w : ℂ} {m : MatterSpace}
    (hm : m ∈ matterDeg (a, w)) {z : BRSTSpace} (hz : z ∈ Tsup (a + shQm, ((0 : ℕ) : ℤ)))
    (hQz : semiInfiniteQ leeYangMatterAction.toAffineSl2Action (m ⊗ₜ[ℂ] gvac) - z ∈
      NTp (a + shQm, ((0 : ℕ) : ℤ))) :
    TensorProduct.map LinearMap.id (bAn c kk) z = mPos hA c kk m ⊗ₜ[ℂ] gvac := by
  have hT : ((a + shQm, ((0 : ℕ) : ℤ)) : (ℤ × ℤ) × ℤ) - (shQm, 0) = (a, 0) := by
    simp
  refine eq_of_Tsup hA (T := (a, 0)) ?_ ?_ ?_
  · have h := bAnB_Tsup c hkk hz
    rwa [hT] at h
  · refine Submodule.mem_iSup_of_mem ((((a, w) + e0n kk), 0), 0) (Submodule.mem_iSup_of_mem ?_
      (tmul_gvac_mem _ (matterDeg_mem_matterB (mPos_mem hA c kk _ m hm))))
    simp [bIdx]
  · have h1 := bAnB_NTp c hkk hQz
    rw [hT, map_sub, bAnB_Q_vac] at h1
    have h2 : (mMode c kk m - mPos hA c kk m) ⊗ₜ[ℂ] gvac ∈ NTp (a, 0) := by
      refine Submodule.mem_iSup_of_mem ((((a, w) + emn kk), 0), 0) (Submodule.mem_iSup_of_mem ?_
        (tmul_gvac_mem _ (matterDeg_mem_matterB (mMode_sub_mPos_mem hA c kk _ m hm))))
      left
      intro e
      have := congrArg (fun x : (ℤ × ℤ) × ℤ => x.1.1) e
      simp [bIdx] at this
    have h3 := Submodule.sub_mem _ h2 h1
    rw [TensorProduct.sub_tmul] at h3
    convert h3 using 1
    abel

end CE

/-! ### The antighost-free blocks in vacuum form -/

section Blocks

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

include hA in
/-- A block vector at `(a, 0)` with `a.2 = 0` is `extM x ⊗ |0⟩`, `extM x ∈ matterDeg (a, n)`. -/
theorem blk_vacForm {n : ℤ} {a : ℤ × ℤ} (ha : a.2 = 0) (x : relativeWeight n)
    (hx : x ∈ blkE n (a, ((0 : ℕ) : ℤ))) :
    (x : BRSTSpace) = extM x ⊗ₜ[ℂ] gvac ∧ extM x ∈ matterDeg (a, (n : ℂ)) := by
  have hg := blk_mem_goodSup hA x hx
  have key : ∀ v ∈ goodSup n (a, ((0 : ℕ) : ℤ)),
      TensorProduct.map LinearMap.id Pvac v = v ∧ extM v ∈ matterDeg (a, (n : ℂ)) := by
    refine goodSup_induction _ ⟨map_zero _, by rw [map_zero]; exact Submodule.zero_mem _⟩
      (fun x y hx hy => ⟨by rw [map_add, hx.1, hy.1], by
        rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩) ?_
    intro j hb hw hc z hz
    have h1 : j.1.1.1 = a := congrArg Prod.fst hb
    have h2 : j.2 = 0 := by have := congrArg Prod.snd hb; simpa using this
    have h := vacForm_blockB h2 (by rw [h1]; exact ha) z hz
    refine ⟨h.1, ?_⟩
    have e : j.1.1 = (a, (n : ℂ)) := Prod.ext h1 hw
    rw [← e]; exact h.2
  obtain ⟨k1, k2⟩ := key _ hg
  exact ⟨by rw [← map_Pvac_eq, k1], k2⟩

include hA in
/-- A block vector at `(a, 0)` with `a.2 = 1` (one `c`). -/
theorem blk_oneC {n : ℤ} {a : ℤ × ℤ} (ha : a.2 = 1) (x : relativeWeight n)
    (hx : x ∈ blkE n (a, ((0 : ℕ) : ℤ))) :
    TensorProduct.map LinearMap.id (NT (Tc n.toNat)) (x : BRSTSpace) = x ∧
      ∀ (c : Fin 3) (kk : ℕ), 1 ≤ kk →
        TensorProduct.map LinearMap.id Pvac
            (TensorProduct.map LinearMap.id (bAn c kk) (x : BRSTSpace)) =
          TensorProduct.map LinearMap.id (bAn c kk) (x : BRSTSpace) ∧
        extM (TensorProduct.map LinearMap.id (bAn c kk) (x : BRSTSpace)) ∈
          matterDeg ((a, (n : ℂ)) - ((1, 1), (kk : ℂ))) := by
  have hg := blk_mem_goodSup hA x hx
  refine ⟨?_, fun c kk hkk => ?_⟩
  · refine goodSup_induction (fun v => TensorProduct.map LinearMap.id (NT (Tc n.toNat)) v = v)
      (map_zero _) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy]) ?_ _ hg
    intro j hb hw hc z hz
    have h1 : j.1.1.1 = a := congrArg Prod.fst hb
    have h2 : j.2 = 0 := by have := congrArg Prod.snd hb; simpa using this
    exact oneC_blockB n.toNat h2 (by rw [h1]; exact ha) hw (le_toNat n) z hz
  · refine goodSup_induction (fun v =>
      TensorProduct.map LinearMap.id Pvac (TensorProduct.map LinearMap.id (bAn c kk) v) =
          TensorProduct.map LinearMap.id (bAn c kk) v ∧
        extM (TensorProduct.map LinearMap.id (bAn c kk) v) ∈
          matterDeg ((a, (n : ℂ)) - ((1, 1), (kk : ℂ))))
      ⟨by simp, by simp⟩ (fun x y hx hy => ⟨by rw [map_add, map_add, hx.1, hy.1], by
        rw [map_add, map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩) ?_ _ hg
    intro j hb hw hc z hz
    have h1 : j.1.1.1 = a := congrArg Prod.fst hb
    have h2 : j.2 = 0 := by have := congrArg Prod.snd hb; simpa using this
    have h := bAn_blockB c hkk h2 (by rw [h1]; exact ha) z hz
    have e : j.1.1 = (a, (n : ℂ)) := Prod.ext h1 hw
    rw [e] at h
    exact h

theorem bAnB_zero_rel {n : ℤ} (c : Fin 3) (y : relativeWeight n) :
    TensorProduct.map LinearMap.id (bAn c 0) (y : BRSTSpace) = 0 := by
  have h := ((mem_relativeCarrier _ _).mp y.2.1).2 c
  rw [antighostZero_eq] at h
  exact h

theorem ev_extM_eq_ext (v : BRSTSpace) :
    ev hA (extM v) = (TensorProduct.rid ℂ (ASpace ⊗[ℂ] BSpace))
      (TensorProduct.map LinearMap.id vacφ (EVB hA v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | tmul m g => simp [extM_tmul, EVB]

theorem EVB_tmul_gvac (m : MatterSpace) : EVB hA (m ⊗ₜ[ℂ] gvac) = ev hA m ⊗ₜ[ℂ] gvac := by
  simp [EVB]

theorem eq_zero_of_tmul_gvac {w : ASpace ⊗[ℂ] BSpace} (h : w ⊗ₜ[ℂ] gvac = 0) : w = 0 := by
  have := congrArg (fun v => (TensorProduct.rid ℂ (ASpace ⊗[ℂ] BSpace))
    (TensorProduct.map LinearMap.id vacφ v)) h
  simpa [vacφ_gvac] using this

theorem eq_zero_of_tmul_gvac' {m : MatterSpace} (h : m ⊗ₜ[ℂ] gvac = 0) : m = 0 := by
  have := congrArg extM h
  simpa [extM_tmul, vacφ_gvac] using this

end Blocks

end

end VOA.KoszulResidual
