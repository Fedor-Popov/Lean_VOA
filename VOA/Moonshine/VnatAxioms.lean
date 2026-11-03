/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatFields
import VOA.Moonshine.NondegLeech
import VOA.Moonshine.VnatAxiomsVir

/-!
# M8i preparation: every VOA axiom of `V♮` except twisted × twisted locality

On `Vnat = VP × TP` (`VP = V_Λ^+`, `TP = (V_Λ^T)^+`) take the **block vertex map** with the
genuine adjoint `W̄ = leechWbar` (`WbarLeech`, unconditional by `NondegLeech`):

`Y♮((u,t), z) = [[Y(u,z), W̄(t,z)], [W(t,z), Y^T(u,z)]]`   (DGM CMP 1996, (4.17)),

i.e. `YN := Ynat wbarL`.  This file checks, for this explicit map and **with no hypotheses**,
every axiom of `VertexOperatorAlgebra` except the locality of two twisted fields:

* VA1 grading (`YN_grading_mode`): all four blocks — `Y` by `leechVOAPlus.grading_mode`, `Y^T` by
  `mode_mem_weight`, `W` by `SkewAdjoint.wMode_mem`, `W̄` by `leechWbar_mem`;
* VA2 vacuum (`YN_vacuum`): `Y♮((𝟙,0)) = 1`;
* VA3 creation for all states (`YN_creation`);
* VA5 regularity (`YN_regularity`);
* VA4 locality for every pair **except** twisted × twisted: `YN_local_of_htt` reduces full
  locality to `htt`; the pp-, pt- and tp-blocks are proved (`YnatU_local`,
  `YnatU_YnatT_local` with `wbar_WbarComm`);
* VOA1 Virasoro with `c = 24` (`YN_virasoro`), using the general `module_virasoro`
  (`VnatAxiomsVir`) for the `TP` block and `leechVOAPlus_centralCharge`;
* VOA2 `L₀ = n` on `gradingNat n` (`YN_L0_grading`);
* VOA3 translation `Y♮(L₋₁v) = ∂Y♮(v)` for all `v` (`YN_translation`: `W.translation`,
  `module_YM_Lm1`, `leechWsk_deriv`, `leechWbar_deriv`);
* VOA4 CFT type (`gradingNat_zero`, `gradingNat_neg`).

## Packaging

* `vnatVOA htt : VertexOperatorAlgebra Vnat` and `vnat_VOA_of_htt`: given **only**
  `htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t')` — the hypothesis of
  `reconstruct_nat` for the generating family `g = id : TP → TP` — there is a VOA structure on
  `Vnat` whose vertex map **is** the block map `YN`, with vacuum `(𝟙,0)`, conformal vector `(ω,0)`,
  central charge `24` and grading `gradingNat`.
* `htt_of_span`, `vnat_VOA_of_htt_span`: `htt` may be checked on any family `g` whose **linear**
  span is `TP` (e.g. a basis), since `t ↦ YnatT leechWbar t` is linear.
* `wordSt_span_id`: for `g = id` the spanning hypothesis of `reconstruct_nat` holds, and
  `reconstruct_nat_id_eq` shows the reconstructed map is `YN` itself.

## TRAP (MonsterRoadmap, "Definition of done")

The conclusion of `vnat_VOA_of_htt` does **not** by itself distinguish `V♮` from the square-zero
extension `V_Λ^+ ⋉ TP` (`W̄ := 0`), which is also a VOA with `c = 24`, `V₁ = 0`, `dim V₂ = 196884`
and graded dimension `J`.  What is specific here is that the vertex map is built from the genuine,
nondegenerate adjoint `leechWbar` (`VnatGenuine.leechWbar_ne_zero` in the parallel file); but
simplicity of `V♮` (`moonshine_simple`) is a separate theorem and is **not** proved here.

## Status
`sorry`-free; the only hypothesis anywhere is the displayed `htt` (M8h, open on this route).  NOT done: `htt`
itself; the reduction of `htt` from a **mode**-generating family (e.g. the cyclic vectors of
`cyclic_TPframe`, or `T₀⁺`) to all of `TP` — that needs the iterate formula
`Y♮(u₍ₙ₎t) = Y♮(u)₍ₙ₎Y♮(t)` for the `W`/`W̄` blocks (or skew-symmetry of `W̄`), which the library
does not yet have; only the linear-span reduction `htt_of_span` is provided.
-/

namespace VOA.Moonshine.VnatAxioms

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction InvForm SkewAdjoint VertexOperatorAlgebra

/-! ## The genuine `W̄` as a linear map, and the block vertex map -/

/-- `t ↦ W̄(t, z)` as a linear map. -/
noncomputable def wbarL : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP) where
  toFun := leechWbar
  map_add' t s := by
    funext k
    simp only [leechWbar_coeff]
    exact leechWbarMode_add _ t s
  map_smul' c t := by
    funext k
    simp only [leechWbar_coeff, RingHom.id_apply]
    exact leechWbarMode_smul _ c t

/-- **The block vertex map of `V♮` with the genuine `W̄`.** -/
noncomputable def YN : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat) := Ynat wbarL

theorem YN_apply (x : Vnat) :
    YN x = blockF (leechVOAPlus.Y x.1) (leechWbar x.2) (leechWsk x.2) (plusModule.YM x.1) :=
  rfl

theorem mode_YN (x y : Vnat) (n : ℤ) :
    mode (YN x) n y = (mode (leechVOAPlus.Y x.1) n y.1 + mode (leechWbar x.2) n y.2,
      mode (leechWsk x.2) n y.1 + mode (plusModule.YM x.1) n y.2) := rfl

theorem YN_inl (u : SkewVP) : YN (u, 0) = YnatU u := Ynat_inl _ u

theorem YN_inr (t : TP) : YN (0, t) = YnatT leechWbar t := Ynat_inr _ t

theorem YN_eq (x : Vnat) : YN x = YnatU x.1 + YnatT leechWbar x.2 := by
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  conv_lhs => rw [hx]
  rw [map_add, YN_inl, YN_inr]

/-! ## The genuine `W̄` satisfies the `WbarComm` interface -/

theorem wbar_WbarComm : WbarComm leechWbar := by
  intro u m t n J hJ
  refine LinearMap.ext fun a => ?_
  have h := leechWbar_comm' u m t n a J hJ
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mode_leechWbar, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  rw [← PreVertexAlgebra.smul_def] at *
  exact h

/-! ## VA1: grading, all four blocks -/

/-- `W(t)₍ₙ₎φ ∈ TP_{wt t + wt φ − n − 1}`. -/
theorem leechWsk_mode_mem {k l : ℤ} {t : TP} (ht : t ∈ plusModule.weight (k : ℂ)) {φ : SkewVP}
    (hφ : φ ∈ leechVOAPlus.grading l) (n : ℤ) :
    mode (leechWsk t) n φ ∈ plusModule.weight ((k + l - n - 1 : ℤ) : ℂ) := by
  have h := wMode_mem plusModule ht hφ n
  simp only [leechWsk, mode_Wsk, wModeLin_apply]
  convert h using 2
  push_cast; ring

/-- **VA1 for `V♮`**: `x ∈ V♮ₖ`, `y ∈ V♮ₗ` ⟹ `x₍ₙ₎y ∈ V♮_{k+l−n−1}`. -/
theorem YN_grading_mode {k l : ℤ} (x : Vnat) (hx : x ∈ gradingNat k) (y : Vnat)
    (hy : y ∈ gradingNat l) (n : ℤ) : mode (YN x) n y ∈ gradingNat (k + l - n - 1) := by
  rw [mem_gradingNat] at hx hy ⊢
  rw [mode_YN]
  refine ⟨add_mem (leechVOAPlus.grading_mode _ hx.1 _ hy.1 n) ?_, add_mem ?_ ?_⟩
  · rw [mode_leechWbar]
    have h := leechWbar_mem n hx.2 hy.2
    convert h using 2
    ring
  · exact leechWsk_mode_mem hx.2 hy.1 n
  · have h := mode_mem_weight plusModule hx.1 hy.2 n
    convert h using 2
    push_cast; ring

/-! ## VA2, VA3, VA5 -/

/-- **VA2**: `Y♮((𝟙, 0), z) = 1`. -/
theorem YN_vacuum : YN vacNat = 1 := by
  have h : YN vacNat = blockF 1 0 0 1 := by
    change blockF (leechVOAPlus.Y leechVOAPlus.vacuum) (wbarL 0) (leechWskLin 0)
      (plusModule.YM leechVOAPlus.vacuum) = _
    rw [map_zero, map_zero, leechVOAPlus.vacuum_Y, plusModule.vacuum_YM]
  funext k
  rw [h, blockF_apply, FormalDist.one_apply, FormalDist.one_apply, FormalDist.one_apply]
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;> split_ifs <;> simp

/-- **VA3** (creation) for all states. -/
theorem YN_creation (x : Vnat) :
    mode (YN x) (-1) vacNat = x ∧ ∀ n : ℤ, 0 ≤ n → mode (YN x) n vacNat = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show -(-1 : ℤ) - 1 = 0 by norm_num, YN_eq]
    change YnatU x.1 0 vacNat + YnatT leechWbar x.2 0 vacNat = x
    rw [YnatU_vac_zero, YnatT_vac_zero]
    simp
  · rw [mode_apply, YN_eq]
    change YnatU x.1 (-n - 1) vacNat + YnatT leechWbar x.2 (-n - 1) vacNat = 0
    rw [YnatU_vac_neg _ _ (by omega), YnatT_vac_neg _ _ _ (by omega), add_zero]

theorem isField_add {a b : FormalDist (End ℂ Vnat)} (ha : IsField a) (hb : IsField b) :
    IsField (a + b) := by
  intro v
  obtain ⟨A, hA⟩ := ha v
  obtain ⟨B, hB⟩ := hb v
  refine ⟨min A B, fun n hn => ?_⟩
  change a n v + b n v = 0
  rw [hA n (by omega), hB n (by omega), add_zero]

theorem YN_isField (x : Vnat) : IsField (YN x) := by
  rw [YN_eq]
  exact isField_add (YnatU_isField _) (YnatT_isField leechWbar_trunc _)

/-- **VA5** (regularity). -/
theorem YN_regularity (x y : Vnat) : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YN x) n y = 0 := by
  obtain ⟨B, hB⟩ := YN_isField x y
  exact ⟨-B, fun n hn => by rw [mode_apply]; exact hB _ (by omega)⟩

/-! ## VA4: locality, modulo the twisted × twisted block -/

theorem local_add_right {a b c : FormalDist (End ℂ Vnat)} (h1 : Local a b) (h2 : Local a c) :
    Local a (b + c) :=
  Reconstruction.Local.symm (Reconstruction.Local.add_left (Reconstruction.Local.symm h1)
    (Reconstruction.Local.symm h2))

/-- **VA4 from `htt`**: the pp-, pt- and tp-blocks are proved; only twisted × twisted
locality is assumed. -/
theorem YN_local_of_htt (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t'))
    (x y : Vnat) : Local (YN x) (YN y) := by
  rw [YN_eq, YN_eq]
  refine Reconstruction.Local.add_left (local_add_right ?_ ?_) (local_add_right ?_ ?_)
  · exact YnatU_local _ _
  · exact YnatU_YnatT_local wbar_WbarComm _ _
  · exact YnatT_YnatU_local wbar_WbarComm _ _
  · exact htt _ _

theorem YnatT_add (a b : TP) :
    YnatT leechWbar (a + b) = YnatT leechWbar a + YnatT leechWbar b := by
  rw [← YN_inr, ← YN_inr, ← YN_inr, ← map_add, Prod.mk_add_mk, add_zero]

theorem YnatT_smul (c : ℂ) (a : TP) : YnatT leechWbar (c • a) = c • YnatT leechWbar a := by
  rw [← YN_inr, ← YN_inr, ← map_smul, Prod.smul_mk, smul_zero]

theorem YnatT_zero : YnatT leechWbar 0 = 0 := by
  rw [← YN_inr, show ((0 : SkewVP), (0 : TP)) = (0 : Vnat) from rfl, map_zero]

/-- Induction over a family `g` whose linear span is `TP`. -/
theorem TP_induction {κ : Type*} (g : κ → TP) (hg : Submodule.span ℂ (Set.range g) = ⊤)
    (P : TP → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a)) (hgen : ∀ i, P (g i)) (t : TP) : P t := by
  have ht : t ∈ Submodule.span ℂ (Set.range g) := by rw [hg]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hgen i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

/-- `htt` may be checked on any family whose linear span is `TP`. -/
theorem htt_of_span {κ : Type*} (g : κ → TP) (hg : Submodule.span ℂ (Set.range g) = ⊤)
    (htt : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j))) :
    ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t') := by
  have hright : ∀ i (t' : TP), Local (YnatT leechWbar (g i)) (YnatT leechWbar t') := by
    intro i
    refine TP_induction g hg _ ?_ ?_ ?_ (fun j => htt i j)
    · rw [YnatT_zero]
      exact Reconstruction.Local.symm (Reconstruction.Local.zero_left _)
    · intro a b ha hb
      rw [YnatT_add]
      exact local_add_right ha hb
    · intro c a ha
      rw [YnatT_smul]
      exact Reconstruction.Local.smulR c ha
  intro t t'
  refine TP_induction g hg (fun s => Local (YnatT leechWbar s) (YnatT leechWbar t')) ?_ ?_ ?_
    (fun i => hright i t') t
  · simp only
    rw [YnatT_zero]
    exact Reconstruction.Local.zero_left _
  · intro a b ha hb
    simp only at ha hb ⊢
    rw [YnatT_add]
    exact Reconstruction.Local.add_left ha hb
  · intro c a ha
    simp only at ha ⊢
    rw [YnatT_smul]
    exact Reconstruction.Local.symm (Reconstruction.Local.smulR c (Reconstruction.Local.symm ha))

/-! ## The conformal structure -/

theorem mode_YN_omega (k : ℤ) :
    mode (YN omegaNat) k
      = blockOp (mode (leechVOAPlus.Y leechVOAPlus.conformalVector) k) 0 0
          (mode (plusModule.YM leechVOAPlus.conformalVector) k) := by
  change mode (YN (leechVOAPlus.conformalVector, 0)) k = _
  rw [YN_inl]
  rfl

theorem blockOp_diag_lie (a a' : End ℂ SkewVP) (b b' : End ℂ TP) :
    ⁅blockOp a 0 0 b, blockOp a' 0 0 b'⁆ = blockOp ⁅a, a'⁆ 0 0 ⁅b, b'⁆ := by
  rw [Ring.lie_def, Ring.lie_def, Ring.lie_def, blockOp_mul, blockOp_mul, blockOp_sub]
  simp

/-- **VOA1 for `V♮`**: the Virasoro relations with `c = 24`. -/
theorem YN_virasoro (m n : ℤ) :
    ⁅mode (YN omegaNat) (m + 1), mode (YN omegaNat) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YN omegaNat) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * 24) • (1 : End ℂ Vnat) else 0) := by
  rw [mode_YN_omega, mode_YN_omega, mode_YN_omega, blockOp_diag_lie,
    leechVOAPlus.virasoro m n, module_virasoro plusModule.toWeakModule m n,
    leechVOAPlus_centralCharge]
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;> split_ifs <;> simp

/-- **VOA2 for `V♮`**: `L₀ = n` on `V♮ₙ`. -/
theorem YN_L0_grading {n : ℤ} (v : Vnat) (hv : v ∈ gradingNat n) :
    mode (YN omegaNat) 1 v = (n : ℂ) • v := by
  rw [mem_gradingNat] at hv
  rw [mode_YN_omega, blockOp_apply, leechVOAPlus.L0_grading _ hv.1,
    plusModule.L0_weight _ _ hv.2]
  simp only [LinearMap.zero_apply, add_zero, zero_add]
  rfl

theorem deriv_blockF {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (a : FormalDist (End ℂ V)) (c : FormalDist (M →ₗ[ℂ] V)) (d : FormalDist (V →ₗ[ℂ] M))
    (b : FormalDist (End ℂ M)) :
    deriv (blockF a c d b) = blockF (deriv a) (deriv c) (deriv d) (deriv b) := by
  funext k
  rw [deriv_apply, blockF_apply, blockF_apply, blockOp_zsmul]
  rfl

/-- **VOA3 for `V♮`**: `Y♮(L₋₁v, z) = ∂_z Y♮(v, z)` for **every** `v`. -/
theorem YN_translation (v : Vnat) : YN (mode (YN omegaNat) 0 v) = deriv (YN v) := by
  have hL : mode (leechVOAPlus.Y leechVOAPlus.conformalVector) 0 = leechVOAPlus.L (-1) := by
    rw [VertexOperatorAlgebra.L_def]; norm_num
  have hv : mode (YN omegaNat) 0 v = (leechVOAPlus.L (-1) v.1, leechLTP v.2) := by
    rw [mode_YN_omega, blockOp_apply, hL]
    simp only [LinearMap.zero_apply, add_zero, zero_add]
    rfl
  rw [hv, YN_apply, YN_apply, deriv_blockF]
  simp only
  rw [leechWbar_deriv, leechWsk_deriv, module_YM_Lm1, ← hL, leechVOAPlus.translation]

/-! ## The packaged vertex operator algebra -/

/-- **The moonshine VOA, conditional on twisted × twisted locality only.**  Its vertex map
is the block map `YN` (genuine `W̄`); everything except `htt` is proved in this file. -/
noncomputable def vnatVOA (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t')) :
    VertexOperatorAlgebra Vnat where
  grading := gradingNat
  isInternal := gradingNat_isInternal
  finrank := finiteDimensional_gradingNat
  Y := YN
  vacuum := vacNat
  vacuum_mem := vacNat_mem
  grading_mode := fun x hx y hy n => YN_grading_mode x hx y hy n
  vacuum_Y := YN_vacuum
  creation := YN_creation
  locality := YN_local_of_htt htt
  regularity := YN_regularity
  conformalVector := omegaNat
  conformal_mem := omegaNat_mem
  centralCharge := 24
  virasoro := YN_virasoro
  L0_grading := fun v hv => YN_L0_grading v hv
  translation := YN_translation
  vacuum_grade := gradingNat_zero
  positivity := fun _ hn => gradingNat_neg hn

/-- **M8i modulo M8h.**  Given **only** twisted × twisted locality `htt` of the genuine block
fields (the `reconstruct_nat` hypothesis for the generating family `g = id`), `Vnat` carries a
vertex operator algebra structure whose vertex map is the block map
`[[Y(u), W̄(t)], [W(t), Y^T(u)]]`, with vacuum `(𝟙,0)`, conformal vector `(ω,0)`, central charge
`24` and grading `gradingNat` (so `V₁ = 0`, `dim V₂ = 196884`, graded dimension `J` by
`VnatCarrier`).

**TRAP.** This conclusion alone does not imply that `V` is `V♮` rather than the square-zero
extension `V_Λ^+ ⋉ TP`, which has the same `c`, grading and graded dimension; simplicity of `V♮`
is a separate theorem (not proved). -/
theorem vnat_VOA_of_htt (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t')) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
        V.centralCharge = 24 ∧ V.grading = gradingNat :=
  ⟨vnatVOA htt, rfl, rfl, rfl, rfl, rfl⟩

/-- The same, with `htt` checked only on a family `g` whose linear span is `TP`. -/
theorem vnat_VOA_of_htt_span {κ : Type*} (g : κ → TP)
    (hg : Submodule.span ℂ (Set.range g) = ⊤)
    (htt : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j))) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
        V.centralCharge = 24 ∧ V.grading = gradingNat :=
  vnat_VOA_of_htt (htt_of_span g hg htt)

/-! ## Relation with `reconstruct_nat` for `g = id` -/

/-- For the generating family `g = id`, the spanning hypothesis of `reconstruct_nat` holds. -/
theorem wordSt_span_id :
    Submodule.span ℂ (Set.range (NonlinearConformal.wordSt (genNat leechWbar (id : TP → TP))
      vacNat)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have h1 : NonlinearConformal.wordSt (genNat leechWbar (id : TP → TP)) vacNat [Sum.inl x.1]
      = (x.1, 0) := YnatU_vac_zero x.1
  have h2 : NonlinearConformal.wordSt (genNat leechWbar (id : TP → TP)) vacNat [Sum.inr x.2]
      = (0, x.2) := YnatT_vac_zero leechWbar x.2
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  rw [hx, ← h1, ← h2]
  exact add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- For `g = id`, the vertex map produced by `reconstruct_nat` is the block map `YN`. -/
theorem reconstruct_nat_id_eq
    (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t')) :
    ∃ YA : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat), YA = YN ∧ (∀ u v : Vnat, Local (YA u) (YA v)) := by
  obtain ⟨YA, -, hL, -, -, -, hU, hT⟩ := reconstruct_nat (id : TP → TP) leechWbar_trunc
    wbar_WbarComm leechWbar_deriv htt wordSt_span_id
  refine ⟨YA, LinearMap.ext fun x => ?_, hL⟩
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  have hT' : YA (0, x.2) = YnatT leechWbar x.2 := hT x.2
  rw [hx, map_add, map_add, hU, hT', YN_inl, YN_inr]

end VOA.Moonshine.VnatAxioms
