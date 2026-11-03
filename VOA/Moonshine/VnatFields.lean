/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatBlock
import VOA.Moonshine.VnatCarrier
import VOA.Core.NonlinearConformal

/-!
# M8d: the generator fields of `V♮` in block form

On `Vnat = VP × TP` (`VnatCarrier`), with `VP = V_Λ^+` and `TP = (V_Λ^T)^+`, the moonshine
vertex operator is (DGM CMP 1996, eq. (4.17))

* `Y♮(u, 0) = diag(Y(u,z), Y^T(u,z))` for `u ∈ VP` (`YnatU`);
* `Y♮(0, t) = offdiag(W̄(t,z), W(t,z))` for `t ∈ TP` (`YnatT Wbar`),

with `W = leechWsk` the skew intertwiner (M8b) and `W̄` its adjoint (M8c, `WbarLeech`).
This file sets up both blocks in exactly the shape `Reconstruction.reconstruct` consumes, with
`W̄` an **abstract parameter** `Wbar : TP → FormalDist (TP →ₗ[ℂ] VP)`.

## Unconditional results (no hypothesis on anything)

* `Tnat := diag(L₋₁, L₋₁^{TP})`, `Tnat_vacNat : Tnat (𝟙,0) = 0`.
* `YnatU u := diagF (Y u) (Y^T u)`; `YnatU_isField`, `YnatU_vac_zero : (Y♮(u,0))_{z⁰}(𝟙,0)
  = (u,0)`, `YnatU_vac_neg`, `YnatU_DCovariant`, `YnatU_local : Local (YnatU u) (YnatU u')`
  (from VOA locality and module locality `VnatBlock.local_YM`).
* `YnatT_vac_zero : (Y♮(0,t))_{z⁰}(𝟙,0) = (0,t)` and `YnatT_vac_neg` — these involve only
  `W(t,z)𝟙 = e^{zL₋₁}t` (`leechWsk_vacuum`), so they hold for **every** `Wbar`.
* `leechWsk_trunc`, `leechWsk_homCov` (translation covariance of `W`).

## Results carrying explicit hypotheses on `Wbar` (each displayed in the statement)

* `YnatT_isField (hWbar : ∀ t, Trunc (Wbar t))`.
* `WbarComm Wbar` — the intertwining commutator formula for `W̄`
  (`u₍ₘ₎ W̄(t)₍ₙ₎ − W̄(t)₍ₙ₎ u₍ₘ₎ = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎`), the exact mirror of the
  proved `leechWsk_comm`.  `local_Wbar_of_comm : WbarComm Wbar → (z₁−z₂)ᴺ[Y(u), W̄(t)] = 0`.
* `YnatU_YnatT_local (hcomm : WbarComm Wbar) : Local (YnatU u) (YnatT Wbar t)` — the
  pt-locality relation (DGM (4.20)–(4.21)); the `W`-block is the proved `leechWsk_local`.
* `YnatT_DCovariant (hcomm : WbarComm Wbar) (hderiv : ∀ t, Wbar (L₋₁t) = ∂ Wbar t)`.
* `Ynat Wbar : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat)` for linear `Wbar`, with `Ynat_inl`, `Ynat_inr`.
* `reconstruct_nat` — the M8i interface: given a family `g : κ → TP` of twisted generators,
  the three `Wbar` hypotheses, **tt-locality** `∀ i j, Local (YnatT Wbar (g i)) (YnatT Wbar (g j))`
  (DGM (4.23), the M8h problem), and spanning of the word states, `reconstruct_of_generators`
  produces the all-states vertex map on `V♮` with VA3–VA5 and `Tnat`-covariance.

## Status
`sorry`-free.  Every theorem's hypotheses are displayed; the ones on `Wbar` are discharged by
M8c (`W̄` with truncation, commutator formula and `L₋₁`-property), and `reconstruct_nat`
additionally needs M8h (tt-locality) and generation.  NOT done here: the VOA structure itself
(grading compatibility of the mixed blocks, Virasoro, `Y♮(𝟙) = 1`), which is M8i.

**Caveat (non-vacuity check).**  `Wbar = 0` satisfies all three `Wbar` hypotheses, and then
tt-locality holds trivially (all products of off-diagonal blocks vanish): the square-zero
extension `VP ⋉ TP` is a genuine vertex algebra.  So these hypotheses are consistent but do not
by themselves single out `V♮`; what distinguishes `V♮` is that `W̄` is the *adjoint* of `W`
(nondegenerate), which M8c must supply, and tt-locality for that `W̄` (M8h).
-/

namespace VOA.Moonshine

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction

/-! ## Translation operator -/

/-- The translation operator `Tnat = diag(L₋₁, L₋₁^{TP})` of `V♮`. -/
noncomputable def Tnat : End ℂ Vnat := blockOp (leechVOAPlus.L (-1)) 0 0 leechLTP

theorem L_neg_one_vacuum : leechVOAPlus.L (-1) leechVOAPlus.vacuum = 0 := by
  rw [VertexOperatorAlgebra.L_def, show (-1 : ℤ) + 1 = 0 by norm_num]
  exact (leechVOAPlus.creation _).2 0 le_rfl

theorem Tnat_vacNat : Tnat vacNat = 0 := by
  rw [Tnat, vacNat, blockOp_apply, L_neg_one_vacuum]
  simp

/-! ## Truncation of the building blocks -/

theorem trunc_Y (u : SkewVP) : Trunc (leechVOAPlus.Y u) := by
  intro x
  obtain ⟨N, hN⟩ := leechVOAPlus.regularity u x
  refine ⟨-N, fun n hn => ?_⟩
  have := hN (-n - 1) (by omega)
  rwa [mode_apply, show -(-n - 1) - 1 = n by ring] at this

theorem trunc_YM (u : SkewVP) : Trunc (plusModule.YM u) := by
  intro x
  obtain ⟨N, hN⟩ := plusModule.truncation u x
  refine ⟨-N, fun n hn => ?_⟩
  have := hN (-n - 1) (by omega)
  rwa [mode_apply, show -(-n - 1) - 1 = n by ring] at this

/-- `W(t,z)` is lower-truncated on every `φ ∈ VP`. -/
theorem leechWsk_trunc (t : TP) : Trunc (leechWsk t) := by
  intro φ
  obtain ⟨N, hN⟩ := wMode_truncation plusModule.toWeakModule t φ
  exact ⟨-N, fun n hn => hN (-n - 1) (by omega)⟩

/-- **Translation covariance of `W`**: `L₋₁^{TP} W(t)ₘ − W(t)ₘ L₋₁ = (m+1) W(t)ₘ₊₁`. -/
theorem leechWsk_homCov (t : TP) : HomCov (leechVOAPlus.L (-1)) leechLTP (leechWsk t) :=
  homCov_Wsk plusModule.toWeakModule t

/-! ## The untwisted generators `Y♮(u, 0) = diag(Y(u), Y^T(u))` -/

/-- **The block field of an untwisted state**: `Y♮((u,0), z) = diag(Y(u,z), Y^T(u,z))`. -/
noncomputable def YnatU (u : SkewVP) : FormalDist (End ℂ Vnat) :=
  diagF (leechVOAPlus.Y u) (plusModule.YM u)

theorem YnatU_isField (u : SkewVP) : IsField (YnatU u) :=
  isField_blockF (trunc_Y u) trunc_zero trunc_zero (trunc_YM u)

/-- Creation: the `z⁰`-coefficient of `Y♮((u,0),z)` on the vacuum is `(u, 0)`. -/
theorem YnatU_vac_zero (u : SkewVP) : YnatU u 0 vacNat = (u, 0) := by
  have h := (leechVOAPlus.creation u).1
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 by norm_num] at h
  rw [YnatU, diagF, blockF_apply, blockOp_apply, vacNat]
  simp [h]

theorem YnatU_vac_neg (u : SkewVP) (q : ℤ) (hq : q < 0) : YnatU u q vacNat = 0 := by
  have h := (leechVOAPlus.creation u).2 (-q - 1) (by omega)
  rw [mode_apply, show -(-q - 1) - 1 = q by ring] at h
  rw [YnatU, diagF, blockF_apply, blockOp_apply, vacNat]
  simp [h]

theorem YnatU_DCovariant (u : SkewVP) : DCovariant Tnat (YnatU u) :=
  dCovariant_blockF (dCovariant_Y u) (homCov_zero _ _) (homCov_zero _ _)
    (dCovariant_YM plusModule.toWeakModule u)

/-- **pp-locality** (DGM (4.18)–(4.19)): `Y♮((u,0),z₁)` and `Y♮((u',0),z₂)` are local. -/
theorem YnatU_local (u u' : SkewVP) : Local (YnatU u) (YnatU u') :=
  local_diag_diag (leechVOAPlus.locality u u') (local_YM plusModule.toWeakModule u u')

/-! ## The twisted generators `Y♮(0, t) = offdiag(W̄(t), W(t))`, `W̄` abstract -/

/-- **The block field of a twisted state**, parametric in the (future) adjoint intertwiner
`Wbar : TP → Hom(TP, VP)⟦z^±⟧`: `Y♮((0,t), z) = offdiag(W̄(t,z), W(t,z))`. -/
noncomputable def YnatT (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t : TP) :
    FormalDist (End ℂ Vnat) :=
  offF (Wbar t) (leechWsk t)

/-- Creation for twisted states holds for every `Wbar`: `(Y♮((0,t)))_{z⁰}(𝟙,0) = (0, t)`. -/
theorem YnatT_vac_zero (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t : TP) :
    YnatT Wbar t 0 vacNat = (0, t) := by
  rw [YnatT, offF, blockF_apply, blockOp_apply, vacNat, leechWsk_vacuum, if_pos le_rfl]
  simp

theorem YnatT_vac_neg (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (t : TP) (q : ℤ) (hq : q < 0) :
    YnatT Wbar t q vacNat = 0 := by
  rw [YnatT, offF, blockF_apply, blockOp_apply, vacNat, leechWsk_vacuum, if_neg (by omega)]
  simp

/-- `Y♮((0,t))` is a field, **given** that `W̄(t)` is lower-truncated. -/
theorem YnatT_isField {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hWbar : ∀ t, Trunc (Wbar t))
    (t : TP) : IsField (YnatT Wbar t) :=
  isField_blockF trunc_zero (hWbar t) (leechWsk_trunc t) trunc_zero

/-- **The intertwining commutator formula for `W̄`** (type `(VP; TP, TP)`), the hypothesis M8c
must discharge — the exact mirror of the proved `leechWsk_comm`: for `J` past the truncation of
`u` on `t`, `u₍ₘ₎ W̄(t)₍ₙ₎ − W̄(t)₍ₙ₎ u₍ₘ₎ = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎`. -/
def WbarComm (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) : Prop :=
  ∀ (u : SkewVP) (m : ℤ) (t : TP) (n : ℤ) (J : ℕ),
    (∀ j : ℕ, J ≤ j → mode (plusModule.YM u) j t = 0) →
    mode (leechVOAPlus.Y u) m ∘ₗ mode (Wbar t) n - mode (Wbar t) n ∘ₗ mode (plusModule.YM u) m
      = ∑ r ∈ Finset.range J, gBinom m r • mode (Wbar (mode (plusModule.YM u) r t)) (m + n - r)

/-- The commutator formula makes `[Y(u,z₁), W̄(t,z₂)]` a finite sum of jump distributions. -/
theorem Wbar_bracket_eq_sum {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (u : SkewVP) (t : TP) (J : ℕ) (hJ : ∀ j : ℕ, J ≤ j → mode (plusModule.YM u) j t = 0) :
    ((fun a b => leechVOAPlus.Y u a ∘ₗ Wbar t b - Wbar t b ∘ₗ plusModule.YM u a) :
        FormalDist₂ (TP →ₗ[ℂ] SkewVP))
      = ∑ r ∈ Finset.range J,
          jumpDist r (fun k => Wbar (mode (plusModule.YM u) r t) (k + r + 1)) := by
  refine FormalDist₂.ext fun a b => ?_
  rw [fd2_finset_sum_apply]
  have hc := hcomm u (-a - 1) t (-b - 1) J hJ
  simp only [mode_apply, show -(-a - 1) - 1 = a by ring, show -(-b - 1) - 1 = b by ring] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [jumpDist, show -(-a - 1 + (-b - 1) - (r : ℤ)) - 1 = a + b + r + 1 by ring]
  rfl

/-- **Locality of `Y(u)` with `W̄(t)`**, from the commutator formula. -/
theorem local_Wbar_of_comm {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (u : SkewVP) (t : TP) :
    ∃ N : ℕ, mulBySubPow N
      ((fun a b => leechVOAPlus.Y u a ∘ₗ Wbar t b - Wbar t b ∘ₗ plusModule.YM u a) :
        FormalDist₂ (TP →ₗ[ℂ] SkewVP)) = 0 := by
  obtain ⟨N, hN⟩ := plusModule.truncation u t
  refine ⟨N.toNat, ?_⟩
  rw [Wbar_bracket_eq_sum hcomm u t N.toNat (fun j hj => hN _ (by omega)), map_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_range] at hr
  exact mulBySubPow_eq_zero_of_le (by omega : r + 1 ≤ N.toNat) (mulBySubPow_jumpDist r _)

/-- **pt-locality** (DGM (4.20)–(4.21)), conditional on `WbarComm Wbar`: `Y♮((u,0),z₁)` and
`Y♮((0,t),z₂)` are local.  The `W`-block is the proved `leechWsk_local`; the `W̄`-block is
`local_Wbar_of_comm`. -/
theorem YnatU_YnatT_local {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (u : SkewVP) (t : TP) : Local (YnatU u) (YnatT Wbar t) :=
  local_diag_off (local_Wbar_of_comm hcomm u t) (leechWsk_local u t)

/-- pt-locality in the other order. -/
theorem YnatT_YnatU_local {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (t : TP) (u : SkewVP) : Local (YnatT Wbar t) (YnatU u) :=
  Local.symm (YnatU_YnatT_local hcomm u t)

/-- Translation covariance of `W̄`, from its commutator formula at `u = ω`, `m = 0` and the
`L₋₁`-derivative property `W̄(L₋₁t, z) = ∂_z W̄(t, z)`. -/
theorem Wbar_homCov {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (hderiv : ∀ t, Wbar (leechLTP t) = deriv (Wbar t)) (t : TP) :
    HomCov leechLTP (leechVOAPlus.L (-1)) (Wbar t) := by
  intro m
  obtain ⟨J0, hJ0⟩ := plusModule.truncation leechVOAPlus.conformalVector t
  have hc := hcomm leechVOAPlus.conformalVector 0 t (-m - 1) (J0.toNat + 1)
    (fun j hj => hJ0 _ (by omega))
  rw [Finset.sum_eq_single 0 (fun r _ hr => by rw [gBinom_zero_left hr, zero_smul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos _)) h)] at hc
  rw [gBinom_zero, one_smul, Nat.cast_zero, sub_zero, zero_add] at hc
  have hL : mode (plusModule.YM leechVOAPlus.conformalVector) 0 t = leechLTP t := rfl
  have hL' : mode (plusModule.YM leechVOAPlus.conformalVector) 0 = leechLTP := rfl
  have hV : mode (leechVOAPlus.Y leechVOAPlus.conformalVector) 0 = leechVOAPlus.L (-1) := by
    rw [VertexOperatorAlgebra.L_def]; norm_num
  rw [hL, hL', hV, hderiv] at hc
  simp only [mode_apply, show -(-m - 1) - 1 = m by ring] at hc
  rw [hc, deriv_apply]

/-- `Y♮((0,t))` is `Tnat`-covariant, **given** the commutator formula and the derivative
property of `W̄`. -/
theorem YnatT_DCovariant {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (hcomm : WbarComm Wbar)
    (hderiv : ∀ t, Wbar (leechLTP t) = deriv (Wbar t)) (t : TP) :
    DCovariant Tnat (YnatT Wbar t) :=
  dCovariant_blockF DCovariant.zero (Wbar_homCov hcomm hderiv t) (leechWsk_homCov t)
    DCovariant.zero

/-! ## The block vertex map on all of `V♮` (for linear `Wbar`) -/

/-- `t ↦ W(t, z)` is linear. -/
noncomputable def leechWskLin : TP →ₗ[ℂ] FormalDist (SkewVP →ₗ[ℂ] TP) where
  toFun := leechWsk
  map_add' t s := by
    refine FormalDist.ext fun k => LinearMap.ext fun φ => ?_
    exact wMode_add_right plusModule.toWeakModule t s (-k - 1) φ
  map_smul' c t := by
    refine FormalDist.ext fun k => LinearMap.ext fun φ => ?_
    exact wMode_smul_right plusModule.toWeakModule c t (-k - 1) φ

/-- The block field as a linear map in its four blocks. -/
theorem blockF_add {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (a a' : FormalDist (End ℂ V)) (c c' : FormalDist (M →ₗ[ℂ] V))
    (d d' : FormalDist (V →ₗ[ℂ] M)) (b b' : FormalDist (End ℂ M)) :
    blockF (a + a') (c + c') (d + d') (b + b') = blockF a c d b + blockF a' c' d' b' :=
  FormalDist.ext fun _ => (blockOp_add _ _ _ _ _ _ _ _).symm

theorem blockF_smul {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (r : ℂ) (a : FormalDist (End ℂ V)) (c : FormalDist (M →ₗ[ℂ] V))
    (d : FormalDist (V →ₗ[ℂ] M)) (b : FormalDist (End ℂ M)) :
    blockF (r • a) (r • c) (r • d) (r • b) = r • blockF a c d b :=
  FormalDist.ext fun _ => (blockOp_smul _ _ _ _ _).symm

/-- **The block vertex map** `Y♮(u, t) = [[Y(u), W̄(t)], [W(t), Y^T(u)]]` of DGM (4.17), for a
linear `W̄`.  (`reconstruct` will in the end produce the vertex map; this one is the naive block
form, which agrees with it on generators.) -/
noncomputable def Ynat (Wbar : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP)) :
    Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat) where
  toFun x := blockF (leechVOAPlus.Y x.1) (Wbar x.2) (leechWskLin x.2) (plusModule.YM x.1)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    exact blockF_add _ _ _ _ _ _ _ _
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    exact blockF_smul _ _ _ _ _

theorem Ynat_inl (Wbar : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP)) (u : SkewVP) :
    Ynat Wbar (u, 0) = YnatU u := by
  change blockF _ (Wbar 0) (leechWskLin 0) _ = _
  rw [map_zero, map_zero]; rfl

theorem Ynat_inr (Wbar : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP)) (t : TP) :
    Ynat Wbar (0, t) = YnatT Wbar t := by
  change blockF (leechVOAPlus.Y 0) _ _ (plusModule.YM 0) = _
  rw [map_zero, map_zero]; rfl

/-! ## The M8i interface -/

/-- The generating family of `V♮`: all untwisted states, and a family `g` of twisted ones. -/
noncomputable def genNat {κ : Type*} (Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)) (g : κ → TP) :
    SkewVP ⊕ κ → FormalDist (End ℂ Vnat) :=
  Sum.elim YnatU (fun i => YnatT Wbar (g i))

/-- **The reconstruction interface for `V♮`** (M8i, conditional).  Given

* the three properties of `W̄` that M8c must supply (`hWbar` truncation, `hcomm` the
  intertwining commutator formula, `hderiv` the `L₋₁`-property),
* **tt-locality** `htt` of the chosen twisted generators `g` (DGM (4.23): the M8h problem), and
* `hspan`: the word states of the generators span `V♮`,

the reconstruction theorem yields a linear all-states vertex map `YA` on `V♮` that agrees with
the block fields on all words, and satisfies VA3 (creation), VA4 (locality), VA5 (regularity)
and `Tnat`-covariance.  Every other input (pp- and pt-locality, creation, `IsField`,
`DCovariant`, `Tnat (𝟙,0) = 0`) is proved above. -/
theorem reconstruct_nat {κ : Type*} {Wbar : TP → FormalDist (TP →ₗ[ℂ] SkewVP)} (g : κ → TP)
    (hWbar : ∀ t, Trunc (Wbar t)) (hcomm : WbarComm Wbar)
    (hderiv : ∀ t, Wbar (leechLTP t) = deriv (Wbar t))
    (htt : ∀ i j, Local (YnatT Wbar (g i)) (YnatT Wbar (g j)))
    (hspan : Submodule.span ℂ (Set.range (NonlinearConformal.wordSt (genNat Wbar g) vacNat))
      = ⊤) :
    ∃ YA : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat),
      (∀ u : Vnat, IsField (YA u)) ∧
      (∀ u v : Vnat, Local (YA u) (YA v)) ∧
      (∀ u : Vnat, (YA u) 0 vacNat = u) ∧
      (∀ u : Vnat, ∀ q : ℤ, q < 0 → (YA u) q vacNat = 0) ∧
      (∀ u : Vnat, DCovariant Tnat (YA u)) ∧
      (∀ u : SkewVP, YA (u, 0) = YnatU u) ∧
      (∀ i, YA (0, g i) = YnatT Wbar (g i)) := by
  have hgen : ∀ i, IsField (genNat Wbar g i) := by
    rintro (u | i)
    · exact YnatU_isField u
    · exact YnatT_isField hWbar (g i)
  obtain ⟨YA, hword, hF, hL, hC, hN, hD⟩ := NonlinearConformal.reconstruct_of_generators vacNat
    Tnat (genNat Wbar g) hgen
    (by
      rintro (u | i) (u' | j)
      · exact YnatU_local u u'
      · exact YnatU_YnatT_local hcomm u (g j)
      · exact YnatT_YnatU_local hcomm (g i) u'
      · exact htt i j)
    (by
      rintro (u | i) q hq
      · exact YnatU_vac_neg u q hq
      · exact YnatT_vac_neg Wbar (g i) q hq)
    Tnat_vacNat
    (by
      rintro (u | i)
      · exact YnatU_DCovariant u
      · exact YnatT_DCovariant hcomm hderiv (g i))
    hspan
  -- one-letter words recover the generator fields
  have hone : ∀ x, YA (NonlinearConformal.wordSt (genNat Wbar g) vacNat [x])
      = NonlinearConformal.wordFld (genNat Wbar g) hgen [x] := fun x => hword [x]
  have hfld : ∀ x, NonlinearConformal.wordFld (genNat Wbar g) hgen [x] = genNat Wbar g x := by
    intro x
    change (Fld.nprod ⟨genNat Wbar g x, hgen x⟩ Fld.one).1 = _
    rw [Fld.nprod_val]
    exact nprod_idField (hgen x)
  refine ⟨YA, hF, hL, hC, hN, hD, fun u => ?_, fun i => ?_⟩
  · have h := hone (Sum.inl u)
    rw [hfld] at h
    have hs : NonlinearConformal.wordSt (genNat Wbar g) vacNat [Sum.inl u] = (u, 0) :=
      YnatU_vac_zero u
    rwa [hs] at h
  · have h := hone (Sum.inr i)
    rw [hfld] at h
    have hs : NonlinearConformal.wordSt (genNat Wbar g) vacNat [Sum.inr i] = (0, g i) :=
      YnatT_vac_zero Wbar (g i)
    rwa [hs] at h

end VOA.Moonshine
