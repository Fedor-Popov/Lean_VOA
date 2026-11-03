/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.VnatFields
import VOA.Moonshine.NondegLeech

/-!
# M8d with the genuine adjoint `W̄`

`VnatFields` set up the generator fields of `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+` with an abstract
`Wbar`.  Here `Wbar` is instantiated with the genuine adjoint `leechWbar` of the skew intertwiner
(`WbarLeech`), whose properties are unconditional by `NondegLeech`.

## Main results (all unconditional)

* `leechWbar_WbarComm : WbarComm leechWbar`.
* `YnatU_YnatT_local_genuine : Local (YnatU u) (YnatT leechWbar t)` and the swapped order.
* `YnatT_DCovariant_genuine`, `YnatT_isField_genuine`.
* `leechWbarLin : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP)` and `YnatG := Ynat leechWbarLin`, with
  `YnatG_inl`, `YnatG_inr`.
* `reconstruct_nat_genuine`: `reconstruct_nat` with all three `W̄` hypotheses discharged;
  remaining inputs are exactly `htt` (M8h) and spanning.

## The non-TRAP certificate: the vacuum pairing

* `leechWbarMode_three_weight_two`: for `t, t' ∈ TP₂` (lowest weight),
  `W̄(t)₍₃₎ t' = TPForm(t', t) · 𝟙`.
* `leechWbar_vacuum_pairing_ne_zero`: for every nonzero `t ∈ TP₂` there is `t' ∈ TP₂` with
  `W̄(t)₍₃₎ t' ≠ 0` (indeed a nonzero multiple of `𝟙`).
* `leechWbar_ne_zero`: `leechWbar ≠ 0`.  Thus the genuine `W̄` is not the square-zero `W̄ = 0`
  of the TRAP (MonsterRoadmap, "Definition of done"); the pairing `TP₂ × TP₂ → ℂ𝟙` is the
  nondegenerate `TPForm`.
-/

namespace VOA.Moonshine

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction InvForm SkewAdjoint

/-! ## The three `W̄` hypotheses for the genuine adjoint -/

/-- **The intertwining commutator formula holds for the genuine `W̄`.** -/
theorem leechWbar_WbarComm : WbarComm leechWbar := by
  intro u m t n J hJ
  refine LinearMap.ext fun a => ?_
  have h := leechWbar_comm' u m t n a J hJ
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mode_leechWbar, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  rw [← PreVertexAlgebra.smul_def] at *
  exact h

theorem leechWbar_Trunc (t : TP) : Trunc (leechWbar t) := leechWbar_trunc t

/-- **pt-locality with the genuine `W̄`.** -/
theorem YnatU_YnatT_local_genuine (u : SkewVP) (t : TP) : Local (YnatU u) (YnatT leechWbar t) :=
  YnatU_YnatT_local leechWbar_WbarComm u t

theorem YnatT_YnatU_local_genuine (t : TP) (u : SkewVP) : Local (YnatT leechWbar t) (YnatU u) :=
  YnatT_YnatU_local leechWbar_WbarComm t u

/-- **`Tnat`-covariance of the twisted generator fields.** -/
theorem YnatT_DCovariant_genuine (t : TP) : DCovariant Tnat (YnatT leechWbar t) :=
  YnatT_DCovariant leechWbar_WbarComm leechWbar_deriv t

/-- **The twisted generator fields are fields.** -/
theorem YnatT_isField_genuine (t : TP) : IsField (YnatT leechWbar t) :=
  YnatT_isField leechWbar_Trunc t

/-! ## The block vertex map -/

/-- `t ↦ W̄(t, z)` as a linear map. -/
noncomputable def leechWbarLin : TP →ₗ[ℂ] FormalDist (TP →ₗ[ℂ] SkewVP) where
  toFun := leechWbar
  map_add' t s := by
    funext k
    simp only [leechWbar_coeff]
    exact leechWbarMode_add _ t s
  map_smul' c t := by
    funext k
    simp only [leechWbar_coeff, RingHom.id_apply]
    exact leechWbarMode_smul _ c t

@[simp] theorem leechWbarLin_apply (t : TP) : leechWbarLin t = leechWbar t := rfl

/-- **The genuine block vertex map** `Y♮(u,t) = [[Y(u), W̄(t)], [W(t), Y^T(u)]]`. -/
noncomputable def YnatG : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat) := Ynat leechWbarLin

theorem YnatG_inl (u : SkewVP) : YnatG (u, 0) = YnatU u := Ynat_inl _ u

theorem YnatG_inr (t : TP) : YnatG (0, t) = YnatT leechWbar t := Ynat_inr _ t

/-- **`reconstruct_nat` for the genuine `W̄`.**  The only remaining inputs are tt-locality of
the chosen twisted generators (M8h) and spanning of the word states. -/
theorem reconstruct_nat_genuine {κ : Type*} (g : κ → TP)
    (htt : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j)))
    (hspan : Submodule.span ℂ
      (Set.range (NonlinearConformal.wordSt (genNat leechWbar g) vacNat)) = ⊤) :
    ∃ YA : Vnat →ₗ[ℂ] FormalDist (End ℂ Vnat),
      (∀ u : Vnat, IsField (YA u)) ∧
      (∀ u v : Vnat, Local (YA u) (YA v)) ∧
      (∀ u : Vnat, (YA u) 0 vacNat = u) ∧
      (∀ u : Vnat, ∀ q : ℤ, q < 0 → (YA u) q vacNat = 0) ∧
      (∀ u : Vnat, DCovariant Tnat (YA u)) ∧
      (∀ u : SkewVP, YA (u, 0) = YnatU u) ∧
      (∀ i, YA (0, g i) = YnatT leechWbar (g i)) :=
  reconstruct_nat g leechWbar_Trunc leechWbar_WbarComm leechWbar_deriv htt hspan

/-! ## The vacuum pairing: the genuine `W̄` is nondegenerate -/

theorem plusModule_weight_one_eq_bot : plusModule.weight (1 : ℂ) = ⊥ := by
  by_contra h
  obtain ⟨n, hn, h2⟩ := plusModule_weight_ne_bot h
  have : (n : ℂ) = 1 := hn.symm
  have : n = 1 := by exact_mod_cast this
  omega

theorem Lp1_weight_two {t : TP} (ht : t ∈ plusModule.weight ((2 : ℤ) : ℂ)) :
    Lp1 plusModule t = 0 := by
  have h := Lp1_mem plusModule ht
  rw [show ((2 : ℤ) : ℂ) - 1 = 1 by norm_num, plusModule_weight_one_eq_bot] at h
  exact (Submodule.mem_bot ℂ).1 h

/-- `B_V(W̄(t)₍₃₎ t', φ) = TPForm(t', W(t)₍₋₁₎ φ)` for `t ∈ TP₂`. -/
theorem leechBV_leechWbarMode_three {t : TP} (ht : t ∈ plusModule.weight ((2 : ℤ) : ℂ))
    (a : TP) (φ : SkewVP) :
    leechBV (leechWbarMode 3 t a) φ = TPForm a (mode (leechWsk t) (-1) φ) := by
  rw [leechWbar_adj' 3 ht 1 (fun j hj => ?_) a φ]
  · simp only [Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero,
      Nat.cast_one, inv_one, Nat.cast_zero, sub_zero, smul_eq_mul]
    norm_num
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm, pow_add, pow_one, Module.End.mul_apply, Lp1_weight_two ht, map_zero]

theorem mode_leechWsk_neg_one_vacuum (t : TP) :
    mode (leechWsk t) (-1) leechVOAPlus.vacuum = t := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 by norm_num, leechWsk_vacuum, if_pos le_rfl]
  simp

/-- **The vacuum pairing**: for `t, t' ∈ TP₂`, `W̄(t)₍₃₎ t' = TPForm(t', t) · 𝟙`. -/
theorem leechWbarMode_three_weight_two {t t' : TP} (ht : t ∈ plusModule.weight ((2 : ℤ) : ℂ))
    (ht' : t' ∈ plusModule.weight ((2 : ℤ) : ℂ)) :
    leechWbarMode 3 t t' = TPForm t' t • leechVOAPlus.vacuum := by
  have hmem := leechWbar_mem 3 ht ht'
  rw [show (2 : ℤ) + 2 - 3 - 1 = 0 by norm_num, leechVOAPlus.vacuum_grade] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rw [← hc]
  congr 1
  have h := leechBV_leechWbarMode_three ht t' leechVOAPlus.vacuum
  rw [← hc, map_smul, LinearMap.smul_apply, leechBV_normalized, smul_eq_mul, mul_one,
    mode_leechWsk_neg_one_vacuum] at h
  exact h

/-- **Nondegeneracy of the genuine `W̄`** (the certificate separating it from the TRAP
`W̄ = 0`): every nonzero lowest-weight twisted state `t` has a partner `t' ∈ TP₂` with
`W̄(t)₍₃₎ t' = c · 𝟙`, `c ≠ 0`. -/
theorem leechWbar_vacuum_pairing_ne_zero {t : TP} (ht : t ∈ plusModule.weight ((2 : ℤ) : ℂ))
    (ht0 : t ≠ 0) :
    ∃ t' ∈ plusModule.weight ((2 : ℤ) : ℂ), ∃ c : ℂ, c ≠ 0 ∧
      leechWbarMode 3 t t' = c • leechVOAPlus.vacuum := by
  obtain ⟨t', ht', hne⟩ := TPForm_nondegenerate _ t ht ht0
  exact ⟨t', ht', TPForm t' t, by rwa [TPForm_symm], leechWbarMode_three_weight_two ht ht'⟩

/-- **`W̄ ≠ 0`.** -/
theorem leechWbar_ne_zero : leechWbar ≠ 0 := by
  intro h0
  have hne : plusModule.weight ((2 : ℤ) : ℂ) ≠ ⊥ := by
    intro h
    have h2 := finrank_plusModule_weight_two
    rw [show (2 : ℂ) = ((2 : ℤ) : ℂ) by norm_num, h, finrank_bot] at h2
    norm_num at h2
  obtain ⟨t, ht, ht0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨t', -, c, hc, heq⟩ := leechWbar_vacuum_pairing_ne_zero ht ht0'
  rw [← mode_leechWbar, h0] at heq
  have hz : c • leechVOAPlus.vacuum = 0 := by
    rw [← heq]; rfl
  exact hc ((smul_eq_zero.mp hz).resolve_right leechVOAPlus_vacuum_ne_zero)

end VOA.Moonshine

