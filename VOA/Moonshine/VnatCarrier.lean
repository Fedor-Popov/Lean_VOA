/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SkewLeech
import VOA.Moonshine.PlusWeightTwo

/-!
# M8d: the carrier `V♮ = V_Λ^+ × (V_Λ^T)^+` and its `ℤ`-grading

The moonshine module's underlying space is `Vnat := VP × TP`, with `VP = V_Λ^+` the carrier of
`leechVOAPlus` (`SkewVP`) and `TP = (V_Λ^T)^+` the carrier of `Moonshine.plusModule`.  Its
grading is `gradingNat n := (V_Λ^+)_n × TP_n`, where `TP`'s `ℂ`-indexed weight grading is read at
the integer `n` (it has no other nonzero pieces: `plusModule_weight_ne_bot`).

## Main results

* `Vnat`, `gradingNat`, `vacNat = (𝟙, 0)`, `omegaNat = (ω, 0)`.
* `gradingNat_isInternal : DirectSum.IsInternal gradingNat`.
* `finiteDimensional_gradingNat`, `finrank_gradingNat` (`= dim (V_Λ^+)_n + dim TP_n`).
* `gradingNat_zero : gradingNat 0 = ℂ ∙ vacNat`, `gradingNat_neg` (`= ⊥` for `n < 0`),
  `gradingNat_one : gradingNat 1 = ⊥`.
* `finrank_gradingNat_two : finrank ℂ (gradingNat 2) = 196884` (`98580 + 98304`).
* `finrank_gradingNat_eq_coeff_JShift : (finrank ℂ (gradingNat n) : ℂ) = [qⁿ](q·J)` for all
  `n : ℕ`.
* `vacNat_mem`, `omegaNat_mem` — `(𝟙,0) ∈ V♮₀`, `(ω,0) ∈ V♮₂`.

These are the M9 numerical targets, proved at the level of the graded vector space.  They become
statements about the VOA `V♮` once its vertex operator (M8i) is built with this grading.

## Status
`sorry`-free and unconditional (no hypotheses beyond the displayed ones).
-/

namespace VOA.Moonshine

open Module

/-- **The carrier of the moonshine module**, `V♮ = V_Λ^+ × (V_Λ^T)^+`. -/
abbrev Vnat : Type := SkewVP × TP

/-- The `ℤ`-grading of `V♮`: `V♮ₙ = (V_Λ^+)ₙ × TPₙ`. -/
noncomputable def gradingNat (n : ℤ) : Submodule ℂ Vnat :=
  (leechVOAPlus.grading n).prod (plusModule.weight (n : ℂ))

theorem mem_gradingNat {n : ℤ} {x : Vnat} :
    x ∈ gradingNat n ↔ x.1 ∈ leechVOAPlus.grading n ∧ x.2 ∈ plusModule.weight (n : ℂ) :=
  Submodule.mem_prod

/-- The vacuum `(𝟙, 0)` of `V♮`. -/
noncomputable def vacNat : Vnat := (leechVOAPlus.vacuum, 0)

/-- The conformal vector `(ω, 0)` of `V♮`. -/
noncomputable def omegaNat : Vnat := (leechVOAPlus.conformalVector, 0)

theorem vacNat_mem : vacNat ∈ gradingNat 0 :=
  mem_gradingNat.2 ⟨leechVOAPlus.vacuum_mem, Submodule.zero_mem _⟩

theorem omegaNat_mem : omegaNat ∈ gradingNat 2 :=
  mem_gradingNat.2 ⟨leechVOAPlus.conformal_mem, Submodule.zero_mem _⟩

/-! ## The direct-sum decomposition -/

/-- `TP` is the sum of its integer weight spaces. -/
theorem iSup_plusModule_weight_int : ⨆ k : ℤ, plusModule.weight (k : ℂ) = ⊤ := by
  have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    plusModule.isInternal
  rw [eq_top_iff, ← h.2]
  refine iSup_le fun α => ?_
  by_cases hα : plusModule.weight α = ⊥
  · rw [hα]; exact bot_le
  · obtain ⟨n, rfl, -⟩ := plusModule_weight_ne_bot hα
    exact le_iSup (fun k : ℤ => plusModule.weight (k : ℂ)) n

theorem gradingNat_iSupIndep : iSupIndep gradingNat := by
  have hV := ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    leechVOAPlus.isInternal).1
  have hT := ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    plusModule.isInternal).1
  intro n
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ k, ⨆ (_ : k ≠ n), gradingNat k)
      ≤ (⨆ k, ⨆ (_ : k ≠ n), leechVOAPlus.grading k).prod
          (⨆ α, ⨆ (_ : α ≠ (n : ℂ)), plusModule.weight α) := by
    refine iSup_le fun k => iSup_le fun hk => ?_
    refine Submodule.prod_mono ?_ ?_
    · exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)
    · refine le_iSup_of_le (k : ℂ) (le_iSup_of_le (fun h => hk (by exact_mod_cast h)) le_rfl)
  have h2 := hle hx'
  rw [Submodule.mem_prod] at h2
  rw [mem_gradingNat] at hx
  have e1 : x.1 = 0 := (Submodule.disjoint_def.1 (hV n)) _ hx.1 h2.1
  have e2 : x.2 = 0 := (Submodule.disjoint_def.1 (hT (n : ℂ))) _ hx.2 h2.2
  exact Prod.ext e1 e2

theorem iSup_gradingNat : ⨆ n, gradingNat n = ⊤ := by
  have hV := ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    leechVOAPlus.isInternal).2
  rw [eq_top_iff]
  rintro ⟨v, t⟩ -
  have hinl : Submodule.map (LinearMap.inl ℂ SkewVP TP) (⨆ n, leechVOAPlus.grading n)
      ≤ ⨆ n, gradingNat n := by
    rw [Submodule.map_iSup]
    refine iSup_le fun n => le_iSup_of_le n ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_gradingNat.2 ⟨hy, Submodule.zero_mem _⟩
  have hinr : Submodule.map (LinearMap.inr ℂ SkewVP TP) (⨆ k : ℤ, plusModule.weight (k : ℂ))
      ≤ ⨆ n, gradingNat n := by
    rw [Submodule.map_iSup]
    refine iSup_le fun n => le_iSup_of_le n ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_gradingNat.2 ⟨Submodule.zero_mem _, hy⟩
  have h1 : ((v, 0) : Vnat) ∈ ⨆ n, gradingNat n :=
    hinl ⟨v, by rw [hV]; trivial, rfl⟩
  have h2 : ((0, t) : Vnat) ∈ ⨆ n, gradingNat n :=
    hinr ⟨t, by rw [iSup_plusModule_weight_int]; trivial, rfl⟩
  have := Submodule.add_mem _ h1 h2
  simpa using this

/-- **`V♮ = ⊕ₙ V♮ₙ`.** -/
theorem gradingNat_isInternal : DirectSum.IsInternal gradingNat :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨gradingNat_iSupIndep, iSup_gradingNat⟩

/-! ## Dimensions -/

/-- `Submodule.prod p q ≃ p × q`. -/
noncomputable def prodSubEquiv {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (p : Submodule ℂ A) (q : Submodule ℂ B) : (p.prod q) ≃ₗ[ℂ] p × q where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.1 x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.1 x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), Submodule.mem_prod.2 ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance finiteDimensional_gradingNat (n : ℤ) : FiniteDimensional ℂ (gradingNat n) := by
  haveI := leechVOAPlus.finrank n
  haveI := plusModule.finrank (n : ℂ)
  exact LinearEquiv.finiteDimensional (prodSubEquiv _ _).symm

theorem finrank_gradingNat (n : ℤ) :
    finrank ℂ (gradingNat n)
      = finrank ℂ (leechVOAPlus.grading n) + finrank ℂ (plusModule.weight (n : ℂ)) := by
  haveI := leechVOAPlus.finrank n
  haveI := plusModule.finrank (n : ℂ)
  rw [gradingNat, LinearEquiv.finrank_eq (prodSubEquiv _ _), Module.finrank_prod]

/-- `V♮ₙ = 0` for `n < 0`. -/
theorem gradingNat_neg {n : ℤ} (hn : n < 0) : gradingNat n = ⊥ := by
  rw [gradingNat, leechVOAPlus.positivity n hn,
    plusModule_weight_eq_bot_of_re_lt_two
      (by simp only [Complex.intCast_re]; exact_mod_cast (by omega : n < 2)),
    Submodule.prod_bot]

/-- **`V♮₀ = ℂ (𝟙, 0)`** (CFT type). -/
theorem gradingNat_zero : gradingNat 0 = ℂ ∙ vacNat := by
  ext ⟨v, t⟩
  rw [mem_gradingNat, Submodule.mem_span_singleton, leechVOAPlus.vacuum_grade,
    Submodule.mem_span_singleton,
    plusModule_weight_eq_bot_of_re_lt_two (by simp), Submodule.mem_bot]
  constructor
  · rintro ⟨⟨c, hc⟩, ht⟩
    exact ⟨c, by rw [vacNat, Prod.smul_mk, smul_zero, hc]; exact Prod.ext rfl ht.symm⟩
  · rintro ⟨c, hc⟩
    rw [vacNat, Prod.smul_mk, smul_zero, Prod.mk.injEq] at hc
    exact ⟨⟨c, hc.1⟩, hc.2.symm⟩

/-- **`V♮₁ = 0`**: `(V_Λ^+)₁ = 0` (`leechVOAPlus_grading_one`) and `TP` has weights `≥ 2`. -/
theorem gradingNat_one : gradingNat 1 = ⊥ := by
  rw [gradingNat, leechVOAPlus_grading_one,
    plusModule_weight_eq_bot_of_re_lt_two (by simp), Submodule.prod_bot]

/-- **`dim V♮₂ = 196884 = 98580 + 98304`** (the Griess algebra dimension). -/
theorem finrank_gradingNat_two : finrank ℂ (gradingNat 2) = 196884 := by
  rw [finrank_gradingNat, leechVOAPlus_finrank_grading_two,
    show ((2 : ℤ) : ℂ) = (2 : ℂ) by norm_num, finrank_plusModule_weight_two]

/-- **The graded dimension of `V♮` is `J`**: `dim V♮ₙ = [qⁿ](q·J(q))` for every `n ≥ 0`
(`JShift = q·J = 1 + 196884 q² + ⋯`). -/
theorem finrank_gradingNat_eq_coeff_JShift (n : ℕ) :
    (finrank ℂ (gradingNat (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift := by
  rw [finrank_gradingNat]
  exact finrank_plusModule_eq_coeff_JShift n

end VOA.Moonshine
