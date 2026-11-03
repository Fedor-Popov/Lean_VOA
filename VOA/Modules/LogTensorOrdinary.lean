/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorStructure
import VOA.Modules.LogVModule

/-!
# Logarithmic versus ordinary intertwining operators; the module vertex operator — T1

* **Embedding.**  An FHL intertwining operator (`VOA.IsIntertwiningOperator`, the notion used by
  the whole of `VOA/Huang`) is a logarithmic one with no `log` terms: `ofOrd Y` puts `Y` in log
  degree `0` (`isLogIntertwining_ofOrd`).  Conversely a logarithmic operator whose first log
  coefficient vanishes is an FHL operator in degree `0` (`isIntertwiningOperator_logZero`).
* **Among ordinary modules nothing new appears**: for `OrdVModule`s (`L₀` semisimple) every
  logarithmic intertwining operator is log-free (`log_one_eq_zero_of_ord`), and
  `ordEquiv : LogIntertwiningOperator A₁ A₂ A₃ ≃ₗ[ℂ] IntertwiningOperator A₁ A₂ A₃`.  Hence
  `logFusionRule = fusionRule` (`logFusionRule_eq_fusionRule`), and every finiteness theorem for
  FHL fusion rules in `VOA/Huang` transfers verbatim.  This is the faithfulness check of the
  HLZ definition against the library's FHL one.
* **Non-vacuity on arbitrary (weak, graded, logarithmic) modules**: the module vertex operator
  `Y_W` of any weak module `W` is a logarithmic intertwining operator of type `(W / V W)`
  (`logModuleIntertwiner`), nonzero when `W ≠ 0` (`logModuleIntertwiner_ne_zero`); in particular
  for every `C2Rigid.GWModule` (`gwModuleIntertwiner`) and `LogVModule`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogTensor

open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-! ## Log-free operators -/

/-- Put FHL mode data in log degree `0`. -/
noncomputable def ofOrd (Y : IntertwiningModes M₁ M₂ M₃) : LogModes M₁ M₂ M₃ :=
  fun n k => if k = 0 then Y n else 0

@[simp] theorem ofOrd_zero (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) : ofOrd Y n 0 = Y n := rfl

@[simp] theorem ofOrd_succ (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) (k : ℕ) :
    ofOrd Y n (k + 1) = 0 := rfl

/-- The FHL axioms (stated for weak modules) make `ofOrd Y` a logarithmic intertwining operator. -/
theorem isLogIntertwining_ofOrd_of {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (htr : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0)
    (hL : ∀ (w₁ : M₁) (n : ℂ), Y n (Lm1 A₁ w₁) = (-n) • Y (n - 1) w₁)
    (hJ : ∀ (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ),
      (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) w₁ w₂)
            - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) (m + i) w₂)))
        = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM u) (ℓ + i) w₁) w₂) :
    IsLogIntertwining A₁ A₂ A₃ (ofOrd Y) := by
  refine ⟨fun _ _ _ => ⟨1, fun k hk => ?_⟩, fun w₁ w₂ n => ?_, fun w₁ n k => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  · obtain ⟨N, hN⟩ := htr w₁ w₂ n
    refine ⟨N, fun m hm k => ?_⟩
    rcases k with _ | k
    · exact hN m hm
    · rfl
  · rcases k with _ | k
    · simp only [ofOrd_zero, ofOrd_succ, hL, LinearMap.zero_apply, smul_zero, add_zero]
    · simp
  · intro u w₁ w₂ ℓ m n k
    rcases k with _ | k
    · exact hJ u w₁ w₂ ℓ m n
    · simp

/-- **Embedding of FHL intertwining operators** (`VOA/Huang/Intertwining.lean`). -/
theorem isLogIntertwining_ofOrd {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    IsLogIntertwining A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule (ofOrd Y) :=
  isLogIntertwining_ofOrd_of hY.truncation hY.L_neg_one hY.jacobi

/-- A logarithmic operator whose first log coefficient vanishes is FHL in degree `0`. -/
theorem isIntertwiningOperator_logZero {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule Y)
    (h1 : ∀ (n : ℂ) (w₁ : M₁) (w₂ : M₂), Y n 1 w₁ w₂ = 0) :
    IsIntertwiningOperator A₁ A₂ A₃ (fun n => Y n 0) := by
  refine ⟨fun w₁ w₂ n => ?_, fun w₁ n => ?_, fun u w₁ w₂ ℓ m n => hY.jacobi u w₁ w₂ ℓ m n 0⟩
  · obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    exact ⟨N, fun k hk => hN k hk 0⟩
  · have h := hY.L_neg_one w₁ n 0
    have h1' : Y (n - 1) (0 + 1) = 0 := by
      ext w₁ w₂; exact h1 (n - 1) w₁ w₂
    rw [h1', LinearMap.zero_apply, smul_zero, add_zero] at h
    exact h

/-! ## Ordinary modules: every logarithmic operator is log-free -/

/-- On an ordinary module the generalized `L₀`-eigenspaces are the graded pieces. -/
theorem OrdVModule.maxGen_eq_weight {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) (α : ℂ) :
    (L0 A.toWeakModule).maxGenEigenspace α = A.weight α :=
  (A.toLog.weight_eq_maxGenEigenspace α).symm

/-- **Among ordinary modules every logarithmic intertwining operator is log-free**:
`Y_{n;1} = 0` (and hence `Y_{n;k} = 0` for all `k ≥ 1`). -/
theorem log_one_eq_zero_of_ord {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule Y)
    (n : ℂ) (w₁ : M₁) (w₂ : M₂) : Y n 1 w₁ w₂ = 0 := by
  -- reduce to homogeneous `w₁, w₂`
  have hw₁ : w₁ ∈ ⨆ α, A₁.weight α := by
    rw [A₁.isInternal.submodule_iSup_eq_top]; trivial
  have hw₂ : w₂ ∈ ⨆ α, A₂.weight α := by
    rw [A₂.isInternal.submodule_iSup_eq_top]; trivial
  induction hw₁ using Submodule.iSup_induction' with
  | mem α₁ x₁ hx₁ =>
    induction hw₂ using Submodule.iSup_induction' with
    | mem α₂ x₂ hx₂ =>
      refine hY.log_eq_zero_of_eigen (α₁ := α₁) (α₂ := α₂) (fun y hy => ?_)
        (A₁.L0_weight α₁ x₁ hx₁) (A₂.L0_weight α₂ x₂ hx₂) le_rfl
      rw [OrdVModule.maxGen_eq_weight] at hy
      exact A₃.L0_weight _ y hy
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- **For ordinary modules, logarithmic and FHL intertwining operators coincide**:
`LogIntertwiningOperator A₁ A₂ A₃ ≃ₗ[ℂ] IntertwiningOperator A₁ A₂ A₃`. -/
noncomputable def ordEquiv (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) :
    LogIntertwiningOperator A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule
      ≃ₗ[ℂ] IntertwiningOperator A₁ A₂ A₃ where
  toFun Y := ⟨fun n => (Y : LogModes M₁ M₂ M₃) n 0,
    isIntertwiningOperator_logZero Y.2 (log_one_eq_zero_of_ord Y.2)⟩
  invFun Y := ⟨ofOrd (Y : IntertwiningModes M₁ M₂ M₃), isLogIntertwining_ofOrd Y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Y := by
    apply Subtype.ext
    funext n k
    rcases k with _ | k
    · rfl
    · change (0 : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) = (Y : LogModes M₁ M₂ M₃) n (k + 1)
      ext w₁ w₂
      exact (Y.2.eq_zero_of_log_eq_zero n 1 (log_one_eq_zero_of_ord Y.2 n) (k + 1)
        (by omega) w₁ w₂).symm
  right_inv Y := rfl

/-- The logarithmic fusion rule among ordinary modules is the FHL fusion rule. -/
theorem logFusionRule_eq_fusionRule (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) :
    logFusionRule A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule = fusionRule A₁ A₂ A₃ :=
  (ordEquiv A₁ A₂ A₃).finrank_eq

/-- Finite-dimensionality transfers from the FHL space. -/
theorem finiteDimensional_of_ord (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) [FiniteDimensional ℂ (IntertwiningOperator A₁ A₂ A₃)] :
    FiniteDimensional ℂ (LogIntertwiningOperator A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule) :=
  LinearEquiv.finiteDimensional (ordEquiv A₁ A₂ A₃).symm

/-! ## The module vertex operator of any weak module -/

section ModuleY

variable {M : Type v₁} [AddCommGroup M] [Module ℂ M]

/-- The bilinear map `(u, x) ↦ u₍ₖ₎ x` of a weak module, `k ∈ ℤ`. -/
noncomputable def weakIntMode (A : WeakModule W M) (k : ℤ) : 𝒱 →ₗ[ℂ] M →ₗ[ℂ] M where
  toFun u := mode (A.YM u) k
  map_add' u₁ u₂ := by simp only [map_add, mode_add]
  map_smul' c u := by simp only [map_smul, mode_smul, RingHom.id_apply]

/-- The module vertex operator `Y_W` as complex-indexed mode data (zero off `ℤ`). -/
noncomputable def weakModuleModes (A : WeakModule W M) : IntertwiningModes 𝒱 M M := fun n =>
  haveI := Classical.propDecidable (∃ k : ℤ, (k : ℂ) = n)
  if h : ∃ k : ℤ, (k : ℂ) = n then weakIntMode A h.choose else 0

theorem weakModuleModes_intCast (A : WeakModule W M) (k : ℤ) :
    weakModuleModes A (k : ℂ) = weakIntMode A k := by
  have h : ∃ k' : ℤ, (k' : ℂ) = (k : ℂ) := ⟨k, rfl⟩
  rw [weakModuleModes, dif_pos h]
  have : h.choose = k := Int.cast_injective h.choose_spec
  rw [this]

theorem weakModuleModes_apply_intCast (A : WeakModule W M) (k : ℤ) (u : 𝒱) (x : M) :
    weakModuleModes A (k : ℂ) u x = mode (A.YM u) k x := by
  rw [weakModuleModes_intCast]; rfl

theorem weakModuleModes_of_not_int (A : WeakModule W M) {n : ℂ}
    (hn : ∀ k : ℤ, (k : ℂ) ≠ n) : weakModuleModes A n = 0 := by
  rw [weakModuleModes, dif_neg (not_exists.mpr hn)]

/-- The module vertex operator `Y_W` of **any** weak module is a logarithmic intertwining
operator of type `(W / V W)` (log-free). -/
theorem isLogIntertwining_module (A : WeakModule W M) :
    IsLogIntertwining (adjointModule W).toWeakModule A A (ofOrd (weakModuleModes A)) := by
  refine isLogIntertwining_ofOrd_of ?_ ?_ ?_
  · intro u x n
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      obtain ⟨N, hN⟩ := A.truncation u x
      refine ⟨N - k, fun j hj => ?_⟩
      rw [show ((k : ℂ) + (j : ℂ)) = ((k + j : ℤ) : ℂ) by push_cast; ring,
        weakModuleModes_apply_intCast]
      exact hN _ (by omega)
    · refine ⟨0, fun j _ => ?_⟩
      rw [weakModuleModes_of_not_int A (n := n + j)
        (fun k hk => hn ⟨k - j, by push_cast; rw [hk]; ring⟩)]
      rfl
  · intro u n
    have hL : Lm1 (adjointModule W).toWeakModule u = W.L (-1) u := by
      simp only [Lm1, VertexOperatorAlgebra.L_def]; rfl
    rw [hL]
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      rw [weakModuleModes_intCast, show ((k : ℂ) - 1) = ((k - 1 : ℤ) : ℂ) by push_cast; ring,
        weakModuleModes_intCast]
      ext x
      have h := act_T_covariance A u k x
      simp only [WeakModule.act_def] at h
      simpa [weakIntMode] using h
    · rw [weakModuleModes_of_not_int A (fun k hk => hn ⟨k, hk⟩),
        weakModuleModes_of_not_int A (n := n - 1)
          (fun k hk => hn ⟨k + 1, by push_cast; rw [hk]; ring⟩)]
      simp
  · intro u v x ℓ m n
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      have h := A.jacobi u v x ℓ m k
      convert h using 2
      · funext i
        rw [show ((k : ℂ) + (i : ℂ)) = ((k + i : ℤ) : ℂ) by push_cast; ring,
          show ((ℓ : ℂ) + (k : ℂ) - (i : ℂ)) = ((ℓ + k - i : ℤ) : ℂ) by push_cast; ring,
          weakModuleModes_apply_intCast, weakModuleModes_apply_intCast]
      · funext i
        rw [show ((m : ℂ) + (k : ℂ) - (i : ℂ)) = ((m + k - i : ℤ) : ℂ) by push_cast; ring,
          weakModuleModes_apply_intCast]
        rfl
    · have hz : ∀ j : ℤ, weakModuleModes A (n + j) = 0 := fun j =>
        weakModuleModes_of_not_int A (fun k hk => hn ⟨k - j, by push_cast; rw [hk]; ring⟩)
      have h2 : ∀ i : ℤ, weakModuleModes A (ℓ + n - i) = 0 := fun i => by
        rw [show (ℓ : ℂ) + n - i = n + ((ℓ - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      have h3 : ∀ i : ℤ, weakModuleModes A (m + n - i) = 0 := fun i => by
        rw [show (m : ℂ) + n - i = n + ((m - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      simp [hz, h2, h3]

/-- The module vertex operator as an element of the space of logarithmic intertwining
operators of type `(W / V W)`. -/
noncomputable def logModuleIntertwiner (A : WeakModule W M) :
    LogIntertwiningOperator (adjointModule W).toWeakModule A A :=
  ⟨ofOrd (weakModuleModes A), isLogIntertwining_module A⟩

/-- **Non-vacuity**: on a nonzero weak module, `Y_W ≠ 0` (its `(−1;0)`-mode on the vacuum is
the identity). -/
theorem logModuleIntertwiner_ne_zero (A : WeakModule W M) [Nontrivial M] :
    logModuleIntertwiner A ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have h1 : (logModuleIntertwiner A : LogModes 𝒱 M M) ((-1 : ℤ) : ℂ) 0 W.vacuum x = x := by
    change weakModuleModes A ((-1 : ℤ) : ℂ) W.vacuum x = x
    rw [weakModuleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]
  rw [h] at h1
  exact hx (by simpa using h1.symm)

instance (A : WeakModule W M) [Nontrivial M] :
    Nontrivial (LogIntertwiningOperator (adjointModule W).toWeakModule A A) :=
  ⟨⟨logModuleIntertwiner A, 0, logModuleIntertwiner_ne_zero A⟩⟩

end ModuleY

/-- **Non-vacuity on graded weak modules** (`C2Rigid.GWModule`, possibly logarithmic, e.g.
`C2Rigid.gwOfFiniteLength`): the module vertex operator is a nonzero logarithmic intertwining
operator of type `(N / V N)`. -/
noncomputable def gwModuleIntertwiner {X : Type u} [AddCommGroup X] [Module ℂ X]
    (N : C2Rigid.GWModule W X) :
    GWLogIntertwiningOperator ((adjointModule W).toGW) N N :=
  logModuleIntertwiner N.toWeakModule

theorem gwModuleIntertwiner_ne_zero {X : Type u} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (N : C2Rigid.GWModule W X) : gwModuleIntertwiner N ≠ 0 :=
  logModuleIntertwiner_ne_zero N.toWeakModule

end VOA.LogTensor
