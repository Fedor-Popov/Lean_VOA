/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzHomFinite
import VOA.Modules.LogTensorPostcompose

/-! # The genuine vacuum unit for logarithmic intertwining operators

Finite log degree and the derivative recurrence force the vacuum insertion to
be constant, with no positive logarithmic terms. Its constant coefficient is
an actual module map and determines the whole operator, since the vacuum
generates the adjoint module. This proves the unit equivalence on arbitrary
weak modules; C2 finiteness and semisimplicity are unnecessary.
-/
namespace VOA.LogTensor
open scoped BigOperators
open Pz
universe u
variable {V M R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
  {W : VertexOperatorAlgebra V}

/-- The vacuum really generates the adjoint weak module. -/
theorem generates_adjoint_vacuum :
    Generates (adjointModule W).toWeakModule {W.vacuum} := by
  intro P hP hStable
  apply top_unique
  intro v _
  have h := hStable v (-1) W.vacuum (hP (Set.mem_singleton W.vacuum))
  change W.smul v (-1) W.vacuum ∈ P at h
  rwa [W.toPreVertexAlgebra.smul_vacuum_neg_one] at h

/-- In particular the genuine tensor unit is finitely generated. -/
theorem finGen_adjoint : FinGen (adjointModule W).toWeakModule :=
  ⟨{W.vacuum},Set.finite_singleton _,generates_adjoint_vacuum⟩

variable {A : WeakModule W M} {B : WeakModule W R} {Y : LogModes V M R}

private theorem vacuum_log_recurrence
    (hY : IsLogIntertwining (adjointModule W).toWeakModule A B Y)
    (n : ℂ) (k : ℕ) (x : M) :
    (n+1) • Y n k W.vacuum x = ((k:ℂ)+1) • Y n (k+1) W.vacuum x := by
  have h := congrArg (fun F : M →ₗ[ℂ] R => F x) (hY.L_neg_one W.vacuum (n+1) k)
  have hVac : Lm1 (adjointModule W).toWeakModule W.vacuum = 0 :=
    W.toPreVertexAlgebra.smul_vacuum_zero W.conformalVector
  simp only [hVac,map_zero,LinearMap.zero_apply,LinearMap.add_apply,
    LinearMap.smul_apply,add_sub_cancel_right] at h
  calc
    (n+1) • Y n k W.vacuum x = (n+1) • Y n k W.vacuum x + 0 := by rw [add_zero]
    _ = (n+1) • Y n k W.vacuum x +
        ((-(n+1)) • Y n k W.vacuum x + ((k:ℂ)+1) • Y n (k+1) W.vacuum x) :=
      congrArg ((n+1) • Y n k W.vacuum x + ·) h
    _ = ((k:ℂ)+1) • Y n (k+1) W.vacuum x := by module

/-- Every positive logarithmic coefficient of the vacuum insertion vanishes. -/
theorem vacuum_positive_log_zero
    (hY : IsLogIntertwining (adjointModule W).toWeakModule A B Y) (k : ℕ) :
    Y (-1) (k+1) W.vacuum = 0 := by
  apply LinearMap.ext
  intro x
  have h := vacuum_log_recurrence hY (-1) k x
  norm_num only [neg_add_cancel,zero_smul] at h
  have hk : ((k:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  exact (smul_eq_zero.mp h.symm).resolve_left hk

/-- Every vacuum mode except the constant, log-free mode vanishes. The finite log
polynomial condition rules out solutions of the derivative recurrence at n≠−1. -/
theorem vacuum_mode_zero_of_ne
    (hY : IsLogIntertwining (adjointModule W).toWeakModule A B Y)
    {n : ℂ} (hn : n ≠ -1) (k : ℕ) : Y n k W.vacuum = 0 := by
  apply LinearMap.ext
  intro x
  have hn' : n+1 ≠ 0 := by intro h; apply hn; linear_combination h
  have hdown : ∀ K : ℕ, (∀ j : ℕ, K ≤ j → Y n j W.vacuum x = 0) →
      ∀ j : ℕ, Y n j W.vacuum x = 0 := by
    intro K
    induction K with
    | zero => intro h j; exact h j (Nat.zero_le j)
    | succ K ih =>
      intro h
      apply ih
      intro j hj
      by_cases hge : K+1 ≤ j
      · exact h j hge
      · have he : j = K := by omega
        subst j
        have hr := vacuum_log_recurrence hY n K x
        rw [h (K+1) le_rfl,smul_zero] at hr
        exact (smul_eq_zero.mp hr).resolve_left hn'
  obtain ⟨K,hK⟩ := hY.logFinite W.vacuum x n
  exact hdown K hK k

/-- The actual constant vacuum coefficient commutes with every weak-module mode. -/
theorem vacuum_mode_isHom
    (hY : IsLogIntertwining (adjointModule W).toWeakModule A B Y) :
    Y (-1) 0 W.vacuum ∈ moduleHomSpace A B := by
  intro u p x
  have h := hY.commutator u W.vacuum x p (-1) 0
  have hz : ∀ i : ℤ, cbz p i • Y (p+(-1)-i) 0
      (mode ((adjointModule W).YM u) i W.vacuum) x = 0 := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg p hi,zero_smul]
    · have hv : mode ((adjointModule W).YM u) i W.vacuum = 0 :=
        W.toPreVertexAlgebra.smul_vacuum_nonneg u hi
      rw [hv,map_zero,LinearMap.zero_apply,smul_zero]
  rw [finsum_congr hz,finsum_zero,sub_eq_zero] at h
  exact h.symm

/-- The vacuum constant determines the whole genuine logarithmic operator. -/
theorem eq_zero_of_vacuum_mode
    (hY : IsLogIntertwining (adjointModule W).toWeakModule A B Y)
    (h0 : Y (-1) 0 W.vacuum = 0) : Y = 0 := by
  apply hY.eq_zero_of_generates_left generates_adjoint_vacuum
  intro s hs n k x
  have hs' : s = W.vacuum := Set.mem_singleton_iff.mp hs
  subst s
  by_cases hn : n = -1
  · subst n
    cases k with
    | zero => rw [h0,LinearMap.zero_apply]
    | succ k => rw [vacuum_positive_log_zero hY k,LinearMap.zero_apply]
  · rw [vacuum_mode_zero_of_ne hY hn k,LinearMap.zero_apply]

/-- The actual linear vacuum-coefficient map from genuine intertwiners to module maps. -/
noncomputable def vacuumModeMap (A : WeakModule W M) (B : WeakModule W R) :
    LogIntertwiningOperator (adjointModule W).toWeakModule A B →ₗ[ℂ] moduleHomSpace A B where
  toFun Y := ⟨Y.1 (-1) 0 W.vacuum,vacuum_mode_isHom Y.2⟩
  map_add' Y Z := rfl
  map_smul' s Y := rfl

theorem vacuumModeMap_injective (A : WeakModule W M) (B : WeakModule W R) :
    Function.Injective (vacuumModeMap A B) := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro Y hY
  apply Subtype.ext
  exact eq_zero_of_vacuum_mode Y.2 (congrArg Subtype.val hY)

/-- The genuine module intertwiner has identity as its vacuum constant coefficient. -/
theorem logModuleIntertwiner_vacuum (A : WeakModule W M) :
    (logModuleIntertwiner A).1 (-1) 0 W.vacuum = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change ofOrd (weakModuleModes A) (-1) 0 W.vacuum x = x
  simp only [ofOrd,if_true]
  rw [show (-1:ℂ) = (((-1):ℤ):ℂ) by norm_num]
  rw [weakModuleModes_apply_intCast,A.vacuum_YM,mode_one,if_pos rfl,Module.End.one_apply]

/-- Every actual weak-module map is realized by a genuine logarithmic unit operator. -/
theorem vacuumModeMap_surjective (A : WeakModule W M) (B : WeakModule W R) :
    Function.Surjective (vacuumModeMap A B) := by
  intro f
  refine ⟨postcompose (homOfSpace f) (logModuleIntertwiner A),?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change f.1 ((logModuleIntertwiner A).1 (-1) 0 W.vacuum x) = f.1 x
  rw [logModuleIntertwiner_vacuum,LinearMap.id_apply]

/-- The genuine logarithmic vacuum-unit equivalence on arbitrary weak modules. -/
noncomputable def vacuumIntertwinerEquiv (A : WeakModule W M) (B : WeakModule W R) :
    LogIntertwiningOperator (adjointModule W).toWeakModule A B ≃ₗ[ℂ] moduleHomSpace A B :=
  LinearEquiv.ofBijective (vacuumModeMap A B)
    ⟨vacuumModeMap_injective A B,vacuumModeMap_surjective A B⟩

end VOA.LogTensor
