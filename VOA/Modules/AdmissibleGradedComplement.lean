/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.AdmissibleModule
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Weak complements give level-graded complements

`AdmissiblyRational` (`Modules/AdmissibleModule.lean`) asks that every **weak** submodule of an admissible module
have a weak complement. The category-internal reading of Dong–Li–Mason instead asks that every **level-graded**
submodule have a **level-graded** complement. `Modules/AdmissibleRationality.lean` recorded the relation between
the two readings as unsettled, and noted that an earlier sketch ("take the graded part of the weak complement")
was not a valid argument.

This file proves the direction needed to apply the graded reading to a hypothesis `AdmissiblyRational W`:

* `AdmissibleModule.levProj k`: the projection `M → M(k)` of the level decomposition;
* `AdmissibleModule.IsLevelGraded P`: `P` is stable under every `levProj k`;
* `AdmissibleModule.levProj_act`: `pr_{k+s} ∘ a₍ₚ₎ = a₍ₚ₎ ∘ pr_k` for `a ∈ 𝒱_w`, `s = w − p − 1`;
* `AdmissibleModule.exists_isLevelGraded_compl`: in a completely reducible admissible module, every level-graded
  weak submodule has a level-graded weak complement;
* `admissiblyRationalGraded_of_admissiblyRational`: `AdmissiblyRational W → AdmissiblyRationalGraded W`.

**The argument** (the release auditor's sketch, checked). Let `π` be the projection onto `P` along a weak
complement `Q`; it commutes with every mode. Its *block-diagonal part* `π₀ := Σ_k pr_k ∘ π ∘ pr_k` still commutes
with every mode, since a homogeneous mode shifts the level by a fixed amount. Because `P` is graded, `π₀` maps
into `P` and is the identity on `P`, so `ker π₀` is a complement of `P`. It is mode-stable and graded. The point
is to take the diagonal part of the **projector**, not the graded part of the **complement**.
-/

namespace VOA

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace AdmissibleModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

open DirectSum

/-- The level decomposition, as a `DirectSum.Decomposition` (a choice, since `isInternal` is a `Prop`). -/
@[reducible] noncomputable def levDecomp (N : AdmissibleModule W M) : DirectSum.Decomposition N.lev :=
  N.isInternal.chooseDecomposition

/-- The projection `M → M(k)` of the level decomposition, as an endomorphism of `M`. -/
noncomputable def levProj (N : AdmissibleModule W M) (k : ℤ) : M →ₗ[ℂ] M :=
  letI := N.levDecomp
  (N.lev k).subtype ∘ₗ (DirectSum.component ℂ ℤ (fun i => N.lev i) k) ∘ₗ
    (DirectSum.decomposeLinearEquiv N.lev).toLinearMap

theorem levProj_apply (N : AdmissibleModule W M) (k : ℤ) (x : M) :
    N.levProj k x = (letI := N.levDecomp; (DirectSum.decompose N.lev x k : M)) := rfl

theorem levProj_of_mem_same (N : AdmissibleModule W M) {k : ℤ} {x : M} (hx : x ∈ N.lev k) :
    N.levProj k x = x := by
  letI := N.levDecomp
  rw [levProj_apply]
  exact DirectSum.decompose_of_mem_same N.lev hx

theorem levProj_of_mem_ne (N : AdmissibleModule W M) {j k : ℤ} {x : M} (hx : x ∈ N.lev j)
    (hjk : j ≠ k) : N.levProj k x = 0 := by
  letI := N.levDecomp
  rw [levProj_apply]
  exact DirectSum.decompose_of_mem_ne N.lev hx hjk

theorem levProj_mem (N : AdmissibleModule W M) (k : ℤ) (x : M) : N.levProj k x ∈ N.lev k := by
  letI := N.levDecomp
  rw [levProj_apply]
  exact (DirectSum.decompose N.lev x k).2

/-- A vector all of whose level components vanish is zero. -/
theorem eq_zero_of_levProj (N : AdmissibleModule W M) {y : M} (hy : ∀ k, N.levProj k y = 0) :
    y = 0 := by
  letI := N.levDecomp
  have h : DirectSum.decompose N.lev y = 0 := by
    ext k
    have := hy k
    rw [levProj_apply] at this
    simpa using this
  have := congrArg (DirectSum.decompose N.lev).symm h
  simpa using this

/-- Induction over the level decomposition: a linear statement holding on every level holds everywhere. -/
theorem lev_induction (N : AdmissibleModule W M) {p : M → Prop} (x : M)
    (hlev : ∀ k, ∀ y ∈ N.lev k, p y) (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) : p x := by
  have hx : x ∈ ⨆ k, N.lev k := by rw [N.lev_iSup_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem k y hy => exact hlev k y hy
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz

/-- **Modes intertwine the level projections**: for `a ∈ 𝒱_w`, `pr_{k+(w−p−1)} ∘ a₍ₚ₎ = a₍ₚ₎ ∘ pr_k`. -/
theorem levProj_act (N : AdmissibleModule W M) {w : ℤ} {a : 𝒱} (ha : a ∈ W.grading w) (p k : ℤ)
    (y : M) :
    N.levProj (k + (w - p - 1)) (N.toWeakModule.act a p y) =
      N.toWeakModule.act a p (N.levProj k y) := by
  refine N.lev_induction (p := fun y => N.levProj (k + (w - p - 1)) (N.toWeakModule.act a p y) =
      N.toWeakModule.act a p (N.levProj k y)) y ?_ ?_ ?_
  · intro j z hz
    have hmem : N.toWeakModule.act a p z ∈ N.lev (j + (w - p - 1)) := N.act_lev' ha hz
    by_cases hjk : j = k
    · subst hjk
      rw [N.levProj_of_mem_same hmem, N.levProj_of_mem_same hz]
    · rw [N.levProj_of_mem_ne hmem (by omega), N.levProj_of_mem_ne hz hjk]
      simp [WeakModule.act]
  · simp [WeakModule.act]
  · intro y z hy hz
    simp only [WeakModule.act, map_add] at hy hz ⊢
    rw [hy, hz]

/-- A weak submodule is **level-graded** when it is stable under every level projection. -/
def IsLevelGraded (N : AdmissibleModule W M) (P : WeakModule.Submodule' N.toWeakModule) : Prop :=
  ∀ k : ℤ, ∀ x ∈ P.carrier, N.levProj k x ∈ P.carrier

/-- The block-diagonal part `Σ_k pr_k ∘ f ∘ pr_k` of an endomorphism `f`. -/
noncomputable def diag (N : AdmissibleModule W M) (f : M →ₗ[ℂ] M) : M →ₗ[ℂ] M :=
  letI := N.levDecomp
  (DirectSum.toModule ℂ ℤ M fun k => N.levProj k ∘ₗ f ∘ₗ (N.lev k).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv N.lev).toLinearMap

theorem diag_of_mem (N : AdmissibleModule W M) (f : M →ₗ[ℂ] M) {k : ℤ} {x : M} (hx : x ∈ N.lev k) :
    N.diag f x = N.levProj k (f x) := by
  letI := N.levDecomp
  simp only [diag, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem N.lev hx]
  erw [DirectSum.toModule_lof]
  rfl

/-- `diag f` commutes with the level projections. -/
theorem levProj_diag (N : AdmissibleModule W M) (f : M →ₗ[ℂ] M) (k : ℤ) (x : M) :
    N.levProj k (N.diag f x) = N.diag f (N.levProj k x) := by
  refine N.lev_induction (p := fun x => N.levProj k (N.diag f x) = N.diag f (N.levProj k x)) x
    ?_ (by simp) (fun y z hy hz => by simp only [map_add, hy, hz])
  intro j y hy
  rw [N.diag_of_mem f hy]
  by_cases hjk : j = k
  · subst hjk
    rw [N.levProj_of_mem_same (N.levProj_mem j _), N.levProj_of_mem_same hy, N.diag_of_mem f hy]
  · rw [N.levProj_of_mem_ne (N.levProj_mem j _) hjk, N.levProj_of_mem_ne hy hjk, map_zero]

/-- If `f` commutes with every mode then so does `diag f`. -/
theorem diag_act (N : AdmissibleModule W M) (f : M →ₗ[ℂ] M)
    (hf : ∀ (a : 𝒱) (n : ℤ) (x : M), f (N.toWeakModule.act a n x) = N.toWeakModule.act a n (f x))
    (a : 𝒱) (n : ℤ) (x : M) :
    N.diag f (N.toWeakModule.act a n x) = N.toWeakModule.act a n (N.diag f x) := by
  -- reduce to homogeneous `a`
  have ha : a ∈ ⨆ w, W.grading w := by rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction ha using Submodule.iSup_induction' with
  | zero => simp only [WeakModule.act_def, map_zero, mode_zero, LinearMap.zero_apply]
  | add a b _ _ iha ihb =>
    rw [WeakModule.act_add_left, WeakModule.act_add_left, map_add, iha, ihb]
  | mem w a ha =>
    refine N.lev_induction (p := fun x => N.diag f (N.toWeakModule.act a n x) =
        N.toWeakModule.act a n (N.diag f x)) x ?_ (by simp [WeakModule.act])
      (fun y z hy hz => by simp only [WeakModule.act, map_add] at hy hz ⊢; rw [hy, hz])
    intro k y hy
    rw [N.diag_of_mem f (N.act_lev' ha hy), N.diag_of_mem f hy, hf, N.levProj_act ha]

/-- **Graded complements.** In a completely reducible admissible module, every level-graded weak submodule
has a level-graded weak complement. -/
theorem exists_isLevelGraded_compl (N : AdmissibleModule W M) (hN : N.IsCompletelyReducible)
    (P : WeakModule.Submodule' N.toWeakModule) (hP : N.IsLevelGraded P) :
    ∃ Q : WeakModule.Submodule' N.toWeakModule, N.IsLevelGraded Q ∧ IsCompl P.carrier Q.carrier := by
  obtain ⟨Q, hPQ⟩ := hN P
  -- the projection onto `P` along `Q`, as an endomorphism of `M`
  set π : M →ₗ[ℂ] M := P.carrier.subtype ∘ₗ P.carrier.projectionOnto Q.carrier hPQ with hπ
  have hπP : ∀ x ∈ P.carrier, π x = x := fun x hx =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hPQ ⟨x, hx⟩)
  have hπQ : ∀ x ∈ Q.carrier, π x = 0 := fun x hx => by
    show ((P.carrier.projectionOnto Q.carrier hPQ x : P.carrier) : M) = 0
    have h0 := Submodule.projectionOnto_apply_right hPQ ⟨x, hx⟩
    rw [show (x : M) = ((⟨x, hx⟩ : Q.carrier) : M) from rfl, h0]
    rfl
  have hπmem : ∀ x, π x ∈ P.carrier := fun x => by simp [hπ]
  have hπact : ∀ (a : 𝒱) (n : ℤ) (x : M),
      π (N.toWeakModule.act a n x) = N.toWeakModule.act a n (π x) := by
    intro a n x
    have hx : x ∈ P.carrier ⊔ Q.carrier := by rw [hPQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [WeakModule.act_add_right, map_add, map_add, hπP _ (P.act_mem a n hy), hπQ _ (Q.act_mem a n hz),
      hπP y hy, hπQ z hz]
    simp only [add_zero]
  set π₀ := N.diag π with hπ₀
  -- `π₀` lands in `P` and is the identity on `P`
  have hπ₀mem : ∀ x, π₀ x ∈ P.carrier := by
    intro x
    refine N.lev_induction (p := fun x => π₀ x ∈ P.carrier) x ?_ (by simp)
      (fun y z hy hz => by show π₀ (y + z) ∈ P.carrier; rw [map_add]; exact P.carrier.add_mem hy hz)
    intro k y hy
    rw [hπ₀, N.diag_of_mem π hy]
    exact hP k _ (hπmem y)
  have hπ₀P : ∀ x ∈ P.carrier, π₀ x = x := by
    intro x hx
    have hz : π₀ x - x = 0 := N.eq_zero_of_levProj fun k => by
      rw [map_sub, hπ₀, N.levProj_diag, N.diag_of_mem π (N.levProj_mem k x), hπP _ (hP k x hx),
        N.levProj_of_mem_same (N.levProj_mem k x), sub_self]
    exact sub_eq_zero.mp hz
  -- the complement: `ker π₀`
  refine ⟨⟨LinearMap.ker π₀, fun a n x hx => ?_⟩, fun k x hx => ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [hπ₀, N.diag_act π hπact, ← hπ₀, hx]
    simp [WeakModule.act]
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [hπ₀, ← N.levProj_diag, ← hπ₀, hx, map_zero]
  · have := LinearMap.isCompl_of_proj (p := P.carrier) (f := π₀.codRestrict P.carrier hπ₀mem)
      (fun x => Subtype.ext (by simpa using hπ₀P x x.2))
    simpa [LinearMap.ker_codRestrict] using this

end AdmissibleModule

/-- **The level-graded reading of rationality**: every level-graded weak submodule of every admissible module
has a level-graded weak complement (the category-internal reading of Dong–Li–Mason). -/
def AdmissiblyRationalGraded (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M)
    (P : WeakModule.Submodule' N.toWeakModule), N.IsLevelGraded P →
    ∃ Q : WeakModule.Submodule' N.toWeakModule, N.IsLevelGraded Q ∧ IsCompl P.carrier Q.carrier

/-- **`AdmissiblyRational` implies the level-graded reading.** -/
theorem admissiblyRationalGraded_of_admissiblyRational {W : VertexOperatorAlgebra 𝒱}
    (h : AdmissiblyRational W) : AdmissiblyRationalGraded W :=
  fun N P hP => N.exists_isLevelGraded_compl (h N) P hP

end VOA

section AxiomAudit
#print axioms VOA.AdmissibleModule.exists_isLevelGraded_compl
#print axioms VOA.admissiblyRationalGraded_of_admissiblyRational
end AxiomAudit
