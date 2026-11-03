/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientClose

/-!
# Generator reduction for invariant forms on modules  (Moonshine step M8c, form part 3)

General `OrdVModule` theory.  For a module `N : OrdVModule W M` and a bilinear form `B` on `M`:

* `FHLInv N B wt u` — FHL invariance at a homogeneous `u ∈ 𝒱_wt`, in the exact shape of
  `InvariantForm.IsFullyInvariant`:
  `B(u₍ₙ₎a, b) = (−1)^{wt} ∑_{j ≤ wt} (1/j!) B(a, (L₁ʲu)₍2wt−n−2−j₎ b)`.
* `WeightOrth N B` — distinct weight spaces are orthogonal; `dualMap N B : M → M*`,
  `a ↦ B(a,·)`, into the library's graded dual `RestrictedDual N`.
* `fhlInv_iff` — for homogeneous `u`, `FHLInv` ⇔ `dualMap` intertwines `u₍ₙ₎` with the
  contragredient mode `YMdual` (`Modules/ContragredientJacobi.lean`).
* `smul_mem_interSub` — the intertwined states form a vertex subalgebra: the module Jacobi
  identity at `m = 0` (`jacobi_m_zero`) on `M`, and the contragredient Jacobi
  identity (`contragredientJacobi_holds`) on `M*`; `vacuum_mem_interSub`.
* `fhlInv_of_generates` — invariance on a generating set of homogeneous states implies
  invariance for every homogeneous state.

## Status
All declarations proved; no `sorry`/axioms.  Unconditional (generation is a hypothesis of
`fhlInv_of_generates`, as it must be).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.InvForm

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **FHL invariance of a bilinear form on a module** at a homogeneous `u ∈ 𝒱_wt` (the module
version of `InvariantForm.IsFullyInvariant`):
`B(u₍ₙ₎a, b) = (−1)^{wt} ∑_{j ≤ wt} (1/j!) B(a, (L₁ʲu)₍2wt−n−2−j₎ b)`, i.e.
`B(Y(u,z)a, b) = B(a, Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹) b)`. -/
def FHLInv (N : OrdVModule W M) (B : LinearMap.BilinForm ℂ M) (wt : ℤ) (u : 𝒱) : Prop :=
  ∀ (n : ℤ) (a b : M), B (mode (N.YM u) n a) b
    = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        B a (mode (N.YM (((W.L 1) ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) b)

/-- Distinct weight spaces are `B`-orthogonal. -/
def WeightOrth (N : OrdVModule W M) (B : LinearMap.BilinForm ℂ M) : Prop :=
  ∀ α β : ℂ, α ≠ β → ∀ x ∈ N.weight α, ∀ y ∈ N.weight β, B x y = 0

/-- The map `M → M*`, `a ↦ B(a, ·)` (graded). -/
noncomputable def dualMap (N : OrdVModule W M) (B : LinearMap.BilinForm ℂ M) :
    M →ₗ[ℂ] RestrictedDual N :=
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  (DFinsupp.mapRange.linearMap fun α => B.compl₁₂ (N.weight α).subtype (N.weight α).subtype).comp
    (DirectSum.decomposeLinearEquiv N.weight).toLinearMap

theorem component_dualMap (N : OrdVModule W M) (B : LinearMap.BilinForm ℂ M) (β : ℂ) (a : M) :
    DirectSum.component ℂ ℂ (fun α => Dual ℂ (N.weight α)) β (dualMap N B a)
      = B.compl₁₂ (N.weight β).subtype (N.weight β).subtype (internalProjTo N.isInternal β a) := by
  rfl


variable {N : OrdVModule W M} {B : LinearMap.BilinForm ℂ M}

theorem form_proj_left (hO : WeightOrth N B) (β : ℂ) (a : M) {x : M} (hx : x ∈ N.weight β) :
    B (internalProjTo N.isInternal β a : M) x = B a x := by
  have ha : a ∈ ⨆ γ, N.weight γ := by
    rw [N.isInternal.submodule_iSup_eq_top]; trivial
  induction ha using Submodule.iSup_induction' with
  | mem γ y hy =>
    by_cases hγ : γ = β
    · subst hγ
      rw [internalProjTo_coe N.isInternal γ ⟨y, hy⟩]
    · rw [internalProjTo_eq_zero_of_ne N hy (Ne.symm hγ), Submodule.coe_zero, map_zero,
        LinearMap.zero_apply, hO γ β hγ y hy x hx]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, Submodule.coe_add, map_add, LinearMap.add_apply, hy, hz,
      map_add, LinearMap.add_apply]

theorem dualPairing_dualMap (hO : WeightOrth N B) (a : M) {β : ℂ} {x : M} (hx : x ∈ N.weight β) :
    dualPairing N x (dualMap N B a) = B a x := by
  rw [dualPairing_component N _ hx, component_dualMap, LinearMap.compl₁₂_apply,
    Submodule.subtype_apply, Submodule.subtype_apply, form_proj_left hO β a hx]

/-- The contragredient mode, paired against a homogeneous vector, reads off one component. -/
theorem dualPairing_mode_YMdual {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (n : ℤ)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) (f : RestrictedDual N) :
    dualPairing N x (mode (YMdual N u) n f)
      = dualCompMap N wt u n (α + n + 1 - wt)
          (DirectSum.component ℂ ℂ (fun β => Dual ℂ (N.weight β)) (α + n + 1 - wt) f) x := by
  induction f using DirectSum.induction_on with
  | zero =>
    have h0 : mode (YMdual N u) n (0 : RestrictedDual N) = 0 := LinearMap.map_zero _
    have h1 : DirectSum.component ℂ ℂ (fun β => Dual ℂ (N.weight β)) (α + n + 1 - wt)
        (0 : RestrictedDual N) = 0 := LinearMap.map_zero _
    erw [h0, h1]
    rw [map_zero, map_zero, LinearMap.zero_apply]
  | of γ g =>
    have hof : (DirectSum.of (fun β => Dual ℂ (N.weight β)) γ g)
        = DirectSum.lof ℂ ℂ (fun β => Dual ℂ (N.weight β)) γ g := rfl
    rw [hof]
    by_cases hγ : γ = α + n + 1 - wt
    · subst hγ
      rw [dualPairing_mode_lof_matched N hu n _ g hx (by unfold dualOutIdx; ring),
        DirectSum.component.lof_self]
    · rw [dualPairing_mode_lof_mismatched N hu n γ g hx (by
          unfold dualOutIdx; intro h; apply hγ; rw [h]; ring),
        DirectSum.component.of, dif_neg hγ, map_zero, LinearMap.zero_apply]
  | add f g hf hg =>
    have h0 : mode (YMdual N u) n (f + g : RestrictedDual N)
        = mode (YMdual N u) n f + mode (YMdual N u) n g := LinearMap.map_add _ _ _
    have h1 : DirectSum.component ℂ ℂ (fun β => Dual ℂ (N.weight β)) (α + n + 1 - wt)
        (f + g : RestrictedDual N)
        = DirectSum.component ℂ ℂ (fun β => Dual ℂ (N.weight β)) (α + n + 1 - wt) f
          + DirectSum.component ℂ ℂ (fun β => Dual ℂ (N.weight β)) (α + n + 1 - wt) g :=
      LinearMap.map_add _ _ _
    erw [h0, h1]
    rw [map_add, hf, hg, map_add, LinearMap.add_apply]

/-- **The key pairing**: `⟨u*₍ₙ₎ φ(a), x⟩` is the FHL right-hand side. -/
theorem dualPairing_mode_dualMap (hO : WeightOrth N B) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (n : ℤ) (a : M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    dualPairing N x (mode (YMdual N u) n (dualMap N B a))
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          B a (mode (N.YM (((W.L 1) ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) x) := by
  rw [dualPairing_mode_YMdual hu n hx, component_dualMap, dualCompMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hmem := twistMode_mem_weight N hu hx n j
  rw [LinearMap.compl₁₂_apply, Submodule.subtype_apply, Submodule.subtype_apply,
    form_proj_left hO _ a ((internalProjTo N.isInternal _ _).2),
    internalProjTo_coe N.isInternal _ ⟨_, hmem⟩]


/-- **Invariance ⇔ `φ : a ↦ B(a, ·)` intertwines `u` with its contragredient action.** -/
theorem fhlInv_iff (hO : WeightOrth N B) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) :
    FHLInv N B wt u ↔
      ∀ (n : ℤ) (a : M), dualMap N B (mode (N.YM u) n a) = mode (YMdual N u) n (dualMap N B a) := by
  constructor
  · intro hI n a
    refine restrictedDual_ext_of_pairing N fun α x hx => ?_
    rw [dualPairing_dualMap hO _ hx, dualPairing_mode_dualMap hO hu n a hx]
    exact hI n a x
  · intro h n a b
    have hb : b ∈ ⨆ γ, N.weight γ := by
      rw [N.isInternal.submodule_iSup_eq_top]; trivial
    induction hb using Submodule.iSup_induction' with
    | mem γ y hy =>
      rw [← dualPairing_dualMap hO _ hy, h, dualPairing_mode_dualMap hO hu n a hy]
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, hy, hz, ← smul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_add, smul_add]

/-- The set of states whose contragredient action is intertwined by `φ`. -/
noncomputable def interSub (N : OrdVModule W M) (B : LinearMap.BilinForm ℂ M) : Submodule ℂ 𝒱 where
  carrier := {u | ∀ (n : ℤ) (a : M),
    dualMap N B (mode (N.YM u) n a) = mode (YMdual N u) n (dualMap N B a)}
  add_mem' {u v} hu hv n a := by
    simp only [Set.mem_setOf_eq, map_add, mode_add, LinearMap.add_apply] at hu hv ⊢
    rw [hu n a, hv n a]
  zero_mem' n a := by
    simp only [map_zero, mode_zero, LinearMap.zero_apply]
  smul_mem' c u hu n a := by
    simp only [Set.mem_setOf_eq, map_smul, mode_smul, LinearMap.smul_apply] at hu ⊢
    rw [hu n a]

theorem vacuum_mem_interSub : W.vacuum ∈ interSub N B := by
  intro n a
  rw [N.vacuum_YM, YMdual_vacuum N, mode_one, mode_one]
  split_ifs <;> simp


theorem finsum_cbz_zero {X : Type*} [AddCommGroup X] [Module ℂ X] (f : ℤ → X) :
    ∑ᶠ i : ℤ, cbz 0 i • f i = f 0 := by
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul]),
    cbz_zero, one_smul]

/-- The module Jacobi identity at `m = 0`: `(u₍ℓ₎v)₍ₙ₎` as a finite combination of products. -/
theorem jacobi_m_zero (A : WeakModule W M) (u v : 𝒱) (a : M) (ℓ n : ℤ) :
    mode (A.YM (W.smul u ℓ v)) n a
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (A.YM u) (ℓ + 0 - i) (mode (A.YM v) (n + i) a)
            - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (0 + i) a)) := by
  rw [A.jacobi u v a ℓ 0 n, finsum_cbz_zero, add_zero, zero_add, sub_zero]

theorem jacobi_m_zero_fin (A : WeakModule W M) (u v : 𝒱) (a : M) (ℓ n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (mode (A.YM u) (ℓ + 0 - i) (mode (A.YM v) (n + i) a)
        - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) (0 + i) a))).Finite := by
  obtain ⟨Kv, hKv⟩ := A.truncation v a
  obtain ⟨Ku, hKu⟩ := A.truncation u a
  apply Set.Finite.subset (Set.finite_Icc 0 (max (Kv - n) Ku))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hKv (n + i) (by omega), hKu (0 + i) (by omega), map_zero, map_zero, smul_zero, sub_zero,
      smul_zero]

/-- **The intertwined states form a vertex subalgebra**: closed under all `n`-th products. -/
theorem smul_mem_interSub {u v : 𝒱} (hu : u ∈ interSub N B) (hv : v ∈ interSub N B) (ℓ : ℤ) :
    W.smul u ℓ v ∈ interSub N B := by
  intro n a
  have hJ := contragredientJacobi_holds N u v (dualMap N B a) ℓ 0 n
  rw [finsum_cbz_zero (fun i => mode (YMdual N (W.smul u (ℓ + i) v)) (0 + n - i) (dualMap N B a)),
    add_zero, zero_add, sub_zero] at hJ
  rw [← hJ, jacobi_m_zero N.toWeakModule u v a ℓ n,
    map_finsum _ (jacobi_m_zero_fin N.toWeakModule u v a ℓ n)]
  refine finsum_congr fun i => ?_
  rw [map_smul, map_sub, map_smul]
  rw [hu, hv, hv, hu, add_zero]


/-- **Generator reduction for module invariant forms.**  If `B` has orthogonal weight spaces,
satisfies the FHL invariance on each member of a set `G` of homogeneous states, and `G`
generates `𝒱` as a vertex algebra (every submodule containing `𝟙` and `G` and closed under all
`n`-th products is `⊤`), then `B` is FHL-invariant for every homogeneous state. -/
theorem fhlInv_of_generates (hO : WeightOrth N B) (G : Set 𝒱)
    (hG : ∀ S : Submodule ℂ 𝒱, W.vacuum ∈ S → (∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, W.smul u n v ∈ S) →
      G ⊆ S → S = ⊤)
    (hGinv : ∀ g ∈ G, ∃ wt : ℤ, g ∈ W.grading wt ∧ FHLInv N B wt g)
    {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) : FHLInv N B wt u := by
  have htop : interSub N B = ⊤ := hG _ vacuum_mem_interSub
    (fun u hu v hv n => smul_mem_interSub hu hv n)
    (fun g hg => by
      obtain ⟨w, hw, hI⟩ := hGinv g hg
      exact (fhlInv_iff hO hw).mp hI)
  exact (fhlInv_iff hO hu).mpr (by
    have : u ∈ interSub N B := by rw [htop]; trivial
    exact this)

end VOA.Moonshine.InvForm
