/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.WeakModule
import VOA.Modules.Character
import VOA.Modules.Translation
import VOA.Core.LieAlgebraV1

/-!
# Zhu's algebra `A(𝒱)` — Theorem 5.3.4  (Gannon §5.3.2, pp. 333–336)

"Remarkably, weakly rational VOAs `𝒱` have (like a finite group `G`) a
finite-dimensional associative semisimple algebra `A(𝒱)`, which classifies the finitely
many irreducible `𝒱`-modules." The VOA analogue of the group algebra `ℂG` / the universal
enveloping algebra `U(𝔤)`.

## The Zhu product and `O(𝒱)`

* **Zhu product** (eq. 5.3.8a/b): for `u ∈ 𝒱ₖ`,
  `u * v = Res_z(Y(u,z) v (z+1)ᵏ / z) = ∑_{m≥0} C(k,m) u₍ₘ₋₁₎ v` (a finite sum, since
  `C(k,m) = 0` for `m > k`), extended over the grade decomposition of a general `u`.
  Built here as `zhuMul` via the bundled `DFinsupp.lsum`.
* **Normal-ordered product** (eq. 5.3.10a): `u · v = Res_z(Y(u,z) v z^{k-1}) = u₍₋₁₎ v`
  (`normalMul`).
* `O(𝒱) := span{(L₋₁u + L₀u) * v}` (eq. 5.3.8c); **Zhu's algebra** `A(𝒱) := 𝒱 / O(𝒱)`,
  built here as the `ℂ`-module quotient with the canonical projection `mk` and unit `[𝟙]`.
* The **unit laws** `𝟙 * v = v` and (right unit) are proved on `𝒱`
  (`zhuMul_vacuum_left`, `zhuMul_vacuum_right`).

## Status

Axiom-clean for the **definitional layer + bilinearity + unit laws + zero-mode descent 5.3.9b**: `zhuMul` (5.3.8a/b), `normalMul` (5.3.10a), `O`, the `ℂ`-module `A(𝒱)`, `mk`,
`one`, the **bilinearity** of the Zhu product
(`zhuMul_add_left`/`zhuMul_smul_left`/`zhuMul_add_right`/`zhuMul_smul_right`, the prerequisite
for `*` to descend to a bilinear product on `A(𝒱)`), the unit laws
`zhuMul_vacuum_left`/`zhuMul_vacuum_right`, and **`oMod_L_translation`** (5.3.9b,
`o(L₋₁u+L₀u)=0`, off the module translation covariance `Modules.Translation.act_T_covariance`)
are all `sorry`-free / axiom-free.

**The associative algebra structure on `A(𝒱)` is proved** (Zhu [574] Thm 2.1.1–2.1.2,
unconditional, axiom-free): `O(𝒱)` is a two-sided ideal for `*` and `*` is associative modulo
`O(𝒱)` — `Modules.ZhuRingInstance.zhuRingData_holds`, hence `instRingA : Ring (A 𝒱)`,
`instAlgebraA : Algebra ℂ (A 𝒱)`.  The **zero-mode descent** is proved both ways (`oMod_L_translation`
5.3.9b; `Modules.ZeroModeMult.oMod_zhuMul_lowest` 5.3.9a), so **Theorem 5.3.4's easy direction is
complete**: `M_h` is a genuine `A(𝒱)`-module (`ZhuRingInstance.moduleMh`).

**Not proved in this file:** **Theorem 5.3.4's lifting direction**: the
generalized-Verma / induced module `U ↦ M(U)` and its irreducible quotient, the bijection
`Φ(𝒱) ↔ Irr A(𝒱)` and `A(𝒱) ≅ ⊕_{M∈Φ} M_{n×n}` for weakly rational `𝒱` (the induced module is
built in the `ZhuVermaAn*` files). The `zhuMul`/`O`/`A(𝒱)` scaffolding here is what the proved
structure is built on.

## Dependencies
* `VOA.Modules.WeakModule`, `Modules.Character` (zero modes `oMod`),
  `Core.LieAlgebraV1` (`zeroMode`).

## References
* Gannon §5.3.2, Thm 5.3.4, eqs. (5.3.8)–(5.3.10); Zhu [574]; Frenkel–Zhu;
  Dong–Li–Mason; Nagatomo–Tsuchiya [227].
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The Zhu product (5.3.8a/b) -/

/-- The weight-`k` slice of the Zhu product `· * v`: on `uₖ ∈ 𝒱ₖ`,
`∑_{m=0}^{k} C(k,m) (uₖ)₍ₘ₋₁₎ v` (a finite sum; for `k ≥ 0`, `C(k,m) = 0` when `m > k`).
A `ℂ`-linear map `𝒱ₖ → 𝒱`. -/
noncomputable def zhuFamily (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] 𝒱 where
  toFun uk := ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • W.smul (uk : 𝒱) ((m : ℤ) - 1) v
  map_add' a b := by
    simp only [Submodule.coe_add, PreVertexAlgebra.smul_add_left, smul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [SetLike.val_smul, PreVertexAlgebra.smul_smul_left, smul_comm c, RingHom.id_apply,
      Finset.smul_sum]

/-- The **Zhu product** `u * v = Res_z(Y(u,z) v (z+1)ᵏ/z) = ∑_m C(k,m) u₍ₘ₋₁₎ v` for
`u ∈ 𝒱ₖ` (Gannon 5.3.8a/b), extended bilinearly over the grade decomposition of `u`. -/
noncomputable def zhuMul (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) : 𝒱 :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (zhuFamily W v)) (DirectSum.decompose W.grading u)

@[inherit_doc] scoped notation:70 u " *[" W "] " v => zhuMul W u v

/-- The **normal-ordered product** `u · v = Res_z(Y(u,z) v z^{k-1}) = u₍₋₁₎ v` (Gannon
5.3.10a). -/
def normalMul (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) : 𝒱 := W.smul u (-1) v

@[simp] theorem normalMul_def (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    normalMul W u v = W.smul u (-1) v := rfl

/-! ## Bilinearity of the Zhu product (proved, axiom-clean)

The Zhu product `u * v` is `ℂ`-bilinear: linear in `u` (it is `DFinsupp.lsum (zhuFamily v)`
post-composed with the grade decomposition, a composite of linear maps) and linear in `v`
(through the `v`-linearity of each `zhuFamily` slice). This is the structural prerequisite for
`*` to descend to a *bilinear* product on `A(𝒱)` once `O(𝒱)` is shown to be a two-sided ideal
(the deep Zhu step). -/

/-- The weight slice `zhuFamily W v` is additive in `v`. -/
theorem zhuFamily_add (W : VertexOperatorAlgebra 𝒱) (v₁ v₂ : 𝒱) :
    zhuFamily W (v₁ + v₂) = zhuFamily W v₁ + zhuFamily W v₂ := by
  funext k
  refine LinearMap.ext fun uk => ?_
  simp only [Pi.add_apply, LinearMap.add_apply, zhuFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_add_right, smul_add, Finset.sum_add_distrib]

/-- The weight slice `zhuFamily W v` is homogeneous in `v`. -/
theorem zhuFamily_smul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (v : 𝒱) :
    zhuFamily W (c • v) = c • zhuFamily W v := by
  funext k
  refine LinearMap.ext fun uk => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply, zhuFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_smul_right, Finset.smul_sum, smul_comm c]

/-- **`(u₁ + u₂) * v = u₁ * v + u₂ * v`** — the Zhu product is additive in the left factor. -/
theorem zhuMul_add_left (W : VertexOperatorAlgebra 𝒱) (u₁ u₂ v : 𝒱) :
    zhuMul W (u₁ + u₂) v = zhuMul W u₁ v + zhuMul W u₂ v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (zhuFamily W v)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) u₁ u₂

/-- **`(c • u) * v = c • (u * v)`** — the Zhu product is homogeneous in the left factor. -/
theorem zhuMul_smul_left (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (u v : 𝒱) :
    zhuMul W (c • u) v = c • zhuMul W u v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (zhuFamily W v)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c u

/-- **`u * (v₁ + v₂) = u * v₁ + u * v₂`** — the Zhu product is additive in the right factor. -/
theorem zhuMul_add_right (W : VertexOperatorAlgebra 𝒱) (u v₁ v₂ : 𝒱) :
    zhuMul W u (v₁ + v₂) = zhuMul W u v₁ + zhuMul W u v₂ := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (zhuFamily W (v₁ + v₂))) (DirectSum.decompose W.grading u) = _
  rw [zhuFamily_add, map_add, LinearMap.add_apply]
  rfl

/-- **`u * (c • v) = c • (u * v)`** — the Zhu product is homogeneous in the right factor. -/
theorem zhuMul_smul_right (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (u v : 𝒱) :
    zhuMul W u (c • v) = c • zhuMul W u v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (zhuFamily W (c • v))) (DirectSum.decompose W.grading u) = _
  rw [zhuFamily_smul, map_smul, LinearMap.smul_apply]
  rfl

/-! ## Unit laws -/

/-- **Left unit:** `𝟙 * v = v` (Gannon §5.3.2). The vacuum's only homogeneous slice is at
grade `0`, where `C(0,m) = δ_{m,0}` and `𝟙₍₋₁₎ v = v`. -/
theorem zhuMul_vacuum_left (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    zhuMul W W.vacuum v = v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : zhuMul W W.vacuum v = zhuFamily W v 0 ⟨W.vacuum, W.vacuum_mem⟩ := by
    change (DFinsupp.lsum ℂ (zhuFamily W v)) (DirectSum.decompose W.grading W.vacuum) = _
    rw [DirectSum.decompose_of_mem W.grading W.vacuum_mem]
    exact DFinsupp.lsum_single ℂ (zhuFamily W v) 0 ⟨W.vacuum, W.vacuum_mem⟩
  rw [hcollapse]
  change ∑ m ∈ Finset.range ((0 : ℤ).toNat + 1), cbz 0 m • W.smul (W.vacuum : 𝒱) ((m : ℤ) - 1) v = v
  rw [show (0 : ℤ).toNat + 1 = 1 from rfl, Finset.sum_range_one]
  simp only [Nat.cast_zero, cbz_zero, one_smul, zero_sub]
  rw [PreVertexAlgebra.smul_vacuum_left, if_pos rfl]

/-- **Right unit:** `v * 𝟙 = v` (Gannon §5.3.2). On each grade `k`, only the `m = 0` term
survives (`v₍ₘ₋₁₎𝟙 = 0` for `m ≥ 1` by creation, `v₍₋₁₎𝟙 = v`), so the product reassembles
the grade decomposition of `v`. -/
theorem zhuMul_vacuum_right (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    zhuMul W v W.vacuum = v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  letI : ∀ (i : ℤ) (x : W.grading i), Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  change (DFinsupp.lsum ℂ (zhuFamily W W.vacuum)) (DirectSum.decompose W.grading v) = v
  have hfam : zhuFamily W W.vacuum = fun k => (W.grading k).subtype := by
    funext k
    refine LinearMap.ext fun uk => ?_
    change ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • W.smul (uk : 𝒱) ((m : ℤ) - 1) W.vacuum
        = (uk : 𝒱)
    rw [Finset.sum_eq_single 0 (fun m _ hm => ?_) (fun h0 => ?_)]
    · simp only [Nat.cast_zero, cbz_zero, one_smul, zero_sub]
      exact (W.smul_vacuum_right (uk : 𝒱)).1
    · rw [PreVertexAlgebra.smul_vacuum_nonneg _ _ (by omega : (0 : ℤ) ≤ (m : ℤ) - 1), smul_zero]
    · exact absurd (Finset.mem_range.mpr (by omega)) h0
  rw [hfam, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  exact DirectSum.sum_support_decompose W.grading v

/-! ## `O(𝒱)` and the algebra `A(𝒱)` -/

/-- `O(𝒱) := span{(L₋₁u + L₀u) * v}` (Gannon 5.3.8c). -/
def O (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = zhuMul W (W.L (-1) u + W.L 0 u) v}

/-- **Zhu's algebra** `A(𝒱) := 𝒱 / O(𝒱)`, as a `ℂ`-module (Gannon 5.3.8). Its associative
algebra structure descends from the Zhu product — see the `### Zhu's theorem` section. -/
abbrev A (W : VertexOperatorAlgebra 𝒱) : Type u := 𝒱 ⧸ O W

/-- The canonical projection `𝒱 → A(𝒱)`, `u ↦ [u]`. -/
def mk (W : VertexOperatorAlgebra 𝒱) : 𝒱 →ₗ[ℂ] A W := (O W).mkQ

/-- The unit `[𝟙] ∈ A(𝒱)`. -/
def one (W : VertexOperatorAlgebra 𝒱) : A W := mk W W.vacuum

/-! ## Zero-mode descent 5.3.9b (proved, axiom-clean)

The module zero mode `o(v)` (`Character.oMod`) on a homogeneous `v ∈ 𝒱ₖ` is `v₍ₖ₋₁₎`
(`oMod_homogeneous`). Combined with the **module translation covariance**
`Modules.Translation.act_T_covariance` (`(L₋₁u)₍n₎ᴹ = −n·u₍n−1₎ᴹ`), this gives
`o(L₋₁u) = −k·o(u)`, while `L₀u = k·u` gives `o(L₀u) = k·o(u)`; they cancel:

  `o(L₋₁u + L₀u) = 0`   (`oMod_L_translation`, Gannon 5.3.9b).

This is exactly the statement that `O(𝒱)`'s generators act as `0` on a lowest-weight space, so
`[u] ∈ A(𝒱)` acts on `M_h` — the bridge from `A(𝒱)` to module categories (Theorem 5.3.4(c)). -/

section ZeroMode
variable {M : Type u} [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra 𝒱}

/-- The zero mode `o(v)` on a homogeneous `v ∈ 𝒱ₖ` is `v₍ₖ₋₁₎` (Gannon §5.2.1). -/
theorem oMod_homogeneous (N : OrdVModule W M) {k : ℤ} {v : 𝒱} (hv : v ∈ W.grading k) :
    oMod N v = mode (N.YM v) (k - 1) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oMod N v = oModFamily N k ⟨v, hv⟩ := by
    change (DFinsupp.lsum ℂ (oModFamily N)) (DirectSum.decompose W.grading v) = _
    rw [DirectSum.decompose_of_mem W.grading hv]
    exact DFinsupp.lsum_single ℂ (oModFamily N) k ⟨v, hv⟩
  rw [hcollapse]; rfl

/-- `o(L₋₁u) = −k·o(u)` on a homogeneous `u ∈ 𝒱ₖ` (off the module translation covariance). -/
theorem oMod_L_neg_one (N : OrdVModule W M) {k : ℤ} {u : 𝒱} (hu : u ∈ W.grading k) :
    oMod N (W.L (-1) u) = (-(k : ℂ)) • oMod N u := by
  have heq : W.L (-1) u = W.smul W.conformalVector 0 u := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def, show ((-1 : ℤ) + 1) = 0 from by ring]
  have hmem : W.L (-1) u ∈ W.grading (k + 1) := by
    have h := W.smul_mem_grading W.conformalVector_mem_grading_two hu 0
    rw [show (2 + k - 0 - 1 : ℤ) = k + 1 from by ring] at h
    rwa [← heq] at h
  rw [oMod_homogeneous N hmem, oMod_homogeneous N hu, show (k + 1 - 1 : ℤ) = k from by ring]
  ext x
  simp only [LinearMap.smul_apply]
  have hcov := act_T_covariance N.toWeakModule u k x
  simp only [WeakModule.act_def] at hcov
  exact hcov

/-- **Zero-mode descent 5.3.9b** (Gannon): `o(L₋₁u + L₀u) = 0` on a homogeneous `u ∈ 𝒱ₖ`.
`o(L₋₁u) = −k·o(u)` (covariance) and `o(L₀u) = k·o(u)` (`L₀u = k·u`) cancel; this makes
`O(𝒱)` act as `0` on lowest-weight spaces, so `[u] ∈ A(𝒱)` acts there. -/
theorem oMod_L_translation (N : OrdVModule W M) {k : ℤ} {u : 𝒱} (hu : u ∈ W.grading k) :
    oMod N (W.L (-1) u + W.L 0 u) = 0 := by
  rw [map_add, oMod_L_neg_one N hu, W.L_zero_grading u hu, map_smul, ← add_smul,
    neg_add_cancel, zero_smul]

end ZeroMode

/-!
### Zhu's theorem — (1)–(2) proved; (3) lifting not proved here

The content of §5.3.2 is built directly on the `zhuMul` / `O` / `A(𝒱)` scaffolding above.

1. **`O(𝒱)` is a two-sided `*`-ideal and `*` is associative mod `O(𝒱)`** (Zhu [574]
   Thm 2.1.1–2.1.2): `u ∈ O ⟹ u*v, v*u ∈ O`, and `(u*v)*w − u*(v*w) ∈ O` — **proved
   unconditionally**, axiom-free (`Modules.ZhuRingInstance.zhuRingData_holds`; the residue cores
   `ZhuRightIdeal.right_ideal_core` + `ZhuAssociator.associator_core`).  This endows `A(𝒱)` with
   an associative `Ring`/`ℂ`-algebra structure with unit `[𝟙]` (`instRingA`, `instAlgebraA`).

2. **Zero-mode descent** (5.3.9a/b): both proved — `o(L₋₁u+L₀u) = 0` (`oMod_L_translation`) and
   `o(u*v) = o(u)∘o(v)` on `M_h` (`Modules.ZeroModeMult.oMod_zhuMul_lowest`). With (1), `[u] ∈ A(𝒱)`
   acts on `M_h` — **Theorem 5.3.4(c), the easy direction `M ↦ M_h`, complete** (`ZhuRingInstance.moduleMh`).

3. **Theorem 5.3.4 lifting direction** (not proved here) (`zhu_semisimple`, `zhu_module_bijection`): for weakly
   rational `𝒱`, `A(𝒱)` finite-dim semisimple, `A(𝒱) ≅ ⊕_{M∈Φ} M_{n(M)×n(M)}`, the bijection
   `Φ(𝒱) ↔ Irr A(𝒱)` — via the generalized-Verma lift `U ↦ M(U)` (the induced module, built in
   the `ZhuVermaAn*` files).

(1)–(2) are proved axiom-free; (3) is not proved here — none faked or axiomatized.
-/

end VOA
