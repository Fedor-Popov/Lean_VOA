/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Commutativity

/-!
# Commutative vertex algebras, repaired — Theorem 5.1.4 for a bare vertex algebra

This leaf file restates the theory of commutative vertex algebras where it is not vacuous.

`Core/Commutativity.lean` states Theorem 5.1.4 for a `VertexOperatorAlgebra`.  For a VOA the
hypothesis forces `𝒱 = ℂ𝟙` (`L₀ = ω₍₁₎ = 0`, so every weight is `0`, and `𝒱₀ = ℂ𝟙` by VOA4):
this is `VertexOperatorAlgebra.old_isCommutative_iff_trivial` below.  Here the theory is
restated for a bare `PreVertexAlgebra`.

## Definition
`PreVertexAlgebra.IsCommutativeVA V`: `u₍ₙ₎v = 0` for all `u, v` and all `n ≥ 0` (Gannon Thm 5.1.4
(3); Borcherds).  On a bare `PreVertexAlgebra` it is equivalent to the library's `IsCommutative`
(`isCommutative_iff_isCommutativeVA`).

## Results (bare `PreVertexAlgebra`, no translation covariance unless stated)
* `isCommutativeVA_iff_bracketDist_eq_zero`: (3) ⇔ (1), all fields commute.
  - (1) ⇒ (3): apply `[Y(u,z₁),Y(v,z₂)] = 0` to `𝟙` and read off the `z₂⁰` coefficient.
  - (3) ⇒ (1): on any vector the commutator has no negative powers of `z₂` and is killed by
    `(z₁-z₂)ᴺ` (VA4), so it vanishes (`eq_zero_of_mulBySubPow_of_bddBelow`).
* `cmul_comm_of_isCommutativeVA`, `cmul_assoc_of_isCommutativeVA`, `commRingOfCommVA`:
  (1) ⇒ (2), product laws.
* `cmul_leibniz_of_isCommutativeVA`: `T` is a derivation.  **Takes translation covariance
  `[T, u₍ₙ₎] = -n u₍ₙ₋₁₎` as an explicit hypothesis**, since `PreVertexAlgebra` has no covariance
  axiom (S1 entry 1).
* `isCommutativeVA_iff_assoc_alg`: the bundled biconditional.
* Non-vacuity: `ofCommAlgebra A` (`Y(u,z) = u·`) is commutative for every finite-dimensional
  commutative `ℂ`-algebra `A`; `exists_isCommutativeVA_not_trivial` (`A = ℂ × ℂ`) is not `ℂ𝟙`.
* Defect certificate: `VertexOperatorAlgebra.old_isCommutative_iff_trivial`.

## References
* Gannon §5.1.3, Thm 5.1.4; Borcherds [68]; Kac, *Vertex algebras for beginners*, §1.4.
-/

namespace VOA

open Module (End)

universe u

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The definition, and the product (2) `cmul` -/

/-- **Commutative vertex algebra** (Gannon Thm 5.1.4 (3); Borcherds): every nonnegative mode
vanishes, `u₍ₙ₎v = 0` for all `u, v` and all `n ≥ 0`.  Equivalent to the commutation of all
fields (`isCommutative_iff_bracketDist_eq_zero`). -/
def IsCommutativeVA (V : PreVertexAlgebra 𝒱) : Prop :=
  ∀ (u v : 𝒱) (n : ℤ), 0 ≤ n → V.smul u n v = 0

/-! ## (1) ⇔ (3) -/

/-- On a commutative vertex algebra the negative-index coefficients vanish:
`(Y u)ₛ w = u₍₋ₛ₋₁₎ w = 0` for `s < 0`. -/
theorem IsCommutativeVA.coeff_neg {V : PreVertexAlgebra 𝒱} (hc : V.IsCommutativeVA) (u w : 𝒱)
    {s : ℤ} (hs : s < 0) : (V.Y u) s w = 0 := by
  have h := hc u w (-s - 1) (by omega)
  rwa [smul_eq_coeff, show -(-s - 1) - 1 = s by ring] at h

/-- **Theorem 5.1.4, (3) ⇔ (1)**: a vertex algebra is commutative iff all its fields commute,
`[Y(u,z₁), Y(v,z₂)] = 0`.  Holds for a bare `PreVertexAlgebra` (no translation covariance). -/
theorem isCommutativeVA_iff_bracketDist_eq_zero (V : PreVertexAlgebra 𝒱) :
    V.IsCommutativeVA ↔ ∀ u v : 𝒱, bracketDist (V.Y u) (V.Y v) = 0 := by
  constructor
  · intro hc u v
    obtain ⟨N, hN⟩ := V.locality u v
    refine FormalDist₂.ext fun s t => LinearMap.ext fun w => ?_
    have hkill : mulBySubPow N (applyVec w (bracketDist (V.Y u) (V.Y v))) = 0 := by
      rw [← applyVec_mulBySubPow, hN, applyVec_zero]
    have hbb : IsBddBelow₂ (applyVec w (bracketDist (V.Y u) (V.Y v))) := by
      refine ⟨0, fun p q hq => ?_⟩
      rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, hc.coeff_neg v w hq, map_zero, hc.coeff_neg v _ hq, sub_zero]
    have h0 := eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb
    exact congrFun (congrFun h0 s) t
  · intro hb u v n hn
    have h := congrArg (fun F : FormalDist₂ (End ℂ 𝒱) => F (-n - 1) 0 V.vacuum) (hb u v)
    simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
    change _ - _ = (0 : End ℂ 𝒱) V.vacuum at h
    rw [Y_apply_vacuum_zero, Y_apply_vacuum_eq_zero V u (by omega), map_zero, sub_zero,
      LinearMap.zero_apply] at h
    rw [smul_eq_coeff]
    exact h

/-- On a commutative vertex algebra all modes commute: `(Y u)ₛ (Y v)ₜ = (Y v)ₜ (Y u)ₛ`. -/
theorem IsCommutativeVA.coeff_comm {V : PreVertexAlgebra 𝒱} (hc : V.IsCommutativeVA) (u v : 𝒱)
    (s t : ℤ) : (V.Y u) s * (V.Y v) t = (V.Y v) t * (V.Y u) s := by
  have h := congrFun (congrFun ((isCommutativeVA_iff_bracketDist_eq_zero V).mp hc u v) s) t
  rw [bracketDist_apply] at h
  exact sub_eq_zero.mp h

/-- **Old vs new on a bare vertex algebra**: the library's `IsCommutative` (all field commutators
vanish, `Core/Commutativity.lean`) is equivalent to `IsCommutativeVA`.  The defect of S1 entry 3
was not this predicate but that every theorem about it was stated for a VOA, where it forces
`𝒱 = ℂ𝟙` (`VertexOperatorAlgebra.old_isCommutative_iff_trivial`). -/
theorem isCommutative_iff_isCommutativeVA (V : PreVertexAlgebra 𝒱) :
    V.IsCommutative ↔ V.IsCommutativeVA :=
  (isCommutativeVA_iff_bracketDist_eq_zero V).symm

/-! ## (1) ⇒ (2): the product laws -/

/-- **Commutativity of `cmul`** on a commutative vertex algebra: `u₍₋₁₎v = v₍₋₁₎u`. -/
theorem cmul_comm_of_isCommutativeVA {V : PreVertexAlgebra 𝒱} (hc : V.IsCommutativeVA) (u v : 𝒱) :
    V.cmul u v = V.cmul v u := by
  have h := LinearMap.congr_fun (hc.coeff_comm u v 0 0) V.vacuum
  simp only [Module.End.mul_apply, Y_apply_vacuum_zero] at h
  rw [cmul_def, cmul_def, smul_eq_coeff, smul_eq_coeff, show -(-1 : ℤ) - 1 = 0 by ring]
  exact h

/-- **Associativity of `cmul`** on a commutative vertex algebra:
`(u·v)·w = w·(u·v) = w₍₋₁₎u₍₋₁₎v = u₍₋₁₎w₍₋₁₎v = u·(w·v) = u·(v·w)`. -/
theorem cmul_assoc_of_isCommutativeVA {V : PreVertexAlgebra 𝒱} (hc : V.IsCommutativeVA)
    (u v w : 𝒱) : V.cmul (V.cmul u v) w = V.cmul u (V.cmul v w) := by
  have hm := LinearMap.congr_fun (hc.coeff_comm w u 0 0) v
  simp only [Module.End.mul_apply] at hm
  rw [cmul_comm_of_isCommutativeVA hc (V.cmul u v) w, cmul_comm_of_isCommutativeVA hc v w]
  simp only [cmul_def, smul_eq_coeff, show -(-1 : ℤ) - 1 = 0 by ring]
  exact hm

/-- **Theorem 5.1.4, (1) ⇒ (2)**, the ring half: a commutative vertex algebra carries a
`CommRing` structure with product `cmul` (`u · v = u₍₋₁₎v`), unit `𝟙`, and the ambient additive
group. -/
@[reducible]
def commRingOfCommVA (V : PreVertexAlgebra 𝒱) (hc : V.IsCommutativeVA) : CommRing 𝒱 :=
  { (inferInstance : AddCommGroup 𝒱) with
    mul := V.cmul
    one := V.vacuum
    mul_assoc := cmul_assoc_of_isCommutativeVA hc
    mul_comm := cmul_comm_of_isCommutativeVA hc
    one_mul := fun a => V.vacuum_cmul a
    mul_one := fun a => V.cmul_vacuum a
    left_distrib := fun a b c => V.smul_add_right a (-1) b c
    right_distrib := fun a b c => V.smul_add_left a b (-1) c
    zero_mul := fun a => V.smul_zero_left (-1) a
    mul_zero := fun a => V.smul_zero_right a (-1) }

/-- **`T` is a derivation of `cmul`** on a commutative vertex algebra (Gannon Thm 5.1.4 (2)):
`T(u·v) = (Tu)·v + u·(Tv)`, with `T u = u₍₋₂₎𝟙`.

⚠ Takes **translation covariance** `[T, u₍ₙ₎] = -n u₍ₙ₋₁₎` as the explicit hypothesis `hT`:
`PreVertexAlgebra` has no covariance axiom, and only the
`n = -1` instance is used.  In a VOA, `T = L₋₁` and the conclusion holds outright
(`VertexOperatorAlgebra.Lneg1_cmul_leibniz`). -/
theorem cmul_leibniz_of_isCommutativeVA {V : PreVertexAlgebra 𝒱} (hc : V.IsCommutativeVA)
    (hT : ∀ (u : 𝒱) (n : ℤ) (w : 𝒱),
      V.T (V.smul u n w) - V.smul u n (V.T w) = (-n : ℂ) • V.smul u (n - 1) w)
    (u v : 𝒱) : V.T (V.cmul u v) = V.cmul (V.T u) v + V.cmul u (V.T v) := by
  have h1 := hT u (-1) v
  rw [show (-((-1 : ℤ) : ℂ)) = 1 by norm_num, one_smul,
    show (-1 : ℤ) - 1 = -2 by ring, sub_eq_iff_eq_add] at h1
  -- `u₍₋₂₎v = v₍₋₁₎(u₍₋₂₎𝟙) = (Tu)·v`, by commuting modes.
  have h2 : V.smul u (-2) v = V.cmul (V.T u) v := by
    have hm := LinearMap.congr_fun (hc.coeff_comm u v 1 0) V.vacuum
    simp only [Module.End.mul_apply, Y_apply_vacuum_zero] at hm
    rw [cmul_comm_of_isCommutativeVA hc, cmul_def, T_apply, smul_eq_coeff, smul_eq_coeff,
      smul_eq_coeff, show -(-2 : ℤ) - 1 = 1 by ring, show -(-1 : ℤ) - 1 = 0 by ring]
    exact hm
  rw [cmul_def, h1, ← h2, cmul_def, add_comm]

/-- **Theorem 5.1.4, (3) ⇔ (3) ∧ (2)** (Gannon), bundled: a vertex algebra is commutative iff
its nonnegative modes vanish and (then) its `(−1)`-product `cmul` is commutative and associative.
The full commutative-associative-unital structure is `commRingOfCommVA`; the derivation law is
`cmul_leibniz_of_isCommutativeVA` (under translation covariance). -/
theorem isCommutativeVA_iff_assoc_alg (V : PreVertexAlgebra 𝒱) :
    V.IsCommutativeVA ↔
      ((∀ (u v : 𝒱) (n : ℤ), 0 ≤ n → V.smul u n v = 0)
        ∧ (∀ u v : 𝒱, V.cmul u v = V.cmul v u)
        ∧ (∀ u v w : 𝒱, V.cmul (V.cmul u v) w = V.cmul u (V.cmul v w))) :=
  ⟨fun hc => ⟨hc, cmul_comm_of_isCommutativeVA hc, cmul_assoc_of_isCommutativeVA hc⟩,
    fun h => h.1⟩

/-! ## Non-vacuity: the vertex algebra of a finite-dimensional commutative algebra -/

section OfCommAlgebra

variable (A : Type u) [CommRing A] [Algebra ℂ A]

/-- The constant field `Y(u,z) = u·` (multiplication by `u`, in degree `z⁰` only). -/
noncomputable def constMulField : A →ₗ[ℂ] FormalDist (End ℂ A) where
  toFun u := fun k => if k = 0 then LinearMap.mulLeft ℂ u else 0
  map_add' u v := by
    funext k
    change (if k = 0 then LinearMap.mulLeft ℂ (u + v) else 0)
      = (if k = 0 then LinearMap.mulLeft ℂ u else 0) + (if k = 0 then LinearMap.mulLeft ℂ v else 0)
    split_ifs
    · ext x; simp [add_mul]
    · simp
  map_smul' c u := by
    funext k
    change (if k = 0 then LinearMap.mulLeft ℂ (c • u) else 0)
      = c • (if k = 0 then LinearMap.mulLeft ℂ u else 0)
    split_ifs
    · ext x; simp
    · simp

theorem constMulField_apply (u : A) (k : ℤ) :
    constMulField A u k = if k = 0 then LinearMap.mulLeft ℂ u else 0 := rfl

theorem mode_constMulField (u : A) (n : ℤ) (x : A) :
    mode (constMulField A u) n x = if n = -1 then u * x else 0 := by
  rw [mode_apply, constMulField_apply]
  by_cases h : n = -1
  · rw [if_pos (by omega), if_pos h]; rfl
  · rw [if_neg (by omega), if_neg h]; rfl

/-- The grading concentrated in degree `0`. -/
def gradingZero : ℤ → Submodule ℂ A := fun n => if n = 0 then ⊤ else ⊥

theorem gradingZero_zero : gradingZero A 0 = ⊤ := by simp [gradingZero]

theorem gradingZero_of_ne {n : ℤ} (h : n ≠ 0) : gradingZero A n = ⊥ := by simp [gradingZero, h]

theorem eq_zero_of_mem_gradingZero {n : ℤ} (h : n ≠ 0) {x : A} (hx : x ∈ gradingZero A n) :
    x = 0 := by
  rw [gradingZero_of_ne A h] at hx; exact (Submodule.mem_bot ℂ).mp hx

theorem gradingZero_isInternal : DirectSum.IsInternal (gradingZero A) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, eq_top_iff.mpr (le_iSup_of_le 0 (by rw [gradingZero_zero]))⟩
  by_cases hi : i = 0
  · subst hi
    have : (⨆ (j : ℤ) (_ : j ≠ 0), gradingZero A j) = ⊥ :=
      iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => gradingZero_of_ne A hj
    rw [this]; exact disjoint_bot_right
  · rw [gradingZero_of_ne A hi]; exact disjoint_bot_left

variable [FiniteDimensional ℂ A]

/-- **The vertex algebra of a finite-dimensional commutative `ℂ`-algebra `A`**: `𝒱 = A` in
degree `0`, `Y(u,z) = u·` (only the mode `u₍₋₁₎ = u·` is nonzero), vacuum `1`.  This is the
`T = 0` case of the (2) ⇒ (1) direction of Theorem 5.1.4. -/
noncomputable def ofCommAlgebra : PreVertexAlgebra A where
  grading := gradingZero A
  isInternal := gradingZero_isInternal A
  finrank := fun _ => inferInstance
  Y := constMulField A
  vacuum := 1
  vacuum_mem := by rw [gradingZero_zero]; trivial
  grading_mode := by
    intro k ℓ u hu v hv n
    rw [mode_constMulField]
    by_cases hd : k + ℓ - n - 1 = 0
    · rw [hd, gradingZero_zero]; trivial
    · by_cases hn : n = -1
      · rw [if_pos hn]
        by_cases hk : k = 0
        · have hℓ : ℓ ≠ 0 := by omega
          rw [eq_zero_of_mem_gradingZero A hℓ hv, mul_zero]; exact Submodule.zero_mem _
        · rw [eq_zero_of_mem_gradingZero A hk hu, zero_mul]; exact Submodule.zero_mem _
      · rw [if_neg hn]; exact Submodule.zero_mem _
  vacuum_Y := by
    refine FormalDist.ext fun k => ?_
    rw [constMulField_apply, FormalDist.one_apply]
    split_ifs
    · ext x; simp
    · rfl
  creation := by
    refine fun u => ⟨by rw [mode_constMulField, if_pos rfl, mul_one], fun n hn => ?_⟩
    rw [mode_constMulField, if_neg (by omega)]
  locality := by
    intro u v
    refine local_of_bracketDist_eq_zero (FormalDist₂.ext fun s t => ?_)
    rw [bracketDist_apply, constMulField_apply, constMulField_apply]
    change _ = (0 : End ℂ A)
    split_ifs
    · ext x; simp [mul_left_comm]
    all_goals simp
  regularity := by
    intro u v
    refine ⟨0, fun n hn => ?_⟩
    rw [mode_constMulField, if_neg (by omega)]

theorem ofCommAlgebra_smul (u : A) (n : ℤ) (x : A) :
    (ofCommAlgebra A).smul u n x = if n = -1 then u * x else 0 :=
  mode_constMulField A u n x

@[simp] theorem ofCommAlgebra_vacuum : (ofCommAlgebra A).vacuum = 1 := rfl

/-- `ofCommAlgebra A` is a commutative vertex algebra. -/
theorem isCommutativeVA_ofCommAlgebra : (ofCommAlgebra A).IsCommutativeVA := by
  intro u v n hn
  rw [ofCommAlgebra_smul, if_neg (by omega)]

/-- Its `(−1)`-product is the product of `A`. -/
theorem ofCommAlgebra_cmul (u v : A) : (ofCommAlgebra A).cmul u v = u * v := by
  rw [cmul_def, ofCommAlgebra_smul, if_pos rfl]

end OfCommAlgebra

/-- **Non-vacuity of `IsCommutativeVA`**: there
is a commutative vertex algebra which is **not** `ℂ𝟙` — `ofCommAlgebra (ℂ × ℂ)`, where
`(1, 0) ∉ ℂ ∙ 𝟙 = ℂ ∙ (1, 1)`. -/
theorem exists_isCommutativeVA_not_trivial :
    ∃ V : PreVertexAlgebra (ℂ × ℂ), V.IsCommutativeVA ∧ ∃ x : ℂ × ℂ, x ∉ ℂ ∙ V.vacuum := by
  refine ⟨ofCommAlgebra (ℂ × ℂ), isCommutativeVA_ofCommAlgebra _, (1, 0), fun h => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  rw [ofCommAlgebra_vacuum] at hc
  have h1 := congrArg Prod.fst hc
  have h2 := congrArg Prod.snd hc
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one, smul_eq_mul,
    mul_one] at h1 h2
  exact one_ne_zero (h1.symm.trans h2)

end PreVertexAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Why the theory is stated for vertex algebras**: a VOA
whose underlying vertex algebra is commutative is `ℂ𝟙`.  Indeed `L₀ = ω₍₁₎ = 0`, so every weight
space `𝒱ₙ` with `n ≠ 0` vanishes, and `𝒱₀ = ℂ𝟙` (VOA4). -/
theorem mem_span_vacuum_of_isCommutativeVA (W : VertexOperatorAlgebra 𝒱)
    (hc : W.toPreVertexAlgebra.IsCommutativeVA) (v : 𝒱) : v ∈ ℂ ∙ W.vacuum := by
  have hle : ∀ n : ℤ, W.grading n ≤ ℂ ∙ W.vacuum := by
    intro n x hx
    by_cases hn : n = 0
    · subst hn; rw [← W.vacuum_grade]; exact hx
    · have hL : W.L 0 x = 0 := by
        rw [L_def]; exact hc W.conformalVector x 1 (by norm_num)
      rw [W.L_zero_grading x hx] at hL
      rcases smul_eq_zero.mp hL with h | h
      · exact absurd (Int.cast_eq_zero.mp h) hn
      · rw [h]; exact Submodule.zero_mem _
  have htop := W.isInternal.submodule_iSup_eq_top
  have hv : v ∈ ⨆ n, W.grading n := by rw [htop]; trivial
  exact (iSup_le hle) hv

/-- **The S1 entry 3 defect, certified**: for a VOA, the library's `IsCommutative` (the hypothesis
of `comm_iff_nonneg_modes`, `commRing_of_comm`, `comm_iff_assoc_alg`, …) holds **iff**
`𝒱 = ℂ𝟙`.  So those theorems are statements about the trivial VOA only. -/
theorem old_isCommutative_iff_trivial (W : VertexOperatorAlgebra 𝒱) :
    W.toPreVertexAlgebra.IsCommutative ↔ ∀ v : 𝒱, v ∈ ℂ ∙ W.vacuum := by
  rw [PreVertexAlgebra.isCommutative_iff_isCommutativeVA]
  refine ⟨mem_span_vacuum_of_isCommutativeVA W, fun h u v n hn => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (h u)
  rw [PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left, if_neg (by omega), smul_zero]

end VertexOperatorAlgebra

end VOA
