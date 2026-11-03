/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtTransport

/-!
# HKL extensions: the vertex operator of an algebra object in `Rep V`

Huang–Kirillov–Lepowsky (2015), Thm 3.2: for an algebra `(A, μ, η)` in the braided category of
ordinary `V`-modules, the would-be vertex operator of the extension `W = A` is

  `Y_W(a, z) b := μ(𝒴_{A,A}(a, z) b)`,

with `𝒴_{A,A}` the universal intertwining operator of the fusion product `A ⊠ A`.  This file
constructs it on the library's actual objects and proves the parts of HKL's proof that are pure
consequences of the universal property, the unitors, the braiding and the twist:

* `extIntertwiner F A μ` — `Y_W` as an intertwining operator of type `(A; A A)`
  (`postcompose` of the universal intertwiner by `μ`);
* `ext_unit_left` — **left unit law ⇒ `Y_W(η v, z) = Y_A(v, z)`** (the `V`-action), hence
  `ext_vacuum_left`: `Y_W(η 𝟙, z) = id` (the vacuum axiom, HKL (3.4));
* `ext_unit_right` — **right unit law ⇒ `Y_W(a, z) η v = e^{zL₋₁} Y_A(v, −z) a`** (the skew module
  vertex operator), the creation property's source;
* `ext_skew` — **commutativity `β_{A,A} ≫ μ = μ` ⇒ `Y_W = Ω₀(Y_W)`**, i.e.
  `Y_W(a, z) b = e^{zL₋₁} Y_W(b, e^{πi} z) a` (HKL's skew-symmetry, from `braiding = Ω₀`);
* `weight_int_of_twist` — **trivial twist ⇒ integral weights**: `θ_A = 𝟙` forces every nonzero
  weight space of `A` to sit at an integer;
* `ext_eq_zero_of_not_int` — hence **only integral modes**: `Y_W(a)_n = 0` for `n ∉ ℤ`, so `Y_W`
  is an honest `ℤ`-indexed formal distribution (`extField`).

What is NOT done here: locality
of `extField` (HKL Thm 3.2's analytic core: associativity of `μ` + the associativity/commutativity
of intertwining operators, `evalAssoc_fourPoint`), and the packaging as a
`VertexOperatorAlgebra` with niceness (KO 2002, CKM 2017, GR Prop. 2.7).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable (F : FusionChoice V) {A : Ordinary V}

/-- **The vertex operator of an algebra object**: `Y_W(a, z) b = μ(𝒴_{A,A}(a, z) b)`, an
intertwining operator of type `(A; A A)`. -/
def extIntertwiner (m : tensorObj F A A ⟶ A) : IntertwiningOperator A.isMod A.isMod A.isMod :=
  postcompose (F A A).intertwiner A.isMod m

@[simp] theorem extIntertwiner_val (m : tensorObj F A A ⟶ A) (n : ℂ) (a b : A.carrier) :
    (extIntertwiner F m).val n a b = m.val ((F A A).intertwiner.val n a b) := rfl

/-! ## Unit laws -/

/-- **Left unit law ⇒ `Y_W(η v, z) = Y_A(v, z)`**: on the image of the unit, the vertex
operator of the extension is the `V`-module vertex operator of `A`. -/
theorem ext_unit_left (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom) (n : ℂ) (v : 𝒱) (b : A.carrier) :
    (extIntertwiner F m).val n (η.val v) b = (moduleIntertwiner A.isMod).val n v b := by
  rw [extIntertwiner_val]
  have h1 := tensorHom_intertwiner F η (𝟙 A) n v b
  rw [Ordinary.id_apply] at h1
  rw [← h1, ← Ordinary.comp_apply, hl, leftUnitor_intertwiner]

/-- On the image of the unit, integral modes are the module modes: `(η v)_k b = v_k b`. -/
theorem ext_unit_left_int (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom) (k : ℤ) (v : 𝒱) (b : A.carrier) :
    (extIntertwiner F m).val (k : ℂ) (η.val v) b = mode (A.isMod.YM v) k b := by
  rw [ext_unit_left F m η hl]
  exact moduleModes_apply_intCast A.isMod k v b

/-- **The vacuum axiom** `Y_W(η 𝟙, z) = id` (HKL (3.4)): `(η 𝟙)_k b = δ_{k,-1} b`. -/
theorem ext_vacuum_left (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom) (k : ℤ) (b : A.carrier) :
    (extIntertwiner F m).val (k : ℂ) (η.val V.vacuum) b = if k = -1 then b else 0 := by
  rw [ext_unit_left_int F m η hl, ← WeakModule.act_def, WeakModule.act_vacuum]

/-- On the image of the unit, non-integral modes vanish. -/
theorem ext_unit_left_not_int (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom) {n : ℂ} (hn : ∀ k : ℤ, (k : ℂ) ≠ n)
    (v : 𝒱) (b : A.carrier) :
    (extIntertwiner F m).val n (η.val v) b = 0 := by
  rw [ext_unit_left F m η hl]
  change moduleModes A.isMod n v b = 0
  rw [moduleModes_of_not_int A.isMod hn]
  rfl

/-- **Right unit law ⇒ `Y_W(a, z) η v = e^{zL₋₁} Y_A(v, −z) a`**: on the image of the unit in
the second slot, the vertex operator of the extension is the skew module vertex operator. -/
theorem ext_unit_right (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom) (n : ℂ) (a : A.carrier) (v : 𝒱) :
    (extIntertwiner F m).val n a (η.val v) =
      (skew vacuumObject A A (moduleIntertwiner A.isMod)).val n a v := by
  rw [extIntertwiner_val]
  have h1 := tensorHom_intertwiner F (𝟙 A) η n a v
  rw [Ordinary.id_apply] at h1
  rw [← h1, ← Ordinary.comp_apply, hr, rightUnitor_intertwiner]

/-- Module modes on the vacuum at a shifted integer: `𝟙_{k+j} a = δ_{k+j,-1} a`. -/
theorem moduleModes_vacuum_shift (A : Ordinary V) (k : ℤ) (j : ℕ) (a : A.carrier) :
    moduleModes A.isMod ((k : ℂ) + (j : ℕ)) V.vacuum a = if k + j = -1 then a else 0 := by
  rw [show ((k : ℂ) + (j : ℕ)) = ((k + j : ℤ) : ℂ) by push_cast; ring,
    moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum]

/-- The skew module vertex operator on the vacuum, nonnegative modes: `e^{zL₋₁}Y_A(𝟙,−z)a` has no
`z^{-k-1}` term for `k ≥ 0`. -/
theorem skew_module_vacuum_nonneg (A : Ordinary V) {k : ℤ} (hk : 0 ≤ k) (a : A.carrier) :
    (skew vacuumObject A A (moduleIntertwiner A.isMod)).val (k : ℂ) a V.vacuum = 0 := by
  change BraidingSkew.skewModes A.isMod.Lm1 BraidingSkew.omegaPhase (moduleModes A.isMod) (k : ℂ) a V.vacuum = 0
  rw [BraidingSkew.skewModes_apply (BraidingSkew.trunc_of_isIntertwining
    (isIntertwiningOperator_moduleModes A.isMod))]
  rw [BraidingSkew.sSum_eq_sum 0 (fun j _ => by
    rw [moduleModes_vacuum_shift, if_neg (by omega)])]
  simp

/-- The skew module vertex operator on the vacuum, mode `-1`: the coefficient of `z⁰` in
`e^{zL₋₁}Y_A(𝟙,−z)a` is `a`. -/
theorem skew_module_vacuum_neg_one (A : Ordinary V) (a : A.carrier) :
    (skew vacuumObject A A (moduleIntertwiner A.isMod)).val ((-1 : ℤ) : ℂ) a V.vacuum = a := by
  change BraidingSkew.skewModes A.isMod.Lm1 BraidingSkew.omegaPhase (moduleModes A.isMod) ((-1 : ℤ) : ℂ) a
    V.vacuum = a
  rw [BraidingSkew.skewModes_apply (BraidingSkew.trunc_of_isIntertwining
    (isIntertwiningOperator_moduleModes A.isMod))]
  rw [BraidingSkew.sSum_eq_sum 1 (fun j hj => by
    rw [moduleModes_vacuum_shift, if_neg (by omega)])]
  rw [Finset.sum_range_one]
  unfold BraidingSkew.sTerm
  rw [show ((-1 : ℤ) : ℂ) + ((0 : ℕ) : ℂ) = ((-1 : ℤ) : ℂ) by push_cast; ring,
    moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]
  have h1 : BraidingSkew.omegaPhase (-1 : ℂ) = 1 := by
    rw [BraidingSkew.omegaPhase]; simp
  simp [BraidingSkew.sc, h1]

/-- **The creation axiom** (VA3) for `Y_W`, from the right unit law:
`(a)_{-1} η𝟙 = a` and `(a)_k η𝟙 = 0` for `k ≥ 0`. -/
theorem ext_creation (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)
    (hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom) (a : A.carrier) :
    (extIntertwiner F m).val ((-1 : ℤ) : ℂ) a (η.val V.vacuum) = a ∧
      ∀ k : ℤ, 0 ≤ k → (extIntertwiner F m).val (k : ℂ) a (η.val V.vacuum) = 0 := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [ext_unit_right F m η hr]; exact skew_module_vacuum_neg_one A a
  · rw [ext_unit_right F m η hr]; exact skew_module_vacuum_nonneg A hk a

/-! ## Commutativity ⇒ skew-symmetry -/

/-- **Commutativity ⇒ skew-symmetry** (HKL Thm 3.2): if `β_{A,A} ≫ μ = μ` for the library braiding
(FHL's `Ω₀`), then `Y_W = Ω₀(Y_W)`, i.e. `Y_W(a, z) b = e^{zL₋₁} Y_W(b, e^{πi} z) a`. -/
theorem ext_skew (m : tensorObj F A A ⟶ A) (hc : (braiding F A A).hom ≫ m = m) :
    skew A A A (extIntertwiner F m) = extIntertwiner F m := by
  have h := postcompose_braidingP_comp Phase.upper F (X := A) (Y := A) m
  rw [hc] at h
  exact h.symm

/-! ## Trivial twist ⇒ integral weights and integral modes -/

/-- **Trivial twist ⇒ integral weights**: if `θ_A = e^{2πiL(0)} = 𝟙`, every nonzero weight
space of `A` sits at an integer. -/
theorem weight_int_of_twist (htw : (twistIso A).hom = 𝟙 A) {α : ℂ}
    (hα : A.isMod.weight α ≠ ⊥) : ∃ k : ℤ, (k : ℂ) = α := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have h := twistIso_hom_of_mem A hx
  rw [htw, Ordinary.id_apply] at h
  have h1 : tw α = 1 := by
    have h2 : (tw α - 1) • x = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx0)
  rw [tw, Complex.exp_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ h2
  rw [hk]; ring

/-- A weight space at a non-integer vanishes when the twist is trivial. -/
theorem weight_eq_bot_of_not_int (htw : (twistIso A).hom = 𝟙 A) {α : ℂ}
    (hα : ∀ k : ℤ, (k : ℂ) ≠ α) : A.isMod.weight α = ⊥ := by
  by_contra h
  obtain ⟨k, hk⟩ := weight_int_of_twist htw h
  exact hα k hk

/-- **Only integral modes**: with trivial twist, `Y_W(a)_n = 0` for every `n ∉ ℤ` (the
`L₀`-conjugation property puts `a_n b` in weight `α + β − n − 1 ∉ ℤ`). -/
theorem ext_eq_zero_of_not_int (m : tensorObj F A A ⟶ A) (htw : (twistIso A).hom = 𝟙 A)
    {n : ℂ} (hn : ∀ k : ℤ, (k : ℂ) ≠ n) (a b : A.carrier) :
    (extIntertwiner F m).val n a b = 0 := by
  have hhom : ∀ α β (a b : A.carrier), a ∈ A.isMod.weight α → b ∈ A.isMod.weight β →
      (extIntertwiner F m).val n a b = 0 := by
    intro α β a b ha hb
    have hmem := FusionTop.mem_weight (extIntertwiner F m).property ha hb n
    by_cases hα : A.isMod.weight α = ⊥
    · rw [hα] at ha
      rw [(Submodule.mem_bot ℂ).mp ha, map_zero, LinearMap.zero_apply]
    by_cases hβ : A.isMod.weight β = ⊥
    · rw [hβ] at hb
      rw [(Submodule.mem_bot ℂ).mp hb, map_zero]
    obtain ⟨k, hk⟩ := weight_int_of_twist htw hα
    obtain ⟨l, hl⟩ := weight_int_of_twist htw hβ
    have hbot : A.isMod.weight (α + β - n - 1) = ⊥ := by
      apply weight_eq_bot_of_not_int htw
      intro j hj
      apply hn (k + l - j - 1)
      push_cast
      rw [hk, hl, hj]; ring
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hA : ∀ (a : A.carrier) β (b : A.carrier), b ∈ A.isMod.weight β →
      (extIntertwiner F m).val n a b = 0 := by
    intro a β b hb
    have e := linearMap_ext_homog A.isMod (((extIntertwiner F m).val n).flip b) 0
      (fun α a ha => hhom α β a b ha hb)
    exact congrArg (fun k => k a) e
  have e := linearMap_ext_homog A.isMod ((extIntertwiner F m).val n a) 0
    (fun β b hb => hA a β b hb)
  exact congrArg (fun k => k b) e

/-- **The vertex operator as an honest `ℤ`-indexed field**: `Y_W(a, z) = Σ_k a_k z^{-k-1}` with
`a_k = μ ∘ 𝒴_{A,A}(a)_k` (the remaining complex modes vanish by `ext_eq_zero_of_not_int` when the
twist is trivial). -/
def extField (m : tensorObj F A A ⟶ A) : A.carrier →ₗ[ℂ] FormalDist (Module.End ℂ A.carrier) where
  toFun a j := (extIntertwiner F m).val ((-j - 1 : ℤ) : ℂ) a
  map_add' a a' := by funext j; exact map_add _ a a'
  map_smul' c a := by funext j; exact map_smul _ c a

theorem mode_extField (m : tensorObj F A A ⟶ A) (a : A.carrier) (k : ℤ) (b : A.carrier) :
    mode (extField F m a) k b = (extIntertwiner F m).val (k : ℂ) a b := by
  change (extIntertwiner F m).val ((-(-k - 1) - 1 : ℤ) : ℂ) a b = _
  rw [show (-(-k - 1) - 1 : ℤ) = k by ring]

end VOA.Huang.HKLExt
