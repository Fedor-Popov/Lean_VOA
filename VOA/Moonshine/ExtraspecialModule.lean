/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LeechLatticeVOA
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.CharP.Two

/-!
# The extraspecial module `T`  (Moonshine step M5; FLM §7.4, Ch. 10)

The twisted sector of the FLM orbifold is `V_Λ^T = S[θ] ⊗ T`, where `T` is the faithful
irreducible module of the extraspecial group `Λ̂/K ≅ 2^{1+24}` on which the central `κ` acts by
`-1`.  Equivalently `T` is the simple module of the **twisted group algebra**
`A_L = ℂ^ε[L/2L]`: basis `e_ᾱ` (`ᾱ ∈ L/2L`), product `e_ᾱ e_β̄ = ε(α,β) e_{α+β}`.  This file
constructs `A_L` and `T` abstractly and computes `dim T`.

## Abstract part (`namespace VOA.Moonshine.Extraspecial`)
For `M : Matrix (Fin n) (Fin n) (ZMod 2)` let `c(x,y) = (-1)^{x ⬝ M y}` on `V = (ZMod 2)^n`
(`coc`; bimultiplicative, `c² = 1`, commutator `(-1)^{x ⬝ (M+Mᵀ) y}`, `coc_comm`).
* `op M x` — left multiplication by `e_x` on the regular representation `V → ℂ`;
  `op_mul : e_x e_y = c(x,y) e_{x+y}`.
* `alg M` — the twisted group algebra, as the `ℂ`-span of the `e_x` inside `End(V → ℂ)` (so the
  ring axioms are inherited); `eq_sum_coeff` (every element is `∑ f_v e_v`), `finrank_alg`
  (`dim = 2^n`).
* `isSimpleRing_alg` — **`A` is simple** when `det(M+Mᵀ) ≠ 0` over `ZMod 2`: averaging
  `∑_w c(w,w) e_w f e_w = 2^n f₀ · 1` (`sum_conj`, from character orthogonality
  `sum_sgn_dotProduct`) moves any nonzero ideal element to a unit.
* Wedderburn–Artin (`IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`) gives `A ≅ M_k(ℂ)`;
  `k² = 2^n` forces `n` even and `k = 2^{n/2}` (`even_of_isUnit`, `repDim_eq`).
* `Rep M hN` — the module `T = ℂ^k` with `A` acting through `repEquiv : A ≃ₐ End_ℂ(T)`;
  `isSimpleModule_rep`, `finrank_rep : dim T = 2^{n/2}`; **uniqueness**
  `nonempty_linearEquiv_rep` (every simple `A`-module is `≅ T`) and
  `finrank_of_isSimpleModule`.

## Lattice part (`namespace VOA.IntegralLattice`)
* `red : L →+ (ZMod 2)^rank` (coordinates mod 2 in `latticeBasis L`), surjective with kernel
  `2L` (`red_surjective`, `red_eq_zero_iff`); `cocMat L` the strictly lower-triangular Gram matrix
  mod 2.
* `latticeCocycle_eq_coc` — **descent**: `ε(α,β) = c(red α, red β)`; hence
  `latticeCocycle_add_two_nsmul` (`ε` depends only on classes mod `2L`).
* `isUnit_det_cocMat` — for `L` even with `IsUnit det(Gram)` (unimodular), the commutator form on
  `L/2L` is nondegenerate (`cocMat + cocMatᵀ = Gram mod 2`, `cocMat_add_transpose`).
* `eA α ∈ A_L`, `eA_mul : e_α e_β = ε(α,β) e_{α+β}`, `eA_neg : e_{-α} = e_α` (θ-compatibility),
  `eA_add_two_nsmul` (`K ⊇ 2L` acts trivially), `span_eA`.
* `ExtraT L hEven hU`, `eT α ∈ End_ℂ(T)`, `eT_mul`, `eT_neg`, `finrank_extraT :
  dim T = 2^{rank L / 2}`, `even_rank_of_unimodular`.

## Leech (`namespace VOA.Moonshine`)
* `leech_isUnit_det_gramMat` (from `Leech.lattice_isUnimodular`), `leechT`,
  **`finrank_leechT : dim T = 4096`**.

## Status
All declarations are proved, with no `sorry`; `#print axioms` for `finrank_leechT`,
`isSimpleRing_alg`, `nonempty_linearEquiv_rep`, `eT_mul` shows only `propext`,
`Classical.choice`, `Quot.sound` (no `VOA.pbw`).  The file is imported by the umbrella
`VOA/Moonshine.lean`.  `T` is *abstract*: its existence comes from
Wedderburn–Artin, not from an explicit model (e.g. functions on the Golay code).  Nothing here
yet relates `T` to the twisted Heisenberg space `S[θ]` (step M6).  The identification with FLM's
`T` is the standard one (simple module of `ℂ^ε[Λ/2Λ]`, central sign acting by `-1` through the
scalars `ε = ±1`), argued in prose, not formalised.

## References
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, §5.5, §7.4, Ch. 10.
-/

namespace VOA.Moonshine.Extraspecial

open scoped BigOperators
open Matrix

/-- The sign character `ZMod 2 → ℂ`, `0 ↦ 1`, `1 ↦ -1`. -/
noncomputable def sgn (z : ZMod 2) : ℂ := (-1 : ℂ) ^ z.val

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn, ZMod.val_one]

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rw [sgn, sgn, sgn, ZMod.val_add, ← pow_add]
  exact (neg_one_pow_eq_pow_mod_two _).symm

theorem sgn_mul_self (a : ZMod 2) : sgn a * sgn a = 1 := by
  rw [← sgn_add, CharTwo.add_self_eq_zero, sgn_zero]

variable {n : ℕ}

theorem add_self_vec (x : Fin n → ZMod 2) : x + x = 0 := by
  ext i; exact CharTwo.add_self_eq_zero _

variable (M : Matrix (Fin n) (Fin n) (ZMod 2))

/-- The cocycle `c(x,y) = (-1)^{x ⬝ M y}` on `V = (ZMod 2)^n`. -/
noncomputable def coc (x y : Fin n → ZMod 2) : ℂ := sgn (x ⬝ᵥ (M *ᵥ y))

theorem coc_add_left (x x' y : Fin n → ZMod 2) : coc M (x + x') y = coc M x y * coc M x' y := by
  simp [coc, add_dotProduct, sgn_add]

theorem coc_add_right (x y y' : Fin n → ZMod 2) : coc M x (y + y') = coc M x y * coc M x y' := by
  simp [coc, mulVec_add, dotProduct_add, sgn_add]

@[simp] theorem coc_zero_left (y : Fin n → ZMod 2) : coc M 0 y = 1 := by simp [coc, sgn_zero]

@[simp] theorem coc_zero_right (x : Fin n → ZMod 2) : coc M x 0 = 1 := by simp [coc, sgn_zero]

theorem coc_sq (x y : Fin n → ZMod 2) : coc M x y * coc M x y = 1 := sgn_mul_self _

/-- The commutator `c(x,y) c(y,x) = (-1)^{x ⬝ (M + Mᵀ) y}`. -/
theorem coc_comm (x y : Fin n → ZMod 2) :
    coc M x y * coc M y x = sgn (x ⬝ᵥ ((M + Mᵀ) *ᵥ y)) := by
  rw [coc, coc, ← sgn_add, add_mulVec, dotProduct_add]
  congr 2
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- Left multiplication by `e_x` on the regular representation `V → ℂ`:
`(e_x g)(y) = c(x, x+y) g(x+y)`, so that `e_x δ_z = c(x,z) δ_{x+z}`. -/
noncomputable def op (x : Fin n → ZMod 2) : Module.End ℂ ((Fin n → ZMod 2) → ℂ) where
  toFun g y := coc M x (x + y) * g (x + y)
  map_add' g h := by ext y; simp [mul_add]
  map_smul' a g := by ext y; simp; ring

theorem op_apply (x : Fin n → ZMod 2) (g : (Fin n → ZMod 2) → ℂ) (y : Fin n → ZMod 2) :
    op M x g y = coc M x (x + y) * g (x + y) := rfl

theorem op_mul (x y : Fin n → ZMod 2) : op M x * op M y = coc M x y • op M (x + y) := by
  refine LinearMap.ext fun g => funext fun z => ?_
  simp only [Module.End.mul_apply, op_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [show y + (x + z) = x + y + z by abel]
  simp only [coc_add_left, coc_add_right]
  linear_combination (-(coc M x x * coc M x z * coc M y x * coc M y y * coc M y z *
    g (x + y + z))) * coc_sq M x y


@[simp] theorem op_zero : op M 0 = 1 := by
  refine LinearMap.ext fun g => funext fun z => ?_
  simp [op_apply]

theorem eq_of_add_eq_zero {x y : Fin n → ZMod 2} (h : x + y = 0) : y = x := by
  have := congrArg (x + ·) h
  simpa [← add_assoc, add_self_vec] using this

theorem add_eq_zero_iff {x y : Fin n → ZMod 2} : x + y = 0 ↔ y = x :=
  ⟨eq_of_add_eq_zero, fun h => h ▸ add_self_vec x⟩

/-- `e_x δ_0 = δ_x`. -/
theorem op_single_zero (x : Fin n → ZMod 2) :
    op M x (Pi.single 0 1) = Pi.single x 1 := by
  funext y
  rw [op_apply]
  by_cases h : y = x
  · subst h; rw [add_self_vec]; simp
  · have h' : x + y ≠ 0 := fun h'' => h (eq_of_add_eq_zero h'')
    simp [h, h']

/-- The conjugation identity `c(w,w) e_w e_v e_w = (-1)^{ω(w,v)} e_v`. -/
theorem op_conj (w v : Fin n → ZMod 2) :
    coc M w w • (op M w * op M v * op M w) = sgn (w ⬝ᵥ ((M + Mᵀ) *ᵥ v)) • op M v := by
  rw [op_mul, smul_mul_assoc, op_mul, smul_smul, smul_smul,
    show w + v + w = v by rw [add_comm w v, add_assoc, add_self_vec, add_zero], ← coc_comm]
  congr 1
  rw [coc_add_left]
  linear_combination (coc M w v * coc M v w) * coc_sq M w w

/-- Character orthogonality on `(ZMod 2)^n`. -/
theorem sum_sgn_dotProduct (u : Fin n → ZMod 2) :
    ∑ w : Fin n → ZMod 2, sgn (w ⬝ᵥ u) = if u = 0 then (Fintype.card (Fin n → ZMod 2) : ℂ)
      else 0 := by
  split_ifs with hu
  · subst hu; simp [sgn_zero]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push Not at h; exact hu (funext h)
    have hi1 : u i = 1 := by
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact this _ hi
    have key : ∑ w : Fin n → ZMod 2, sgn (w ⬝ᵥ u)
        = ∑ w : Fin n → ZMod 2, sgn ((w + Pi.single i 1) ⬝ᵥ u) :=
      (Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun _ => rfl)).symm
    simp only [add_dotProduct, sgn_add, single_dotProduct, one_mul, hi1, sgn_one,
      ← Finset.sum_mul] at key
    linear_combination key / 2

/-- The **twisted group algebra** `ℂ^c[(ZMod 2)^n]`, realised as the span of the operators
`e_x` inside `End((V → ℂ))` (the left regular representation). -/
noncomputable def alg : Subalgebra ℂ (Module.End ℂ ((Fin n → ZMod 2) → ℂ)) :=
  (Submodule.span ℂ (Set.range (op M))).toSubalgebra
    (by rw [← op_zero]; exact Submodule.subset_span ⟨0, rfl⟩)
    (by
      intro a b ha hb
      have hmul := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at hmul
      refine (Submodule.span_le.mpr ?_) hmul
      rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
      change op M x * op M y ∈ _
      rw [op_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩))

theorem op_mem (x : Fin n → ZMod 2) : op M x ∈ alg M :=
  Submodule.subset_span ⟨x, rfl⟩

theorem mem_alg_iff (f : Module.End ℂ ((Fin n → ZMod 2) → ℂ)) :
    f ∈ alg M ↔ f ∈ Submodule.span ℂ (Set.range (op M)) := Iff.rfl

/-- **Coefficient formula**: every `f ∈ A` is `∑_v f(δ₀)(v) • e_v`. -/
theorem eq_sum_coeff {f : Module.End ℂ ((Fin n → ZMod 2) → ℂ)} (hf : f ∈ alg M) :
    f = ∑ v, f (Pi.single 0 1) v • op M v := by
  rw [mem_alg_iff] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨w, rfl⟩ := hg
      rw [op_single_zero]
      simp [Pi.single_apply]
  | zero => simp
  | add f g _ _ hf hg =>
      conv_lhs => rw [hf, hg]
      simp [add_smul, Finset.sum_add_distrib]
  | smul a f _ hf =>
      conv_lhs => rw [hf]
      simp [Finset.smul_sum, smul_smul]

/-- The operators `e_x` are linearly independent. -/
theorem linearIndependent_op : LinearIndependent ℂ (op M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (fun f : Module.End ℂ ((Fin n → ZMod 2) → ℂ) => f (Pi.single 0 1) i) hg
  simpa [op_single_zero, Pi.single_apply] using this

/-- `dim_ℂ A = 2^n`. -/
theorem finrank_alg : Module.finrank ℂ (alg M) = 2 ^ n := by
  have h := finrank_span_eq_card (linearIndependent_op M)
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
  exact h


/-- Nondegeneracy of the commutator form: `(M + Mᵀ) v = 0 → v = 0`. -/
theorem mulVec_eq_zero_iff (hN : IsUnit (M + Mᵀ).det) (v : Fin n → ZMod 2) :
    (M + Mᵀ) *ᵥ v = 0 ↔ v = 0 := by
  have hinj := (Matrix.mulVec_injective_iff_isUnit (A := M + Mᵀ)).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hN)
  constructor
  · intro h; exact hinj (by rw [h, mulVec_zero])
  · rintro rfl; exact mulVec_zero _

/-- **Averaging over conjugation** isolates the identity coefficient:
`∑_w c(w,w) e_w f e_w = 2^n f₀ · 1` for `f ∈ A`, when the commutator form is nondegenerate. -/
theorem sum_conj (hN : IsUnit (M + Mᵀ).det) {f : Module.End ℂ ((Fin n → ZMod 2) → ℂ)}
    (hf : f ∈ alg M) :
    ∑ w, coc M w w • (op M w * f * op M w) =
      ((Fintype.card (Fin n → ZMod 2) : ℂ) * f (Pi.single 0 1) 0) • 1 := by
  set a : (Fin n → ZMod 2) → ℂ := f (Pi.single 0 1) with ha
  have hfa : f = ∑ v, a v • op M v := eq_sum_coeff M hf
  have h1 : ∀ w, coc M w w • (op M w * f * op M w)
      = ∑ v, (a v * sgn (w ⬝ᵥ ((M + Mᵀ) *ᵥ v))) • op M v := by
    intro w
    rw [hfa, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_comm, op_conj, smul_smul]
  rw [Finset.sum_congr rfl fun w _ => h1 w, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Finset.mul_sum, sum_sgn_dotProduct, mulVec_eq_zero_iff M hN]
  rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [hv]) (by simp), if_pos rfl, op_zero,
    mul_comm]

/-- **The twisted group algebra is simple** when the commutator form `M + Mᵀ` is nondegenerate
over `ZMod 2`. -/
theorem isSimpleRing_alg (hN : IsUnit (M + Mᵀ).det) : IsSimpleRing (alg M) := by
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : ∃ a ∈ I, a ≠ 0
  · right
    obtain ⟨a, haI, ha0⟩ := hI
    -- some coefficient of `a` is nonzero
    obtain ⟨v₀, hv₀⟩ : ∃ v : Fin n → ZMod 2,
        (a : Module.End ℂ ((Fin n → ZMod 2) → ℂ)) (Pi.single 0 1) v ≠ 0 := by
      by_contra h
      push Not at h
      apply ha0
      apply Subtype.ext
      rw [eq_sum_coeff M a.2]
      simp [h]
    -- move it to the identity slot
    set b : alg M := ⟨op M v₀, op_mem M v₀⟩ * a with hb
    have hbI : b ∈ I := I.mul_mem_left _ _ haI
    have hb0 : (b : Module.End ℂ ((Fin n → ZMod 2) → ℂ)) (Pi.single 0 1) 0 ≠ 0 := by
      simp only [hb, Subalgebra.coe_mul, Module.End.mul_apply, op_apply, add_zero]
      exact mul_ne_zero (by
        have := coc_sq M v₀ v₀; intro h; rw [h, zero_mul] at this; exact zero_ne_one this) hv₀
    -- average
    have hsum : ∑ w, (⟨coc M w w • op M w, Subalgebra.smul_mem _ (op_mem M w) _⟩ : alg M) * b *
        ⟨op M w, op_mem M w⟩ ∈ I :=
      sum_mem fun w _ => I.mul_mem_right _ _ (I.mul_mem_left _ _ hbI)
    set s : ℂ := (Fintype.card (Fin n → ZMod 2) : ℂ) *
      (b : Module.End ℂ ((Fin n → ZMod 2) → ℂ)) (Pi.single 0 1) 0
    have hs : s ≠ 0 := mul_ne_zero (by simp) hb0
    have heq : ∑ w, (⟨coc M w w • op M w, Subalgebra.smul_mem _ (op_mem M w) _⟩ : alg M) * b *
        ⟨op M w, op_mem M w⟩ = algebraMap ℂ (alg M) s := by
      apply Subtype.ext
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [Subalgebra.coe_smul, Subalgebra.coe_one, Subalgebra.coe_mul,
        AddSubmonoidClass.coe_finsetSum, smul_mul_assoc]
      exact sum_conj M hN b.2
    rw [heq] at hsum
    have h1 : (1 : alg M) ∈ I := by
      have := I.mul_mem_left (algebraMap ℂ (alg M) s⁻¹) _ hsum
      rwa [← map_mul, inv_mul_cancel₀ hs, map_one] at this
    exact (TwoSidedIdeal.one_mem_iff I).mp h1
  · left
    push Not at hI
    ext x
    simp only [TwoSidedIdeal.mem_bot]
    exact ⟨fun hx => hI x hx, fun hx => hx ▸ I.zero_mem⟩


/-! ## Wedderburn–Artin: `A ≅ M_k(ℂ)` with `k² = 2^n` -/

theorem exists_matrix (hN : IsUnit (M + Mᵀ).det) :
    ∃ k : ℕ, 2 ^ n = k * k ∧ Nonempty (alg M ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) := by
  haveI := isSimpleRing_alg M hN
  obtain ⟨k, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ (alg M)
  refine ⟨k, ?_, ⟨e⟩⟩
  have := e.toLinearEquiv.finrank_eq
  rwa [finrank_alg, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at this

/-- `2^n = k²` forces `n` even and `k = 2^{n/2}`. -/
theorem even_and_eq_of_two_pow_eq_mul_self {k : ℕ} (h : 2 ^ n = k * k) :
    Even n ∧ k = 2 ^ (n / 2) := by
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro k h.symm)
  rw [← pow_add] at h
  have hm : n = m + m := Nat.pow_right_injective le_rfl h
  subst hm
  exact ⟨⟨m, rfl⟩, by rw [← two_mul, Nat.mul_div_cancel_left m two_pos]⟩

/-- The dimension `k` of the simple module (`A ≅ M_k(ℂ)`). -/
noncomputable def repDim (hN : IsUnit (M + Mᵀ).det) : ℕ := (exists_matrix M hN).choose

theorem two_pow_eq_repDim_mul_self (hN : IsUnit (M + Mᵀ).det) :
    2 ^ n = repDim M hN * repDim M hN := (exists_matrix M hN).choose_spec.1

/-- A nondegenerate alternating form over `ZMod 2` forces even rank. -/
theorem even_of_isUnit (hN : IsUnit (M + Mᵀ).det) : Even n :=
  (even_and_eq_of_two_pow_eq_mul_self (two_pow_eq_repDim_mul_self M hN)).1

theorem repDim_eq (hN : IsUnit (M + Mᵀ).det) : repDim M hN = 2 ^ (n / 2) :=
  (even_and_eq_of_two_pow_eq_mul_self (two_pow_eq_repDim_mul_self M hN)).2

/-- The **simple module** `T = ℂ^k` of `A`. -/
def Rep (hN : IsUnit (M + Mᵀ).det) : Type := Fin (repDim M hN) → ℂ

noncomputable instance (hN : IsUnit (M + Mᵀ).det) : AddCommGroup (Rep M hN) :=
  inferInstanceAs (AddCommGroup (Fin (repDim M hN) → ℂ))

noncomputable instance (hN : IsUnit (M + Mᵀ).det) : Module ℂ (Rep M hN) :=
  inferInstanceAs (Module ℂ (Fin (repDim M hN) → ℂ))

instance (hN : IsUnit (M + Mᵀ).det) : FiniteDimensional ℂ (Rep M hN) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin (repDim M hN) → ℂ))

/-- `A ≃ End_ℂ(T)` (Wedderburn–Artin, composed with matrices-as-endomorphisms). -/
noncomputable def repEquiv (hN : IsUnit (M + Mᵀ).det) : alg M ≃ₐ[ℂ] Module.End ℂ (Rep M hN) :=
  (exists_matrix M hN).choose_spec.2.some.trans Matrix.toLinAlgEquiv'

noncomputable instance (hN : IsUnit (M + Mᵀ).det) : Module (alg M) (Rep M hN) :=
  Module.compHom (Rep M hN) (repEquiv M hN : alg M →+* Module.End ℂ (Rep M hN))

theorem smul_def (hN : IsUnit (M + Mᵀ).det) (a : alg M) (v : Rep M hN) :
    a • v = repEquiv M hN a v := rfl

instance (hN : IsUnit (M + Mᵀ).det) : IsScalarTower ℂ (alg M) (Rep M hN) where
  smul_assoc c a v := by
    rw [smul_def, smul_def, map_smul, LinearMap.smul_apply]

theorem finrank_rep (hN : IsUnit (M + Mᵀ).det) :
    Module.finrank ℂ (Rep M hN) = 2 ^ (n / 2) := by
  rw [← repDim_eq M hN]
  exact Module.finrank_fin_fun ℂ

instance (hN : IsUnit (M + Mᵀ).det) : Nontrivial (Rep M hN) := by
  have hk : repDim M hN ≠ 0 := by
    intro h; have := two_pow_eq_repDim_mul_self M hN; rw [h] at this; simp at this
  haveI : Nonempty (Fin (repDim M hN)) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  exact inferInstanceAs (Nontrivial (Fin (repDim M hN) → ℂ))

/-- `T` is a **simple** `A`-module. -/
instance isSimpleModule_rep (hN : IsUnit (M + Mᵀ).det) : IsSimpleModule (alg M) (Rep M hN) := by
  have hE := (isSimpleModule_iff_toSpanSingleton_surjective (R := Module.End ℂ (Rep M hN))
    (M := Rep M hN)).mp inferInstance
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun x hx y => ?_⟩
  obtain ⟨f, hf⟩ := hE.2 x hx y
  refine ⟨(repEquiv M hN).symm f, ?_⟩
  simp only [LinearMap.toSpanSingleton_apply] at hf ⊢
  rw [smul_def, AlgEquiv.apply_symm_apply]
  exact hf

/-- **Uniqueness**: every simple `A`-module (compatible with the `ℂ`-structure) is isomorphic to
`T`, hence has dimension `2^{n/2}`. -/
theorem nonempty_linearEquiv_rep (hN : IsUnit (M + Mᵀ).det) (S : Type*) [AddCommGroup S]
    [Module (alg M) S] [IsSimpleModule (alg M) S] :
    Nonempty (S ≃ₗ[alg M] Rep M hN) := by
  haveI := isSimpleRing_alg M hN
  haveI : IsArtinianRing (alg M) := IsArtinianRing.of_finite ℂ (alg M)
  have hiso := IsSimpleRing.isIsotypic (alg M) (S × Rep M hN)
  let m₁ := LinearMap.range (LinearMap.inl (alg M) S (Rep M hN))
  let m₂ := LinearMap.range (LinearMap.inr (alg M) S (Rep M hN))
  let e₁ : S ≃ₗ[alg M] m₁ := LinearEquiv.ofInjective _ LinearMap.inl_injective
  let e₂ : Rep M hN ≃ₗ[alg M] m₂ := LinearEquiv.ofInjective _ LinearMap.inr_injective
  haveI : IsSimpleModule (alg M) m₁ := IsSimpleModule.congr e₁.symm
  haveI : IsSimpleModule (alg M) m₂ := IsSimpleModule.congr e₂.symm
  obtain ⟨e⟩ := hiso m₂ m₁
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

theorem finrank_of_isSimpleModule (hN : IsUnit (M + Mᵀ).det) (S : Type*) [AddCommGroup S]
    [Module ℂ S] [Module (alg M) S] [IsScalarTower ℂ (alg M) S] [IsSimpleModule (alg M) S] :
    Module.finrank ℂ S = 2 ^ (n / 2) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_rep M hN S
  rw [(e.restrictScalars ℂ).finrank_eq, finrank_rep]


/-- `(-1)^m = sgn (m mod 2)`. -/
theorem neg_one_zpow_eq_sgn (m : ℤ) : (-1 : ℂ) ^ m = sgn (m : ZMod 2) := by
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · rw [(Int.even_iff.mpr h).neg_one_zpow, (ZMod.intCast_zmod_eq_zero_iff_dvd m 2).mpr
      (by omega), sgn_zero]
  · rw [(Int.odd_iff.mpr h).neg_one_zpow, show m = 2 * (m / 2) + 1 by omega]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add, sgn_one]

end VOA.Moonshine.Extraspecial

/-! ## The lattice `L/2L` and the extraspecial module of an even unimodular lattice -/

namespace VOA.IntegralLattice

open Matrix VOA.Moonshine.Extraspecial

variable (L : VOA.IntegralLattice)

/-- The rank index used by the canonical basis `latticeBasis L`. -/
noncomputable def bRank : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ L.carrier)

theorem bRank_eq_rank : L.bRank = L.rank :=
  (Module.finrank_eq_card_chooseBasisIndex ℤ L.carrier).symm

/-- The Gram matrix of `L` in the canonical basis. -/
noncomputable def gramMat : Matrix (Fin L.bRank) (Fin L.bRank) ℤ :=
  Matrix.of fun i j => L.form (latticeBasis L i) (latticeBasis L j)

/-- The cocycle exponent matrix mod 2: the strictly lower-triangular part of the Gram matrix. -/
noncomputable def cocMat : Matrix (Fin L.bRank) (Fin L.bRank) (ZMod 2) :=
  Matrix.of fun i j => if j < i then (L.form (latticeBasis L i) (latticeBasis L j) : ZMod 2) else 0

/-- Reduction `L → L/2L ≅ (ZMod 2)^rank` in the canonical basis. -/
noncomputable def red : L.carrier →+ (Fin L.bRank → ZMod 2) where
  toFun α i := ((latticeBasis L).repr α i : ZMod 2)
  map_zero' := by
    funext i; simp only [map_zero, Finsupp.zero_apply, Pi.zero_apply]; exact Int.cast_zero
  map_add' α β := by ext i; simp

theorem red_apply (α : L.carrier) (i : Fin L.bRank) :
    red L α i = ((latticeBasis L).repr α i : ZMod 2) := rfl

/-- `red` is surjective. -/
theorem red_surjective : Function.Surjective (red L) := by
  intro x
  refine ⟨(latticeBasis L).repr.symm (Finsupp.equivFunOnFinite.symm fun i => ((x i).val : ℤ)), ?_⟩
  ext i
  simp [red_apply]

/-- `ker red = 2L`: the reduction identifies `(ZMod 2)^rank` with `L/2L`. -/
theorem red_eq_zero_iff (α : L.carrier) : red L α = 0 ↔ ∃ γ, α = 2 • γ := by
  constructor
  · intro h
    have hdiv : ∀ i, (2 : ℤ) ∣ (latticeBasis L).repr α i := fun i => by
      have := congrFun h i
      change ((latticeBasis L).repr α i : ZMod 2) = 0 at this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    refine ⟨(latticeBasis L).repr.symm
      (Finsupp.equivFunOnFinite.symm fun i => (latticeBasis L).repr α i / 2), ?_⟩
    apply (latticeBasis L).repr.injective
    ext i
    simp [Int.mul_ediv_cancel' (hdiv i)]
  · rintro ⟨γ, rfl⟩
    ext i
    simp only [red_apply, map_nsmul, Finsupp.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-- **Descent of the cocycle to `L/2L`**: `ε(α,β) = c(ᾱ, β̄)` with `c` the sign of the
lower-triangular Gram form mod 2.  In particular `ε(α,β)` depends only on `α, β mod 2L`. -/
theorem latticeCocycle_eq_coc (α β : L.carrier) :
    latticeCocycle L α β = coc (cocMat L) (red L α) (red L β) := by
  rw [latticeCocycle, cocycle, neg_one_zpow_eq_sgn, coc]
  congr 1
  simp only [cocExp, dotProduct, mulVec, Finset.mul_sum, cocMat, red_apply, of_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1 h2
  · exact absurd h2 h1
  · ring

/-- `ε(α + 2γ, β) = ε(α, β)` and `ε(α, β + 2γ) = ε(α, β)`. -/
theorem latticeCocycle_add_two_nsmul (α β γ : L.carrier) :
    latticeCocycle L (α + 2 • γ) β = latticeCocycle L α β ∧
      latticeCocycle L α (β + 2 • γ) = latticeCocycle L α β := by
  have h2 : red L (2 • γ) = 0 := (red_eq_zero_iff L _).mpr ⟨γ, rfl⟩
  simp only [latticeCocycle_eq_coc, map_add, h2, add_zero, and_self]

/-- For an even lattice, `cocMat + cocMatᵀ` is the Gram matrix mod 2. -/
theorem cocMat_add_transpose (hEven : L.Even) :
    cocMat L + (cocMat L)ᵀ = (gramMat L).map (Int.cast : ℤ → ZMod 2) := by
  ext i j
  simp only [add_apply, transpose_apply, cocMat, gramMat, of_apply, map_apply]
  rcases lt_trichotomy j i with h | rfl | h
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg (lt_irrefl _), add_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hEven _
  · rw [if_neg (by omega), if_pos h, zero_add, form_symm]

/-- For an even **unimodular** lattice the commutator form on `L/2L` is nondegenerate. -/
theorem isUnit_det_cocMat (hEven : L.Even) (hU : IsUnit (gramMat L).det) :
    IsUnit (cocMat L + (cocMat L)ᵀ).det := by
  have h := hU.map (Int.castRingHom (ZMod 2))
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
  rwa [cocMat_add_transpose L hEven]


/-! ### The algebra `A_L = ℂ^ε[L/2L]` and the images `e_α` of lattice elements -/

/-- The image `e_α ∈ A_L = ℂ^ε[L/2L]` of the lattice element `α`. -/
noncomputable def eA (α : L.carrier) : alg (cocMat L) := ⟨op (cocMat L) (red L α), op_mem _ _⟩

theorem coe_eA (α : L.carrier) : (eA L α : Module.End ℂ _) = op (cocMat L) (red L α) := rfl

/-- `e_α e_β = ε(α,β) e_{α+β}` in `A_L`. -/
theorem eA_mul (α β : L.carrier) : eA L α * eA L β = latticeCocycle L α β • eA L (α + β) := by
  apply Subtype.ext
  change op _ _ * op _ _ = latticeCocycle L α β • op _ _
  rw [op_mul, map_add, latticeCocycle_eq_coc]

theorem eA_zero : eA L 0 = 1 := by
  apply Subtype.ext
  change op _ _ = 1
  rw [map_zero, op_zero]

/-- `K = 2L` acts trivially: `e_{α + 2γ} = e_α`. -/
theorem eA_add_two_nsmul (α γ : L.carrier) : eA L (α + 2 • γ) = eA L α := by
  have h2 : red L (2 • γ) = 0 := (red_eq_zero_iff L _).mpr ⟨γ, rfl⟩
  simp only [eA, map_add, h2, add_zero]

/-- **θ-compatibility**: `e_{-α} = e_α` in `A_L` (since `-α ≡ α mod 2L`). -/
theorem eA_neg (α : L.carrier) : eA L (-α) = eA L α := by
  have := eA_add_two_nsmul L (-α) α
  rw [two_nsmul, neg_add_cancel_left] at this
  exact this.symm

/-- `dim_ℂ A_L = 2^{rank L}`. -/
theorem finrank_alg_cocMat : Module.finrank ℂ (alg (cocMat L)) = 2 ^ L.rank := by
  rw [finrank_alg, bRank_eq_rank]

/-- The `e_α` span `A_L`. -/
theorem span_eA : Submodule.span ℂ (Set.range (eA L)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  have hx : (⟨f, hf⟩ : alg (cocMat L))
      = ∑ v, f (Pi.single 0 1) v • (⟨op (cocMat L) v, op_mem _ _⟩ : alg (cocMat L)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [Subalgebra.coe_smul]
    exact eq_sum_coeff _ hf
  rw [hx]
  refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨α, rfl⟩ := red_surjective L v
  exact ⟨α, rfl⟩

section Unimodular

variable (hEven : L.Even) (hU : IsUnit (gramMat L).det)
include hEven hU

/-- `A_L` is a simple ring (even unimodular `L`). -/
theorem isSimpleRing_alg_cocMat : IsSimpleRing (alg (cocMat L)) :=
  isSimpleRing_alg _ (isUnit_det_cocMat L hEven hU)

/-- An even unimodular lattice has even rank (the commutator form on `L/2L` is a nondegenerate
alternating form). -/
theorem even_rank_of_unimodular : _root_.Even L.rank := by
  rw [← bRank_eq_rank]; exact even_of_isUnit _ (isUnit_det_cocMat L hEven hU)

/-- **The extraspecial module** `T_L`: the simple `A_L`-module. -/
noncomputable abbrev ExtraT : Type := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)

/-- `dim T_L = 2^{rank L / 2}`. -/
theorem finrank_extraT : Module.finrank ℂ (ExtraT L hEven hU) = 2 ^ (L.rank / 2) := by
  rw [finrank_rep, bRank_eq_rank]

/-- Every simple `A_L`-module has dimension `2^{rank L / 2}`. -/
theorem finrank_of_isSimpleModule_alg_cocMat (S : Type*) [AddCommGroup S] [Module ℂ S]
    [Module (alg (cocMat L)) S] [IsScalarTower ℂ (alg (cocMat L)) S]
    [IsSimpleModule (alg (cocMat L)) S] : Module.finrank ℂ S = 2 ^ (L.rank / 2) := by
  rw [finrank_of_isSimpleModule _ (isUnit_det_cocMat L hEven hU) S, bRank_eq_rank]

/-- The operator of `e_α` on `T_L`. -/
noncomputable def eT (α : L.carrier) : Module.End ℂ (ExtraT L hEven hU) :=
  repEquiv _ (isUnit_det_cocMat L hEven hU) (eA L α)

theorem eT_apply (α : L.carrier) (v : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    eT L hEven hU α v = eA L α • v := rfl

/-- **The relations on `T_L`**: `e_α e_β = ε(α,β) e_{α+β}`. -/
theorem eT_mul (α β : L.carrier) :
    eT L hEven hU α * eT L hEven hU β = latticeCocycle L α β • eT L hEven hU (α + β) := by
  rw [eT, eT, eT, ← map_mul, eA_mul, map_smul]

instance isSimpleModule_extraT :
    IsSimpleModule (alg (cocMat L)) (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :=
  isSimpleModule_rep _ _

theorem eT_zero : eT L hEven hU 0 = 1 := by rw [eT, eA_zero, map_one]

/-- `e_{-α}` and `e_α` act identically on `T_L` (θ-compatibility; `K` acts trivially). -/
theorem eT_neg (α : L.carrier) : eT L hEven hU (-α) = eT L hEven hU α := by
  rw [eT, eT, eA_neg]

theorem eT_add_two_nsmul (α γ : L.carrier) : eT L hEven hU (α + 2 • γ) = eT L hEven hU α := by
  rw [eT, eT, eA_add_two_nsmul]

end Unimodular

end VOA.IntegralLattice

/-! ## The Leech lattice: `dim T = 4096` -/

namespace VOA.Moonshine

open IntegralLattice

/-- The Leech lattice is unimodular in the form used here. -/
theorem leech_isUnit_det_gramMat : IsUnit (gramMat leech).det := by
  have h := Leech.lattice_isUnimodular
  rw [_root_.IntegralLattice.IsUnimodular,
    ← _root_.IntegralLattice.det_eq_gram_det _ (latticeBasis leech)] at h
  exact h

/-- **The FLM module `T` for the Leech lattice**: the simple module of `ℂ^ε[Λ/2Λ]`. -/
noncomputable abbrev leechT : Type := ExtraT leech leech_even leech_isUnit_det_gramMat

/-- `dim T = 2^12 = 4096`. -/
theorem finrank_leechT : Module.finrank ℂ leechT = 4096 := by
  rw [finrank_extraT, leech_rank]; norm_num

end VOA.Moonshine

