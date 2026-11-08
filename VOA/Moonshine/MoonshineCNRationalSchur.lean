/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
# Schur's span formula and descent through rational functionals

Two pieces of linear algebra behind the rationality of `Aut V♮` on `V♮₂`
(`Notes/monster_aut/RATIONALITY.md`, §2.2–§2.3).

**Schur's span formula.** Let `σ : S →* M_n(K)` be a representation of a finite group, `E` an
idempotent commuting with `σ(S)` with `tr E ≠ 0`, and suppose the commutant of `σ(S)` is scalar on
the image of `E`: every `T` commuting with `σ(S)` has `E T E ∈ K·E`. Then for every `Y`,

  `Σ_s tr(σ(s⁻¹) E Y) · σ(s) E = (|S| / tr E) · E Y E`.

The proof is the classical one: the group average `Σ_s σ(s) E X E σ(s⁻¹)` commutes with `σ(S)` and
is cut out by `E`, hence is `(|S| tr(EX) / tr E) · E`; reading it on matrix units gives the
orthogonality relation of the matrix coefficients, which is the span formula.

**Descent.** A complex matrix `H` with `H.map f = f(1) · Z` for every `ℚ`-linear functional
`f : ℂ → ℚ` (applied entrywise) is the rational matrix `Z`. Applying `f` entrywise commutes with
multiplication by rational matrices and with the trace against a rational matrix.

**Rationality criterion** (`eq_map_ratCast_of_rational_traces`). Over `K = ℚ`: if all the traces
`tr(σ(s⁻¹) E H)` are rational, then `E H E` is the rational matrix
`(tr E / |S|) Σ_s tr(σ(s⁻¹) E H) σ(s) E`. This is the matrix form of Galois descent, with the field
automorphisms of `ℂ` replaced by `ℚ`-linear functionals.

## Main results
* `groupAverage_commute`, ⭐ `groupAverage_eq_smul`.
* ⭐ `schur_span_formula`.
* ⭐ `eq_map_ratCast_of_forall_dual`, `map_dual_mul_mul`, `trace_mul_map_dual`.
* ⭐ `eq_map_ratCast_of_rational_traces`.
-/

namespace VOA.Moonshine.Rationality

open Matrix

section Schur

variable {K n S : Type*} [Field K] [Fintype n] [DecidableEq n] [Group S] [Fintype S]

/-- The group average `Σ_s σ(s) X σ(s⁻¹)` commutes with every `σ(t)`. -/
theorem groupAverage_commute (σ : S →* Matrix n n K) (X : Matrix n n K) (t : S) :
    (∑ s, σ s * X * σ s⁻¹) * σ t = σ t * ∑ s, σ s * X * σ s⁻¹ := by
  have hinv : σ t⁻¹ * σ t = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft t⁻¹) _ _ fun s => ?_
  have hs : σ s = σ t * σ (t⁻¹ * s) := by rw [← map_mul, mul_inv_cancel_left]
  have hs' : σ s⁻¹ = σ (t⁻¹ * s)⁻¹ * σ t⁻¹ := by
    rw [← map_mul, mul_inv_rev, inv_inv, mul_inv_cancel_right]
  change σ s * X * σ s⁻¹ * σ t = σ t * (σ (t⁻¹ * s) * X * σ (t⁻¹ * s)⁻¹)
  rw [hs, hs']
  simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]

/-- `(M · e_{jk} · N)_{il} = M_{ij} N_{kl}` for the matrix unit `e_{jk}`. -/
theorem mul_single_mul_apply (M N : Matrix n n K) (i j k l : n) :
    (M * single j k (1 : K) * N) i l = M i j * N k l := by
  have h1 : ∀ a, (M * single j k (1 : K)) i a = if a = k then M i j else 0 := by
    intro a
    by_cases ha : a = k
    · subst ha
      rw [mul_single_apply_same, mul_one, if_pos rfl]
    · rw [mul_single_apply_of_ne _ _ _ _ _ ha, if_neg ha]
  rw [Matrix.mul_apply]
  simp_rw [h1, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]

/-- ⭐ **Schur averaging.** If `E` is an idempotent commuting with `σ(S)`, `tr E ≠ 0`, and every
matrix commuting with `σ(S)` is a scalar on the image of `E`, then
`Σ_s σ(s) E X E σ(s⁻¹) = (|S| tr(EX) / tr E) · E`. -/
theorem groupAverage_eq_smul (σ : S →* Matrix n n K) (E : Matrix n n K) (hE : E * E = E)
    (hEσ : ∀ s, E * σ s = σ s * E) (hr : E.trace ≠ 0)
    (hirr : ∀ T : Matrix n n K, (∀ s, T * σ s = σ s * T) → ∃ c : K, E * T * E = c • E)
    (X : Matrix n n K) :
    ∑ s, σ s * E * X * E * σ s⁻¹
      = ((Fintype.card S : K) * (E * X).trace / E.trace) • E := by
  have hE' : ∀ Z : Matrix n n K, E * (E * Z) = E * Z := fun Z => by
    rw [← Matrix.mul_assoc, hE]
  set A : Matrix n n K := ∑ s, σ s * (E * X * E) * σ s⁻¹ with hA
  have hAeq : ∑ s, σ s * E * X * E * σ s⁻¹ = A := by
    rw [hA]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Matrix.mul_assoc]
  have hAc : ∀ t, A * σ t = σ t * A := groupAverage_commute σ (E * X * E)
  have hEAE : E * A * E = A := by
    rw [hA, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h1 : σ s⁻¹ * E = E * σ s⁻¹ := (hEσ s⁻¹).symm
    calc E * (σ s * (E * X * E) * σ s⁻¹) * E
        = (E * σ s) * (E * X * E) * (σ s⁻¹ * E) := by simp only [Matrix.mul_assoc]
      _ = σ s * (E * (E * (X * (E * (E * σ s⁻¹))))) := by
          rw [hEσ s, h1]; simp only [Matrix.mul_assoc]
      _ = σ s * (E * X * E) * σ s⁻¹ := by
          rw [hE', hE']; simp only [Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := hirr A hAc
  rw [hEAE] at hc
  have htr : A.trace = (Fintype.card S : K) * (E * X).trace := by
    rw [hA, Matrix.trace_sum]
    have hterm : ∀ s, (σ s * (E * X * E) * σ s⁻¹).trace = (E * X).trace := by
      intro s
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hE]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc' : c = (Fintype.card S : K) * (E * X).trace / E.trace := by
    rw [eq_div_iff hr, ← htr, hc, Matrix.trace_smul, smul_eq_mul]
  rw [hAeq, hc, hc']

/-- **Orthogonality of matrix coefficients**, the entry form of `groupAverage_eq_smul` on the matrix
unit `e_{jk}`: `Σ_s (σ(s)E)_{ij} (Eσ(s⁻¹))_{kl} = (|S|/tr E) E_{kj} E_{il}`. -/
theorem sum_mul_coeff_eq (σ : S →* Matrix n n K) (E : Matrix n n K) (hE : E * E = E)
    (hEσ : ∀ s, E * σ s = σ s * E) (hr : E.trace ≠ 0)
    (hirr : ∀ T : Matrix n n K, (∀ s, T * σ s = σ s * T) → ∃ c : K, E * T * E = c • E)
    (i j k l : n) :
    ∑ s, (σ s * E) i j * (E * σ s⁻¹) k l
      = (Fintype.card S : K) / E.trace * (E k j * E i l) := by
  have h := congrFun (congrFun (groupAverage_eq_smul σ E hE hEσ hr hirr (single j k 1)) i) l
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace_mul_single] at h
  have hterm : ∀ s, (σ s * E * single j k (1 : K) * E * σ s⁻¹) i l
      = (σ s * E) i j * (E * σ s⁻¹) k l := by
    intro s
    rw [show σ s * E * single j k (1 : K) * E * σ s⁻¹
        = σ s * E * single j k (1 : K) * (E * σ s⁻¹) by simp only [Matrix.mul_assoc],
      mul_single_mul_apply]
  simp only [hterm] at h
  rw [h]
  simp only [MulOpposite.op_one, one_smul]
  ring

/-- ⭐ **Schur's span formula.** With `E` an idempotent commuting with `σ(S)`, `tr E ≠ 0`, and the
commutant of `σ(S)` scalar on the image of `E`:
`Σ_s tr(σ(s⁻¹) E Y) · σ(s) E = (|S| / tr E) · E Y E` for every `Y`. -/
theorem schur_span_formula (σ : S →* Matrix n n K) (E : Matrix n n K) (hE : E * E = E)
    (hEσ : ∀ s, E * σ s = σ s * E) (hr : E.trace ≠ 0)
    (hirr : ∀ T : Matrix n n K, (∀ s, T * σ s = σ s * T) → ∃ c : K, E * T * E = c • E)
    (Y : Matrix n n K) :
    ∑ s, (σ s⁻¹ * E * Y).trace • (σ s * E)
      = ((Fintype.card S : K) / E.trace) • (E * Y * E) := by
  set κ : K := (Fintype.card S : K) / E.trace
  have key : ∀ i j k l, ∑ s, (σ s * E) i j * (E * σ s⁻¹) k l = κ * (E k j * E i l) :=
    sum_mul_coeff_eq σ E hE hEσ hr hirr
  have htr : ∀ s, (σ s⁻¹ * E * Y).trace = ∑ k, ∑ j, (E * σ s⁻¹) k j * Y j k := by
    intro s
    rw [← (hEσ s⁻¹), Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
  ext i l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, htr]
  calc ∑ s, (∑ k, ∑ j, (E * σ s⁻¹) k j * Y j k) * (σ s * E) i l
      = ∑ s, ∑ k, ∑ j, Y j k * ((σ s * E) i l * (E * σ s⁻¹) k j) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ k, ∑ s, ∑ j, Y j k * ((σ s * E) i l * (E * σ s⁻¹) k j) := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ s, Y j k * ((σ s * E) i l * (E * σ s⁻¹) k j) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ j, Y j k * ∑ s, (σ s * E) i l * (E * σ s⁻¹) k j := by
        simp only [Finset.mul_sum]
    _ = ∑ k, ∑ j, Y j k * (κ * (E k l * E i j)) := by
        simp only [key]
    _ = κ * (E * Y * E) i l := by
        simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        ring

end Schur

/-! ## Descent through `ℚ`-linear functionals -/

section Descent

variable {l m n o : Type*}

theorem dual_ratCast_mul (f : ℂ →ₗ[ℚ] ℚ) (q : ℚ) (z : ℂ) : f ((q : ℂ) * z) = q * f z := by
  rw [← Rat.smul_def, map_smul, smul_eq_mul]

theorem dual_mul_ratCast (f : ℂ →ₗ[ℚ] ℚ) (q : ℚ) (z : ℂ) : f (z * (q : ℂ)) = f z * q := by
  rw [mul_comm, dual_ratCast_mul, mul_comm]

/-- ⭐ **Descent.** A complex matrix `H` with `H.map f = f(1) · Z` for every `ℚ`-linear functional
`f : ℂ → ℚ` is the rational matrix `Z`. -/
theorem eq_map_ratCast_of_forall_dual (H : Matrix m n ℂ) (Z : Matrix m n ℚ)
    (h : ∀ f : ℂ →ₗ[ℚ] ℚ, H.map f = f 1 • Z) : H = Z.map (Rat.castHom ℂ) := by
  ext i j
  rw [Matrix.map_apply, Rat.coe_castHom, ← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).1 fun f => ?_
  have hf := congrFun (congrFun (h f) i) j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hf
  rw [map_sub, hf, show ((Z i j : ℚ) : ℂ) = (Z i j : ℂ) * 1 by rw [mul_one], dual_ratCast_mul]
  ring

/-- Applying a `ℚ`-linear functional entrywise commutes with multiplication by rational matrices. -/
theorem map_dual_mul_mul [Fintype m] [Fintype n] (f : ℂ →ₗ[ℚ] ℚ) (R : Matrix l m ℚ)
    (X : Matrix m n ℂ) (R' : Matrix n o ℚ) :
    (R.map (Rat.castHom ℂ) * X * R'.map (Rat.castHom ℂ)).map f = R * X.map f * R' := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Rat.coe_castHom, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [dual_mul_ratCast, dual_ratCast_mul]

/-- The trace against a rational matrix commutes with applying a `ℚ`-linear functional
entrywise: `tr(R · X.map f) = f (tr(R · X))`. -/
theorem trace_mul_map_dual [Fintype m] [Fintype n] (f : ℂ →ₗ[ℚ] ℚ) (R : Matrix m n ℚ)
    (X : Matrix n m ℂ) :
    (R * X.map f).trace = f (R.map (Rat.castHom ℂ) * X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum,
    Rat.coe_castHom, dual_ratCast_mul]

end Descent

/-! ## The rationality criterion -/

section Criterion

variable {n S : Type*} [Fintype n] [DecidableEq n] [Group S] [Fintype S]

/-- ⭐ **Rationality from rational traces and an absolutely irreducible rational group.** Let
`σ : S →* M_n(ℚ)` be a rational representation of a finite group, `E` a rational idempotent
commuting with `σ(S)` with `tr E ≠ 0`, and assume the commutant of `σ(S)` is scalar on the image
of `E`. If `H` is a complex matrix all of whose traces `tr(σ(s⁻¹) E H)` are rational numbers
`q s`, then `E H E` is the rational matrix `(tr E / |S|) Σ_s q(s) σ(s) E`. -/
theorem eq_map_ratCast_of_rational_traces (σ : S →* Matrix n n ℚ) (E : Matrix n n ℚ)
    (hE : E * E = E) (hEσ : ∀ s, E * σ s = σ s * E) (hr : E.trace ≠ 0)
    (hirr : ∀ T : Matrix n n ℚ, (∀ s, T * σ s = σ s * T) → ∃ c : ℚ, E * T * E = c • E)
    (H : Matrix n n ℂ) (q : S → ℚ)
    (hq : ∀ s, ((σ s⁻¹ * E).map (Rat.castHom ℂ) * H).trace = (q s : ℂ)) :
    E.map (Rat.castHom ℂ) * H * E.map (Rat.castHom ℂ)
      = ((E.trace / Fintype.card S) • ∑ s, q s • (σ s * E)).map (Rat.castHom ℂ) := by
  apply eq_map_ratCast_of_forall_dual
  intro f
  have hcard : (Fintype.card S : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hspan := schur_span_formula σ E hE hEσ hr hirr (H.map f)
  have htr : ∀ s, (σ s⁻¹ * E * H.map f).trace = q s * f 1 := by
    intro s
    rw [trace_mul_map_dual, hq s, show ((q s : ℚ) : ℂ) = (q s : ℂ) * 1 by rw [mul_one],
      dual_ratCast_mul]
  simp only [htr] at hspan
  rw [map_dual_mul_mul]
  have hEHE : E * H.map f * E
      = (E.trace / Fintype.card S) • ∑ s, (q s * f 1) • (σ s * E) := by
    rw [hspan, smul_smul, div_mul_div_comm, mul_comm E.trace, div_self (mul_ne_zero hcard hr),
      one_smul]
  rw [hEHE, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [smul_smul]
  congr 1
  ring

end Criterion

end VOA.Moonshine.Rationality
