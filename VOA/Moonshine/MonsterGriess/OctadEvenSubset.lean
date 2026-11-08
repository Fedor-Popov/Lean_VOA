/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Lagrangian.lean
  CFSG/Monster/FourierTriality.lean
  CFSG/Monster/Octad/EvenSubset.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.VisibleAction
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NoncommRing

/-!
# Axiom's Monster port (triality closure): Fourier/sign triality on a binary quadratic space; even subsets of an octad

* `fourierMatrix b m`, `signMatrix q` and `binary_quadratic_fourier_triality` — for a nondegenerate
  binary quadratic space `E` of dimension `2m` with Gauss sum `2^m`, the Fourier matrix `H` and the
  sign matrix `D` satisfy `H² = D² = 1`, `HDH = DHD`, `(HD)³ = 1` (dyadic entries);
* `Octad.EvenQuot d` — even subsets of an 8-set `d` modulo `d`, a 6-dimensional quadratic space
  (`quadForm d`), with `eight_point_even_subset_quadratic_space`.

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Octad` ↦ `VOA.Moonshine.MonsterGriess`, `….Octad`.
  Module-system syntax dropped; `public noncomputable section` ↦ `noncomputable section`.  Bodies
  verbatim except as listed.
* `sgn_mul_self` (source: `FourierTriality.lean`) is already ported in `VisibleAction.lean` and is
  used, not repeated.
* Drift: `dite_eq_left h` ↦ `dif_pos h`; `ite_eq_left h`/`ite_eq_right h` ↦ `if_pos h`/`if_neg h`.
* From `Lagrangian.lean` only `symm_of_alternating`, `sum_sgn_of_not_perp`, `sub_eq_add_zmod_two`
  are ported (the Lagrangian functions `fourier`, `signOp`, `lagrangianFun` are not reached).
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

open Module Matrix

/-! ### From `CFSG/Monster/Lagrangian.lean` -/

section Lagrangian

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]

omit [Fintype E] in
theorem symm_of_alternating {b : LinearMap.BilinForm (ZMod 2) E} (halt : ∀ v, b v v = 0)
    (x y : E) : b x y = b y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  have h' : b y x = -b x y := eq_neg_of_add_eq_zero_left h
  rw [ZMod.neg_eq_self_mod_two] at h'
  exact h'.symm

theorem sum_sgn_of_not_perp (b : LinearMap.BilinForm (ZMod 2) E) (K : Submodule (ZMod 2) E)
    [DecidablePred (· ∈ K)] {w : E} {k₀ : E} (hk₀ : k₀ ∈ K) (hne : b w k₀ ≠ 0) :
    ∑ k : K, sgn (b w k) = 0 := by
  have h1 : b w k₀ = 1 := by
    have : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact this _ hne
  have hshift : ∑ k : K, sgn (b w k) = ∑ k : K, sgn (b w ((k : E) + k₀)) :=
    (Fintype.sum_equiv (Equiv.addRight (⟨k₀, hk₀⟩ : K)) _ _ fun k => by simp).symm
  simp only [map_add, sgn_add, h1] at hshift
  have : sgn 1 = -1 := rfl
  rw [this] at hshift
  simp only [mul_neg, mul_one, Finset.sum_neg_distrib] at hshift
  linarith

omit [Fintype E] in
theorem sub_eq_add_zmod_two (v a : E) : v - a = v + a := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right]
  rw [← two_smul (ZMod 2) a]
  simp [show (2 : ZMod 2) = 0 from rfl]

end Lagrangian

/-! ### From `CFSG/Monster/FourierTriality.lean` -/

noncomputable section FourierTriality

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] [DecidableEq E]

def fourierMatrix (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) : Matrix E E ℚ :=
  fun u v => ((2 : ℚ) ^ m)⁻¹ * sgn (b u v)

def signMatrix (q : E → ZMod 2) : Matrix E E ℚ := Matrix.diagonal fun u => sgn (q u)

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem signMatrix_mul_self (q : E → ZMod 2) : signMatrix q * signMatrix q = 1 := by
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  simp only [sgn_mul_self]
  exact Matrix.diagonal_one

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] in
theorem signMatrix_transpose (q : E → ZMod 2) : (signMatrix q)ᵀ = signMatrix q :=
  Matrix.diagonal_transpose _

omit [Fintype E] [DecidableEq E] in
theorem fourierMatrix_transpose {b : LinearMap.BilinForm (ZMod 2) E} (halt : ∀ v, b v v = 0)
    (m : ℕ) : (fourierMatrix b m)ᵀ = fourierMatrix b m := by
  ext u v
  simp [fourierMatrix, symm_of_alternating halt u v]

theorem sum_sgn_bilin {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.Nondegenerate) (w : E) :
    ∑ v, sgn (b w v) = if w = 0 then (Fintype.card E : ℚ) else 0 := by
  classical
  split_ifs with h
  · subst h; simp [sgn]
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, b w v₀ ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (hb.1 w hc)
    have := sum_sgn_of_not_perp b ⊤ (Submodule.mem_top (x := v₀)) hv₀
    rw [← this]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun x => Submodule.mem_top) _ _
      fun x => rfl).symm

section Quadratic

variable (Q : QuadraticForm (ZMod 2) E)

omit [Fintype E] [DecidableEq E] in
theorem polarBilin_self (v : E) : QuadraticMap.polarBilin Q v v = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  have : (2 : ZMod 2) = 0 := rfl
  simp [this]

omit [Fintype E] [DecidableEq E] in
theorem quad_add (u v : E) : Q (u + v) = Q u + Q v + QuadraticMap.polarBilin Q u v := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

omit [Fintype E] [DecidableEq E] in
theorem polarBilin_symm (u v : E) :
    QuadraticMap.polarBilin Q u v = QuadraticMap.polarBilin Q v u :=
  symm_of_alternating (polarBilin_self Q) u v

theorem fourierMatrix_mul_self (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) :
    fourierMatrix (QuadraticMap.polarBilin Q) m * fourierMatrix (QuadraticMap.polarBilin Q) m =
      1 := by
  ext u w
  simp only [Matrix.mul_apply, fourierMatrix]
  have h : ∀ v, ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q u v) *
      (((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q v w)) =
      ((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q (u + w) v) := by
    intro v
    rw [map_add, LinearMap.add_apply, sgn_add, polarBilin_symm Q v w]
    ring
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum, sum_sgn_bilin hb]
  by_cases huw : u = w
  · subst huw
    have : u + u = 0 := by rw [← sub_eq_add_zmod_two, sub_self]
    simp only [this, ite_true, Matrix.one_apply_eq, hE]
    have h2 : ((2 ^ (2 * m) : ℕ) : ℚ) = (2 : ℚ) ^ m * (2 : ℚ) ^ m := by
      push_cast
      rw [two_mul, pow_add]
    rw [h2]
    field_simp
  · have : u + w ≠ 0 := fun h => huw (by rw [← sub_eq_zero, sub_eq_add_zmod_two]; exact h)
    simp only [this, ite_false, Matrix.one_apply_ne huw, mul_zero]

theorem fourier_sign_braid {m : ℕ} (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q *
        fourierMatrix (QuadraticMap.polarBilin Q) m =
      signMatrix Q * fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q := by
  ext u w
  rw [Matrix.mul_apply, signMatrix]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, fourierMatrix]
  have h : ∀ v, ((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q u v) * sgn (Q v) *
      (((2 : ℚ) ^ m)⁻¹ * sgn (QuadraticMap.polarBilin Q v w)) =
      ((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (Q (u + w)) * sgn (Q (v + (u + w))) := by
    intro v
    have e1 : Q (v + (u + w)) = Q v + Q (u + w) +
        (QuadraticMap.polarBilin Q v u + QuadraticMap.polarBilin Q v w) := by
      rw [quad_add Q v (u + w), (QuadraticMap.polarBilin Q v).map_add u w]
    rw [e1, sgn_add, sgn_add, sgn_add, polarBilin_symm Q v u]
    have hsq := sgn_mul_self (Q (u + w))
    linear_combination (-(((2 : ℚ) ^ m)⁻¹ * ((2 : ℚ) ^ m)⁻¹ * sgn (Q v) *
      sgn (QuadraticMap.polarBilin Q u v) * sgn (QuadraticMap.polarBilin Q v w))) * hsq
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum]
  rw [show ∑ v, sgn (Q (v + (u + w))) = ∑ v, sgn (Q v) from
    Fintype.sum_equiv (Equiv.addRight (u + w)) _ _ (fun v => rfl), hgauss]
  rw [quad_add Q u w, sgn_add, sgn_add]
  field_simp

theorem fourier_sign_cube (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) ^ 3 = 1 := by
  set H := fourierMatrix (QuadraticMap.polarBilin Q) m
  set D := signMatrix Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hD : D * D = 1 := signMatrix_mul_self Q
  have hbr : H * D * H = D * H * D := fourier_sign_braid Q hgauss
  calc (H * D) ^ 3 = (H * D * H) * (D * H * D) := by
        rw [pow_succ, pow_two]; simp only [Matrix.mul_assoc]
    _ = (D * H * D) * (D * H * D) := by rw [hbr]
    _ = 1 := by
        calc D * H * D * (D * H * D) = D * H * (D * D) * H * D := by simp only [Matrix.mul_assoc]
          _ = D * (H * H) * D := by rw [hD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hH, Matrix.mul_one, hD]

theorem trace_fourier_sign {m : ℕ} (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    Matrix.trace (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) = 1 := by
  simp only [Matrix.trace, Matrix.diag, signMatrix, Matrix.mul_diagonal, fourierMatrix,
    polarBilin_self, sgn_zero, mul_one]
  rw [← Finset.mul_sum, hgauss]
  field_simp

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem toLin'_pow_eq (M : Matrix E E ℚ) (n : ℕ) :
    Matrix.toLin' (M ^ n) = (Matrix.toLin' M) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ n ih => rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ]; rfl

theorem fourier_sign_sq (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) ^ 2 =
      signMatrix Q * fourierMatrix (QuadraticMap.polarBilin Q) m := by
  set H := fourierMatrix (QuadraticMap.polarBilin Q) m
  set D := signMatrix Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hbr : H * D * H = D * H * D := fourier_sign_braid Q hgauss
  calc (H * D) ^ 2 = H * (D * H * D) := by rw [pow_two]; simp only [Matrix.mul_assoc]
    _ = H * (H * D * H) := by rw [hbr]
    _ = D * H := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, Matrix.one_mul]

theorem finrank_ker_fourier_sign_sub_one (hb : (QuadraticMap.polarBilin Q).Nondegenerate)
    {m : ℕ} (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    finrank ℚ (LinearMap.ker (Matrix.toLin'
      (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q - 1))) =
      (2 ^ (2 * m) + 2) / 3 := by
  set τ := fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q with hτdef
  have h3 : τ ^ 3 = 1 := fourier_sign_cube Q hb hE hgauss
  have htr : Matrix.trace τ = 1 := trace_fourier_sign Q hgauss
  have htr2 : Matrix.trace (τ ^ 2) = 1 := by
    rw [fourier_sign_sq Q hb hE hgauss, Matrix.trace_mul_comm, ← hτdef, htr]
  set T : (E → ℚ) →ₗ[ℚ] (E → ℚ) := Matrix.toLin' τ with hT
  have hT3 : T ^ 3 = 1 := by
    rw [hT, ← toLin'_pow_eq, h3, Matrix.toLin'_one]
    rfl
  set P : (E → ℚ) →ₗ[ℚ] (E → ℚ) := (3 : ℚ)⁻¹ • (1 + T + T ^ 2) with hP
  have hPidem : IsIdempotentElem P := by
    have hT4 : T ^ 4 = T := by rw [pow_succ, hT3, one_mul]
    show P * P = P
    rw [hP, smul_mul_smul_comm]
    have : (1 + T + T ^ 2) * (1 + T + T ^ 2) = (3 : ℚ) • (1 + T + T ^ 2) := by
      have e : (1 + T + T ^ 2) * (1 + T + T ^ 2) = 1 + 2 • T + 3 • T ^ 2 + 2 • T ^ 3 + T ^ 4 := by
        noncomm_ring
      rw [e, hT3, hT4]
      rw [← Nat.cast_smul_eq_nsmul ℚ 2, ← Nat.cast_smul_eq_nsmul ℚ 3]
      module
    rw [this, smul_smul]
    norm_num
  have hrange : LinearMap.range P = LinearMap.ker (T - 1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      show (T * P) y = P y
      rw [hP, mul_smul_comm]
      congr 1
      have : T * (1 + T + T ^ 2) = 1 + T + T ^ 2 := by
        have e : T * (1 + T + T ^ 2) = T + T ^ 2 + T ^ 3 := by noncomm_ring
        rw [e, hT3]
        abel
      rw [this]
    · intro hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      refine ⟨x, ?_⟩
      have hx2 : (T ^ 2) x = x := by rw [pow_two, Module.End.mul_apply, hx, hx]
      rw [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        hx, hx2]
      module
  have hker : LinearMap.ker (Matrix.toLin' (τ - 1)) = LinearMap.ker (T - 1) := by
    rw [map_sub, Matrix.toLin'_one]
    rfl
  have htrace : LinearMap.trace ℚ (E → ℚ) P = finrank ℚ (LinearMap.range P) :=
    LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range P hPidem)
  have htrP : LinearMap.trace ℚ (E → ℚ) P = ((2 : ℚ) ^ (2 * m) + 2) / 3 := by
    rw [hP, map_smul, map_add, map_add, LinearMap.trace_one, hT, ← toLin'_pow_eq τ 2]
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ E), LinearMap.trace_eq_matrix_trace ℚ
      (Pi.basisFun ℚ E)]
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin',
      htr, htr2]
    rw [Module.finrank_fintype_fun_eq_card, hE]
    push_cast
    ring
  rw [hker, ← hrange]
  have hq : (finrank ℚ (LinearMap.range P) : ℚ) = ((2 : ℚ) ^ (2 * m) + 2) / 3 := by
    rw [← htrace, htrP]
  have hnat : 3 * finrank ℚ (LinearMap.range P) = 2 ^ (2 * m) + 2 := by
    have : (3 * finrank ℚ (LinearMap.range P) : ℚ) = ((2 ^ (2 * m) + 2 : ℕ) : ℚ) := by
      push_cast
      rw [hq]
      ring
    exact_mod_cast this
  omega

theorem orderOf_fourier_sign (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : 1 ≤ m) (hE : Fintype.card E = 2 ^ (2 * m)) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    orderOf (fourierMatrix (QuadraticMap.polarBilin Q) m * signMatrix Q) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (fourier_sign_cube Q hb hE hgauss) fun h1 => ?_
  have htr := trace_fourier_sign Q hgauss
  rw [h1, Matrix.trace_one, hE] at htr
  have : (2 : ℕ) ^ (2 * m) ≥ 4 := by
    calc (2 : ℕ) ^ (2 * m) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have h' : ((2 ^ (2 * m) : ℕ) : ℚ) = 1 := htr
  have : (2 ^ (2 * m) : ℕ) = 1 := by exact_mod_cast h'
  omega

end Quadratic

theorem sgn_mem_dyadic (t : ZMod 2) : sgn t ∈ dyadic := by
  unfold sgn
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem inv_two_pow_mem_dyadic (m : ℕ) : ((2 : ℚ) ^ m)⁻¹ ∈ dyadic := by
  refine mem_dyadic.2 ⟨m, ?_⟩
  have : ((2 : ℚ) ^ m)⁻¹ = ((2 ^ m : ℕ) : ℚ)⁻¹ := by push_cast; rfl
  rw [this, Rat.inv_natCast_den]
  split_ifs <;> simp

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] [DecidableEq E] in
theorem fourierMatrix_mem_dyadic' {b : E → E → ZMod 2} (m : ℕ) (u v : E) :
    ((2 : ℚ) ^ m)⁻¹ * sgn (b u v) ∈ dyadic :=
  dyadic.mul_mem (inv_two_pow_mem_dyadic m) (sgn_mem_dyadic _)

omit [Fintype E] [DecidableEq E] in
theorem fourierMatrix_mem_dyadic (b : LinearMap.BilinForm (ZMod 2) E) (m : ℕ) (u v : E) :
    fourierMatrix b m u v ∈ dyadic :=
  fourierMatrix_mem_dyadic' (b := fun x y => b x y) m u v

omit [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] in
theorem signMatrix_mem_dyadic (q : E → ZMod 2) (u v : E) : signMatrix q u v ∈ dyadic := by
  unfold signMatrix Matrix.diagonal
  simp only [Matrix.of_apply]
  split_ifs
  · exact sgn_mem_dyadic _
  · exact dyadic.zero_mem

omit [AddCommGroup E] [Module (ZMod 2) E] [DecidableEq E] in
theorem mul_mem_dyadic {M N : Matrix E E ℚ} (hM : ∀ u v, M u v ∈ dyadic)
    (hN : ∀ u v, N u v ∈ dyadic) (u v : E) : (M * N) u v ∈ dyadic := by
  rw [Matrix.mul_apply]
  exact dyadic.sum_mem fun w _ => dyadic.mul_mem (hM u w) (hN w v)

omit [AddCommGroup E] [Module (ZMod 2) E] [DecidableEq E] in
theorem vecMul_mem_dyadic {M : Matrix E E ℚ} (hM : ∀ u v, M u v ∈ dyadic) {x : E → ℚ}
    (hx : ∀ u, x u ∈ dyadic) (v : E) : Matrix.vecMul x M v ∈ dyadic := by
  simp only [Matrix.vecMul, dotProduct]
  exact dyadic.sum_mem fun u _ => dyadic.mul_mem (hx u) (hM u v)

/-- ⭐ **Fourier/sign triality** on a nondegenerate binary quadratic space. -/
theorem binary_quadratic_fourier_triality (Q : QuadraticForm (ZMod 2) E)
    (hb : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) E = 2 * m) (hgauss : ∑ u, sgn (Q u) = 2 ^ m) :
    let H := fourierMatrix (QuadraticMap.polarBilin Q) m
    let D := signMatrix Q
    Hᵀ = H ∧ Dᵀ = D ∧ H * Hᵀ = 1 ∧ D * Dᵀ = 1 ∧ H * H = 1 ∧ D * D = 1 ∧
      H * D * H = D * H * D ∧ (H * D) ^ 3 = 1 ∧
      (∀ x : E → ℚ, (∀ u, x u ∈ dyadic) → ∀ v, Matrix.vecMul x H v ∈ dyadic ∧
        Matrix.vecMul x D v ∈ dyadic ∧ Matrix.vecMul x (H * D) v ∈ dyadic) ∧
      Matrix.trace (H * D) = 1 ∧
      finrank ℚ (LinearMap.ker (Matrix.toLin' (H * D - 1))) = (2 ^ (2 * m) + 2) / 3 ∧
      (1 ≤ m → orderOf (H * D) = 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : Fintype.card E = 2 ^ (2 * m) := by
    rw [← FiniteField.pow_finrank_eq_card 2 E, hdim]
  intro H D
  have hHt : Hᵀ = H := fourierMatrix_transpose (polarBilin_self Q) m
  have hDt : Dᵀ = D := signMatrix_transpose Q
  have hH : H * H = 1 := fourierMatrix_mul_self Q hb hE
  have hD : D * D = 1 := signMatrix_mul_self Q
  have hHd : ∀ u v, H u v ∈ dyadic := fourierMatrix_mem_dyadic _ m
  have hDd : ∀ u v, D u v ∈ dyadic := signMatrix_mem_dyadic Q
  refine ⟨hHt, hDt, by rw [hHt, hH], by rw [hDt, hD], hH, hD, fourier_sign_braid Q hgauss,
    fourier_sign_cube Q hb hE hgauss, fun x hx v => ⟨vecMul_mem_dyadic hHd hx v,
      vecMul_mem_dyadic hDd hx v, vecMul_mem_dyadic (mul_mem_dyadic hHd hDd) hx v⟩,
    trace_fourier_sign Q hgauss, finrank_ker_fourier_sign_sub_one Q hb hE hgauss,
    fun hm => orderOf_fourier_sign Q hb hm hE hgauss⟩

end FourierTriality

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Octad/EvenSubset.lean` -/

namespace VOA.Moonshine.MonsterGriess.Octad

open VOA.Moonshine.MonsterGriess Module Matrix

noncomputable section

variable {I : Type*} [DecidableEq I]

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

def ind (s : Finset I) : I → ZMod 2 := fun i => if i ∈ s then 1 else 0

theorem ind_apply (s : Finset I) (i : I) : ind s i = if i ∈ s then 1 else 0 := rfl

def evenSubsets (d : Finset I) : Submodule (ZMod 2) (I → ZMod 2) where
  carrier := {x | (∀ i, i ∉ d → x i = 0) ∧ ∑ i ∈ d, x i = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun i hi => by simp [hx i hi, hy i hi], by simp [Finset.sum_add_distrib, hx', hy']⟩
  zero_mem' := ⟨fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨fun i hi => by simp [hx i hi], by simp [← Finset.mul_sum, hx']⟩

omit [DecidableEq I] in
theorem mem_evenSubsets {d : Finset I} {x : I → ZMod 2} :
    x ∈ evenSubsets d ↔ (∀ i, i ∉ d → x i = 0) ∧ ∑ i ∈ d, x i = 0 := Iff.rfl

def complSpan (d : Finset I) : Submodule (ZMod 2) (evenSubsets d) :=
  (Submodule.span (ZMod 2) {ind d}).comap (evenSubsets d).subtype

/-- Even subsets of `d` modulo `d`. -/
def EvenQuot (d : Finset I) : Type _ := evenSubsets d ⧸ complSpan d

instance (d : Finset I) : AddCommGroup (EvenQuot d) :=
  inferInstanceAs (AddCommGroup (evenSubsets d ⧸ complSpan d))

instance (d : Finset I) : Module (ZMod 2) (EvenQuot d) :=
  inferInstanceAs (Module (ZMod 2) (evenSubsets d ⧸ complSpan d))

def mk (d : Finset I) : evenSubsets d →ₗ[ZMod 2] EvenQuot d := (complSpan d).mkQ

theorem mk_surjective (d : Finset I) : Function.Surjective (mk d) :=
  Submodule.mkQ_surjective _

instance (d : Finset I) : Finite (evenSubsets d) := by
  refine Finite.of_injective (fun x : evenSubsets d => fun i : d => (x : I → ZMod 2) i) ?_
  intro x y h
  ext i
  by_cases hi : i ∈ d
  · exact congrFun h ⟨i, hi⟩
  · rw [x.2.1 i hi, y.2.1 i hi]

instance (d : Finset I) : Finite (EvenQuot d) := Finite.of_surjective _ (mk_surjective d)

instance (d : Finset I) : Fintype (EvenQuot d) := Fintype.ofFinite _

instance (d : Finset I) : DecidableEq (EvenQuot d) := Classical.decEq _

theorem mem_complSpan_iff {d : Finset I} (x : evenSubsets d) :
    x ∈ complSpan d ↔ (x : I → ZMod 2) = 0 ∨ (x : I → ZMod 2) = ind d := by
  simp only [complSpan, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    rcases zmod2_cases c with rfl | rfl
    · left; rw [← hc, zero_smul]
    · right; rw [← hc, one_smul]
  · rintro (h | h)
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩

theorem mk_eq_mk_iff {d : Finset I} (x y : evenSubsets d) :
    mk d x = mk d y ↔ (x : I → ZMod 2) = y ∨ (x : I → ZMod 2) = y + ind d := by
  refine (Submodule.Quotient.eq (complSpan d) (x := x) (y := y)).trans ?_
  rw [mem_complSpan_iff, Submodule.coe_sub, sub_eq_zero, sub_eq_iff_eq_add']

theorem mk_eq_zero_iff {d : Finset I} (x : evenSubsets d) :
    mk d x = 0 ↔ x ∈ complSpan d :=
  Submodule.Quotient.mk_eq_zero (complSpan d)

theorem sum_ind {d s : Finset I} (hs : s ⊆ d) : ∑ i ∈ d, ind s i = (s.card : ZMod 2) := by
  simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]

theorem sum_mul_ind (x : I → ZMod 2) {d s : Finset I} (hs : s ⊆ d) :
    ∑ i ∈ d, x i * ind s i = ∑ i ∈ s, x i := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs]

theorem ind_mem_evenSubsets {d δ : Finset I} (hδ : δ ⊆ d) (he : Even δ.card) :
    ind δ ∈ evenSubsets d :=
  ⟨fun i hi => if_neg fun h => hi (hδ h), by
    rw [sum_ind hδ]; exact (ZMod.natCast_eq_zero_iff_even).2 he⟩

/-- The class of an even subset `δ ⊆ d` in `EvenQuot d`. -/
def cls (d δ : Finset I) : EvenQuot d :=
  if h : δ ⊆ d ∧ Even δ.card then mk d ⟨ind δ, ind_mem_evenSubsets h.1 h.2⟩ else 0

theorem cls_eq {d δ : Finset I} (hδ : δ ⊆ d) (he : Even δ.card) :
    cls d δ = mk d ⟨ind δ, ind_mem_evenSubsets hδ he⟩ := dif_pos ⟨hδ, he⟩

theorem exists_cls_eq {d : Finset I} (v : EvenQuot d) :
    ∃ δ, δ ⊆ d ∧ Even δ.card ∧ cls d δ = v := by
  obtain ⟨x, rfl⟩ := mk_surjective d v
  set δ := d.filter fun i => (x : I → ZMod 2) i ≠ 0 with hδdef
  have hind : ind δ = x := by
    funext i
    by_cases hi : i ∈ d
    · rcases zmod2_cases ((x : I → ZMod 2) i) with h | h <;> simp [ind, δ, hi, h]
    · simp [ind, δ, hi, x.2.1 i hi]
  have hδ : δ ⊆ d := Finset.filter_subset _ _
  have he : Even δ.card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← sum_ind hδ, hind]
    exact x.2.2
  refine ⟨δ, hδ, he, ?_⟩
  rw [cls_eq hδ he]
  congr 1
  exact Subtype.ext hind

theorem cls_eq_cls_iff {d δ ε : Finset I} (hδ : δ ⊆ d) (hδe : Even δ.card) (hε : ε ⊆ d)
    (hεe : Even ε.card) : cls d δ = cls d ε ↔ ε = δ ∨ ε = d \ δ := by
  rw [cls_eq hδ hδe, cls_eq hε hεe, mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · left
      ext i
      have := congrFun h i
      by_cases hδi : i ∈ δ <;> by_cases hεi : i ∈ ε <;> simp_all [ind]
    · right
      ext i
      have := congrFun h i
      by_cases hdi : i ∈ d
      · by_cases hδi : i ∈ δ <;> by_cases hεi : i ∈ ε <;> simp_all [ind]
      · simp only [Finset.mem_sdiff, hdi, false_and, iff_false]
        exact fun h => hdi (hε h)
  · rintro (rfl | rfl)
    · left; rfl
    · right
      funext i
      simp only [Pi.add_apply, ind, Finset.mem_sdiff]
      by_cases hdi : i ∈ d
      · by_cases hδi : i ∈ δ
        · simp [hdi, hδi]
        · simp [hdi, hδi]; decide
      · have : i ∉ δ := fun h => hdi (hδ h)
        simp [hdi, this]

theorem even_card_sdiff {d δ : Finset I} (hd : Even d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    Even (d \ δ).card := by
  rw [Finset.card_sdiff_of_subset hδ, Nat.even_sub (Finset.card_le_card hδ)]
  exact iff_of_true hd he

theorem cls_compl {d δ : Finset I} (hd : Even d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    cls d (d \ δ) = cls d δ := by
  rw [cls_eq_cls_iff Finset.sdiff_subset (even_card_sdiff hd hδ he) hδ he]
  exact Or.inr (Finset.sdiff_sdiff_eq_self hδ).symm

def wt (d : Finset I) (x : I → ZMod 2) : ℕ := ∑ i ∈ d, (x i).val

def dotForm (d : Finset I) : LinearMap.BilinForm (ZMod 2) (evenSubsets d) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => ∑ i ∈ d, (x : I → ZMod 2) i * (y : I → ZMod 2) i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_assoc, Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [mul_left_comm, Finset.mul_sum])

omit [DecidableEq I] in
theorem dotForm_apply (d : Finset I) (x y : evenSubsets d) :
    dotForm d x y = ∑ i ∈ d, (x : I → ZMod 2) i * (y : I → ZMod 2) i := rfl

private theorem val_add_add : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by
  decide

omit [DecidableEq I] in
theorem wt_add (d : Finset I) (x y : I → ZMod 2) :
    wt d (x + y) + 2 * ∑ i ∈ d, (x i * y i).val = wt d x + wt d y := by
  simp only [wt, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib, val_add_add]

omit [DecidableEq I] in
theorem natCast_wt (d : Finset I) (x : I → ZMod 2) : (wt d x : ZMod 2) = ∑ i ∈ d, x i := by
  simp only [wt, Nat.cast_sum, ZMod.natCast_zmod_val]

omit [DecidableEq I] in
theorem even_wt {d : Finset I} {x : I → ZMod 2} (hx : x ∈ evenSubsets d) : Even (wt d x) := by
  rw [← ZMod.natCast_eq_zero_iff_even, natCast_wt]
  exact hx.2

theorem wt_ind {d s : Finset I} (hs : s ⊆ d) : wt d (ind s) = s.card := by
  have h : ∀ i, (ind s i).val = if i ∈ s then 1 else 0 := fun i => by
    unfold ind; split_ifs <;> rfl
  simp only [wt, h, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hs,
    Nat.cast_id]

omit [DecidableEq I] in
theorem evenQuad_add_aux (d : Finset I) (x y : evenSubsets d) :
    ((wt d ↑(x + y) / 2 : ℕ) : ZMod 2) =
      ((wt d x / 2 : ℕ) : ZMod 2) + ((wt d y / 2 : ℕ) : ZMod 2) + dotForm d x y := by
  have h := wt_add d x y
  rw [← Submodule.coe_add] at h
  obtain ⟨a, ha⟩ := even_wt x.2
  obtain ⟨b, hb⟩ := even_wt y.2
  set c := ∑ i ∈ d, ((x : I → ZMod 2) i * (y : I → ZMod 2) i).val with hcdef
  have hc : (c : ZMod 2) = dotForm d x y := by
    simp only [c, dotForm_apply, Nat.cast_sum, ZMod.natCast_zmod_val]
  have key : wt d ↑(x + y) / 2 + c = wt d x / 2 + wt d y / 2 := by omega
  have key' := congrArg (Nat.cast : ℕ → ZMod 2) key
  push_cast at key'
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← hc]
  linear_combination key' - (c : ZMod 2) * h2

def evenQuad (d : Finset I) : QuadraticForm (ZMod 2) (evenSubsets d) where
  toFun x := ((wt d x / 2 : ℕ) : ZMod 2)
  toFun_smul a x := by
    rcases zmod2_cases a with rfl | rfl
    · simp [wt]
    · simp
  exists_companion' := ⟨dotForm d, evenQuad_add_aux d⟩

omit [DecidableEq I] in
theorem evenQuad_apply (d : Finset I) (x : evenSubsets d) :
    evenQuad d x = ((wt d x / 2 : ℕ) : ZMod 2) := rfl

omit [DecidableEq I] in
theorem evenQuad_add (d : Finset I) (x y : evenSubsets d) :
    evenQuad d (x + y) = evenQuad d x + evenQuad d y + dotForm d x y :=
  evenQuad_add_aux d x y

theorem complSpan_le_radical {d : Finset I} (hd : 4 ∣ d.card) :
    complSpan d ≤ (evenQuad d).radical := by
  intro x hx
  rcases (mem_complSpan_iff x).1 hx with h | h
  · rw [show x = 0 from Subtype.ext h]
    exact Submodule.zero_mem _
  · have hq : evenQuad d x = 0 := by
      rw [evenQuad_apply, h, wt_ind subset_rfl]
      obtain ⟨k, hk⟩ := hd
      rw [hk, show 4 * k / 2 = 2 * k by omega, Nat.cast_mul]
      exact mul_eq_zero_of_left rfl _
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hq, fun n => ?_⟩
    rw [evenQuad_add, hq, zero_add, dotForm_apply, h]
    simp only [ind, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.inter_self]
    rw [n.2.2, add_zero]

def liftQuad (d : Finset I) (h : 4 ∣ d.card) : QuadraticForm (ZMod 2) (EvenQuot d) :=
  (evenQuad d).lift (complSpan d) (complSpan_le_radical h)

def quadForm (d : Finset I) : QuadraticForm (ZMod 2) (EvenQuot d) :=
  if h : 4 ∣ d.card then liftQuad d h else 0

theorem quadForm_mk {d : Finset I} (hd : 4 ∣ d.card) (x : evenSubsets d) :
    quadForm d (mk d x) = evenQuad d x := by
  rw [quadForm, dif_pos hd]
  rfl

theorem polarBilin_quadForm_mk {d : Finset I} (hd : 4 ∣ d.card) (x y : evenSubsets d) :
    QuadraticMap.polarBilin (quadForm d) (mk d x) (mk d y) = dotForm d x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, quadForm_mk hd,
    quadForm_mk hd, quadForm_mk hd, evenQuad_add]
  ring

theorem quadForm_cls {d δ : Finset I} (hd : 4 ∣ d.card) (hδ : δ ⊆ d) (he : Even δ.card) :
    quadForm d (cls d δ) = ((δ.card / 2 : ℕ) : ZMod 2) := by
  rw [cls_eq hδ he, quadForm_mk hd, evenQuad_apply, wt_ind hδ]

theorem polarBilin_quadForm_cls {d δ ε : Finset I} (hd : 4 ∣ d.card) (hδ : δ ⊆ d)
    (hδe : Even δ.card) (hε : ε ⊆ d) (hεe : Even ε.card) :
    QuadraticMap.polarBilin (quadForm d) (cls d δ) (cls d ε) = ((δ ∩ ε).card : ZMod 2) := by
  rw [cls_eq hδ hδe, cls_eq hε hεe, polarBilin_quadForm_mk hd, dotForm_apply]
  have h : ∀ i, ind δ i * ind ε i = ind (δ ∩ ε) i := fun i => by
    simp only [ind, ite_zero_mul_ite_zero, mul_one, Finset.mem_inter]
  simp only [h]
  exact sum_ind (Finset.inter_subset_left.trans hδ)

theorem polarBilin_quadForm_separatingLeft {d : Finset I} (hd : 4 ∣ d.card) (hne : d.Nonempty) :
    (QuadraticMap.polarBilin (quadForm d)).SeparatingLeft := by
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective d v
  have hpair : ∀ i ∈ d, ∀ j ∈ d, (x : I → ZMod 2) i = (x : I → ZMod 2) j := by
    intro i hi j hj
    by_cases hij : i = j
    · rw [hij]
    · have hsub : ({i, j} : Finset I) ⊆ d :=
        Finset.insert_subset hi (Finset.singleton_subset_iff.2 hj)
      have he : Even ({i, j} : Finset I).card := by
        rw [Finset.card_pair hij]; exact even_two
      have h := hv (cls d {i, j})
      rw [cls_eq hsub he, polarBilin_quadForm_mk hd, dotForm_apply, sum_mul_ind _ hsub,
        Finset.sum_pair hij] at h
      exact zmod2_eq_of_add_eq_zero _ _ h
  obtain ⟨i₀, hi₀⟩ := hne
  refine (mk_eq_zero_iff x).2 ((mem_complSpan_iff x).2 ?_)
  rcases zmod2_cases ((x : I → ZMod 2) i₀) with h | h
  · left
    funext i
    by_cases hi : i ∈ d
    · rw [hpair i hi i₀ hi₀, h]; rfl
    · exact x.2.1 i hi
  · right
    funext i
    by_cases hi : i ∈ d
    · rw [hpair i hi i₀ hi₀, h, ind_apply, if_pos hi]
    · rw [x.2.1 i hi, ind_apply, if_neg hi]

theorem polarBilin_quadForm_nondegenerate {d : Finset I} (hd : 4 ∣ d.card) (hne : d.Nonempty) :
    (QuadraticMap.polarBilin (quadForm d)).Nondegenerate := by
  have hl := polarBilin_quadForm_separatingLeft hd hne
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [polarBilin_symm]
  exact hy x

theorem sum_evenQuot_eq {M : Type*} [AddCommMonoid M] {d : Finset I} (hd : Even d.card) {i₀ : I}
    (hi₀ : i₀ ∈ d) (F : EvenQuot d → M) :
    ∑ v, F v = ∑ δ ∈ (d.erase i₀).powerset with Even δ.card, F (cls d δ) := by
  symm
  refine Finset.sum_bij (fun δ _ => cls d δ) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro δ hδ ε hε h
    simp only [Finset.mem_filter, Finset.mem_powerset] at hδ hε
    have hδd : δ ⊆ d := hδ.1.trans (Finset.erase_subset _ _)
    have hεd : ε ⊆ d := hε.1.trans (Finset.erase_subset _ _)
    rcases (cls_eq_cls_iff hδd hδ.2 hεd hε.2).1 h with h' | h'
    · exact h'.symm
    · exfalso
      have : i₀ ∈ ε := by
        rw [h']
        exact Finset.mem_sdiff.2 ⟨hi₀, fun h => Finset.notMem_erase i₀ d (hδ.1 h)⟩
      exact Finset.notMem_erase i₀ d (hε.1 this)
  · intro v _
    obtain ⟨δ, hδ, he, rfl⟩ := exists_cls_eq v
    by_cases h : i₀ ∈ δ
    · refine ⟨d \ δ, ?_, cls_compl hd hδ he⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => ?_, even_card_sdiff hd hδ he⟩
      rw [Finset.mem_sdiff] at hi
      exact Finset.mem_erase.2 ⟨fun h' => hi.2 (h' ▸ h), hi.1⟩
    · refine ⟨δ, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun i hi => Finset.mem_erase.2 ⟨fun h' => h (h' ▸ hi), hδ hi⟩, he⟩

theorem card_evenQuot {d : Finset I} (hd : d.card = 8) : Fintype.card (EvenQuot d) = 64 := by
  obtain ⟨i₀, hi₀⟩ : d.Nonempty := Finset.card_pos.1 (by omega)
  have h7 : (d.erase i₀).card = 7 := by rw [Finset.card_erase_of_mem hi₀, hd]
  rw [Fintype.card_eq_sum_ones, sum_evenQuot_eq (by rw [hd]; decide) hi₀, Finset.sum_filter]
  have := Finset.sum_powerset_apply_card (fun n => if Even n then (1 : ℕ) else 0)
    (x := d.erase i₀)
  rw [this, h7]
  decide

theorem finrank_evenQuot {d : Finset I} (hd : d.card = 8) :
    finrank (ZMod 2) (EvenQuot d) = 6 := by
  have h := FiniteField.pow_finrank_eq_card 2 (EvenQuot d)
  rw [card_evenQuot hd, show (64 : ℕ) = 2 ^ 6 from rfl] at h
  exact Nat.pow_right_injective le_rfl h

theorem sgn_natCast (n : ℕ) : sgn (n : ZMod 2) = (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [(ZMod.natCast_eq_zero_iff_even).2 h, h.neg_one_pow]; rfl
  · rw [(ZMod.natCast_eq_one_iff_odd).2 h, h.neg_one_pow]; rfl

theorem sum_sgn_quadForm {d : Finset I} (hd : d.card = 8) :
    ∑ v : EvenQuot d, sgn (quadForm d v) = 8 := by
  obtain ⟨i₀, hi₀⟩ : d.Nonempty := Finset.card_pos.1 (by omega)
  have h4 : 4 ∣ d.card := by rw [hd]; norm_num
  have h7 : (d.erase i₀).card = 7 := by rw [Finset.card_erase_of_mem hi₀, hd]
  rw [sum_evenQuot_eq (by rw [hd]; decide) hi₀]
  rw [Finset.sum_congr rfl fun δ hδ => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at hδ
    rw [quadForm_cls h4 (hδ.1.trans (Finset.erase_subset _ _)) hδ.2, sgn_natCast]]
  rw [Finset.sum_filter]
  have := Finset.sum_powerset_apply_card (fun n => if Even n then ((-1 : ℚ) ^ (n / 2)) else 0)
    (x := d.erase i₀)
  rw [this, h7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.even_iff]
  norm_num [Nat.choose]

/-- ⭐ **The even subsets of an octad modulo the octad form a 6-dimensional quadratic space with
Fourier/sign triality.** -/
theorem eight_point_even_subset_quadratic_space (d : Finset I) (hd : d.card = 8) :
    let H := fourierMatrix (QuadraticMap.polarBilin (quadForm d)) 3
    let D := signMatrix (quadForm d)
    (∀ δ ε, δ ⊆ d → Even δ.card → ε ⊆ d → Even ε.card →
      quadForm d (cls d δ) = ((δ.card / 2 : ℕ) : ZMod 2) ∧
      QuadraticMap.polarBilin (quadForm d) (cls d δ) (cls d ε) = ((δ ∩ ε).card : ZMod 2)) ∧
    finrank (ZMod 2) (EvenQuot d) = 6 ∧
    (QuadraticMap.polarBilin (quadForm d)).Nondegenerate ∧
    ∑ v : EvenQuot d, sgn (quadForm d v) = 8 ∧
    (∀ δ ε, δ ⊆ d → Even δ.card → ε ⊆ d → Even ε.card →
      H (cls d δ) (cls d ε) = (-1) ^ (δ ∩ ε).card / 8 ∧
      D (cls d δ) (cls d ε) = if cls d δ = cls d ε then (-1) ^ (δ.card / 2) else 0) ∧
    H * Hᵀ = 1 ∧ H * H = 1 ∧ D * Dᵀ = 1 ∧ D * D = 1 ∧
    orderOf (H * D) = 3 ∧ Matrix.trace (H * D) = 1 ∧
    finrank ℚ (LinearMap.ker (Matrix.toLin' (H * D - 1))) = 22 := by
  intro H D
  have h4 : 4 ∣ d.card := by rw [hd]; norm_num
  have hne : d.Nonempty := Finset.card_pos.1 (by omega)
  have hb := polarBilin_quadForm_nondegenerate h4 hne
  have hdim : finrank (ZMod 2) (EvenQuot d) = 2 * 3 := finrank_evenQuot hd
  have hgauss : ∑ u, sgn (quadForm d u) = 2 ^ 3 := by rw [sum_sgn_quadForm hd]; norm_num
  obtain ⟨-, -, hHH', hDD', hHH, hDD, -, -, -, htr, hker, hord⟩ :=
    binary_quadratic_fourier_triality (quadForm d) hb hdim hgauss
  refine ⟨fun δ ε hδ hδe hε hεe =>
      ⟨quadForm_cls h4 hδ hδe, polarBilin_quadForm_cls h4 hδ hδe hε hεe⟩,
    finrank_evenQuot hd, hb, sum_sgn_quadForm hd, fun δ ε hδ hδe hε hεe => ⟨?_, ?_⟩,
    hHH', hHH, hDD', hDD, hord (by norm_num), htr, ?_⟩
  · simp only [H, fourierMatrix]
    rw [polarBilin_quadForm_cls h4 hδ hδe hε hεe, sgn_natCast]
    ring
  · simp only [D, signMatrix, Matrix.diagonal_apply]
    rw [quadForm_cls h4 hδ hδe, sgn_natCast]
  · rw [hker]
    norm_num

end

end VOA.Moonshine.MonsterGriess.Octad
