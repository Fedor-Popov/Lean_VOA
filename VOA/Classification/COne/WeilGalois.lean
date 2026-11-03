/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.ThetaGalois

/-!
# The Weil Galois law (G4): reduction to the congruence property

`WeilGaloisLaw` (`ThetaGalois.lean`) says: for `4N ∣ M`, `24 ∣ M`, `ℓ` prime to `M` and
`γ ≡ diag(ℓ, ℓ⁻¹) (mod M)`, every Weil word matrix `A` of `γ` acts on even `2N`-periodic vectors
as `v ↦ (2N/ℓ) v(ℓ ·)`. This file proves it **equivalent** to the single scalar statement

* `WeilKernelLaw`: for `γ ∈ Γ(M)` every Weil word matrix has `A₀₀ = 1`

(`weilGaloisLaw_iff_weilKernelLaw`), i.e. everything except the congruence property of the
`η⁻¹`-twisted Weil representation is proved. Ingredients, all proved here:

1. **Heisenberg covariance** (`weilWord_heis`): with `W(x,y) v(μ) = e((2yμ + xy)/4N) v(μ+x)`,
   every Weil word matrix of `γ = [[a,b],[c,d]]` satisfies
   `A W(x,y) = W(s(dx − cy), s(−bx + ay)) A` for a sign `s = ±1`.
2. **Monomiality** (`weilWord_diag`): if `γ ≡ diag (mod 4N)` then
   `A_{μν} = A₀₀ · [ν ≡ s a μ (mod 2N)]`. Hence `WeilGaloisLaw ⇐ WeilScalarLaw` (`A₀₀ = (2N/ℓ)`).
3. **Splitting** (`weilScalarLaw_of_kernel_torus`): the scalar law follows from the kernel law and
   one good representative per torus class (`WeilTorusLaw`).
4. **The torus representative** `𝔡(ℓ, m) = T^ℓ S T^m S T^ℓ S⁻¹ ≡ diag(ℓ, m)`: its word matrix has
   `A₀₀ = e(−(2ℓ+m)/24) G_ℓ / √(2N)` with `G_a = ∑_{k mod 2N} e(ak²/4N)` (`dlMat_apply`). The kernel
   law on the relation word `𝔡(1,1) = 1` supplies Gauss's sign `G_1 = e(1/8)√(2N)`.
5. **The Gauss ratio law** (`gaussRatioLaw`, sign-free, proved from scratch):
   `G_ℓ = (2N/ℓ) e((ℓ−1)/8) G_1` for `ℓ` prime to `2N`, via CRT for Gauss sums (`gs_crt`), the
   odd prime-square reduction (`gs_p2`), the prime case through Mathlib's quadratic character and
   `gaussSum` machinery (`gs_prime`), the Jacobi law for odd moduli (`gs_jacobi`), the 2-adic
   recursion and base values (`gs_two_step`, `gs_four`, `gs_eight`, `one_add_E4`), and Jacobi
   reciprocity (`gs_two_adic`).

## What remains

`WeilKernelLaw` — the congruence property `ρ(Γ(M)) = 1` of the `η⁻¹`-twisted Weil representation,
read on one matrix entry. It contains Gauss's sign theorem (apply it to the relation word
`T S T S T S⁻¹ = 1`), which is not in Mathlib. Numerically confirmed:
`scratchpad/kernel_check.py`, 300 random `γ ∈ Γ(M)` (Euclidean `S,T` words), error `< 1e-8`.
-/

open Complex Finset

noncomputable section

namespace VOA.Classification.COne

namespace WeilGalois

/-! ## The character `e₄(k) = e(k/4N)` -/

/-- `e₄(k) = exp(2πik/4N)`. -/
def e4 (N : ℕ) (k : ℤ) : ℂ := cexp (2 * Real.pi * I * (k : ℂ) / (4 * N))

theorem e4_add (N : ℕ) (a b : ℤ) : e4 N (a + b) = e4 N a * e4 N b := by
  unfold e4; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e4_zero (N : ℕ) : e4 N 0 = 1 := by simp [e4]

theorem e4_period {N : ℕ} (hN : 0 < N) (a k : ℤ) : e4 N (a + 4 * N * k) = e4 N a := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold e4
  rw [show 2 * Real.pi * I * (((a + 4 * N * k : ℤ)) : ℂ) / (4 * N) =
      2 * Real.pi * I * (a : ℂ) / (4 * N) + k * (2 * Real.pi * I) by push_cast; field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem e4_eq_of_eq {N : ℕ} (hN : 0 < N) {a b : ℤ} (h : ∃ k : ℤ, a = b + 4 * N * k) :
    e4 N a = e4 N b := by
  obtain ⟨k, rfl⟩ := h; exact e4_period hN b k

theorem modEq_of_e4_eq {N : ℕ} (hN : 0 < N) {a b : ℤ} (h : e4 N a = e4 N b) :
    a ≡ b [ZMOD (4 * N : ℕ)] := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  unfold e4 at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h2 : ((a : ℤ) : ℂ) = ((b + 4 * N * n : ℤ) : ℂ) := by
    have := hn
    field_simp at this
    push_cast
    linear_combination this
  have h3 : a = b + 4 * N * n := by exact_mod_cast h2
  exact (Int.modEq_iff_dvd.2 ⟨-n, by push_cast; linarith⟩)

theorem exists_of_modEq {a b : ℤ} {n : ℕ} (h : a ≡ b [ZMOD n]) : ∃ k : ℤ, b = a + n * k := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h
  exact ⟨k, by linarith⟩

/-! ## Indices modulo `2N` -/

variable {N : ℕ}

theorem weilIdx_val (hN : 0 < N) (z : ℤ) :
    (((weilIdx hN z : ℕ)) : ℤ) = z % ((2 * N : ℕ) : ℤ) := by
  have h1 : 0 ≤ z % ((2 * N : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
  simp only [weilIdx, Int.toNat_of_nonneg h1]

theorem eq_weilIdx_iff (hN : 0 < N) (j : Fin (2 * N)) (z : ℤ) :
    j = weilIdx hN z ↔ ((j : ℕ) : ℤ) ≡ z [ZMOD (2 * N : ℕ)] := by
  have hj : ((j : ℕ) : ℤ) % ((2 * N : ℕ) : ℤ) = (j : ℕ) :=
    Int.emod_eq_of_lt (by omega) (by have := j.2; omega)
  rw [Fin.ext_iff, ← Int.natCast_inj, weilIdx_val, Int.ModEq, hj]

theorem weilIdx_fin (hN : 0 < N) (j : Fin (2 * N)) : weilIdx hN ((j : ℕ) : ℤ) = j :=
  ((eq_weilIdx_iff hN j _).2 Int.ModEq.rfl).symm

theorem weilIdx_congr (hN : 0 < N) {z z' : ℤ} (h : z ≡ z' [ZMOD (2 * N : ℕ)]) :
    weilIdx hN z = weilIdx hN z' :=
  (eq_weilIdx_iff hN _ _).2 ((weilIdx_modEq hN z).trans h)

theorem weilIdx_cast_add (hN : 0 < N) (z w : ℤ) :
    weilIdx hN (((weilIdx hN z : ℕ) : ℤ) + w) = weilIdx hN (z + w) :=
  weilIdx_congr hN ((weilIdx_modEq hN z).add_right w)

/-! ## The Heisenberg matrices -/

/-- The Heisenberg operator `W(x,y) v (μ) = e((2yμ + xy)/4N) v(μ + x)`, as a matrix. -/
def heis (N : ℕ) (x y : ℤ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ := fun μ ν =>
  if ((ν : ℕ) : ℤ) ≡ ((μ : ℕ) : ℤ) + x [ZMOD (2 * N : ℕ)] then
    e4 N (y * (2 * ((μ : ℕ) : ℤ) + x)) else 0

theorem heis_mul_apply (hN : 0 < N) (x y : ℤ) (A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ)
    (μ ν : Fin (2 * N)) :
    (heis N x y * A) μ ν = e4 N (y * (2 * ((μ : ℕ) : ℤ) + x)) * A (weilIdx hN (μ + x)) ν := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (weilIdx hN (((μ : ℕ) : ℤ) + x))]
  · rw [heis, if_pos (weilIdx_modEq hN _)]
  · intro j _ hj
    rw [heis, if_neg, zero_mul]
    intro h; exact hj ((eq_weilIdx_iff hN j _).2 h)
  · simp

theorem mul_heis_apply (hN : 0 < N) (x y : ℤ) (A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ)
    (μ ν : Fin (2 * N)) :
    (A * heis N x y) μ ν = A μ (weilIdx hN (ν - x)) *
      e4 N (y * (2 * ((weilIdx hN (ν - x) : ℕ) : ℤ) + x)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (weilIdx hN (((ν : ℕ) : ℤ) - x))]
  · rw [heis, if_pos]
    have := (weilIdx_modEq hN (((ν : ℕ) : ℤ) - x)).add_right x
    simpa using this.symm
  · intro j _ hj
    rw [heis, if_neg, mul_zero]
    intro h; apply hj; rw [eq_weilIdx_iff]
    have := h.sub_right x
    simpa using this.symm
  · simp

theorem heis_congr (hN : 0 < N) {x x' y y' : ℤ} (hx : x ≡ x' [ZMOD (4 * N : ℕ)])
    (hy : y ≡ y' [ZMOD (4 * N : ℕ)]) : heis N x y = heis N x' y' := by
  have e : (2 : ℤ) * ((2 * N : ℕ) : ℤ) = ((4 * N : ℕ) : ℤ) := by push_cast; ring
  have hx2 : x ≡ x' [ZMOD (2 * N : ℕ)] := Int.ModEq.of_mul_left 2 (by rw [e]; exact hx)
  ext μ ν
  unfold heis
  have hc : (((ν : ℕ) : ℤ) ≡ ((μ : ℕ) : ℤ) + x [ZMOD (2 * N : ℕ)]) ↔
      (((ν : ℕ) : ℤ) ≡ ((μ : ℕ) : ℤ) + x' [ZMOD (2 * N : ℕ)]) :=
    ⟨fun h => h.trans (hx2.add_left _), fun h => h.trans (hx2.add_left _).symm⟩
  by_cases h : ((ν : ℕ) : ℤ) ≡ ((μ : ℕ) : ℤ) + x [ZMOD (2 * N : ℕ)]
  · rw [if_pos h, if_pos (hc.1 h)]
    obtain ⟨p, hp⟩ := exists_of_modEq hx
    obtain ⟨q, hq⟩ := exists_of_modEq hy
    refine (e4_eq_of_eq hN ⟨y * p + q * (2 * ((μ : ℕ) : ℤ) + x) + 4 * N * q * p, ?_⟩).symm
    rw [hp, hq]; push_cast; ring
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## Intertwining with `S` and `T` -/

theorem weilS_apply (N : ℕ) (μ j : Fin (2 * N)) :
    weilS N μ j = ((Real.sqrt (2 * N))⁻¹ : ℝ) * e4 N (2 * ((j : ℕ) : ℤ) * ((μ : ℕ) : ℤ)) := by
  unfold weilS e4; congr 2; push_cast; ring

theorem weilPhase_eq (N : ℕ) (μ : ℤ) :
    weilPhase N μ = e4 N (μ ^ 2) * cexp (-(2 * Real.pi * I / 24)) := by
  unfold weilPhase e4; push_cast; ring_nf

theorem weilS_heis (hN : 0 < N) (x y : ℤ) :
    weilS N * heis N x y = heis N y (-x) * weilS N := by
  ext μ ν
  rw [mul_heis_apply hN, heis_mul_apply hN, weilS_apply, weilS_apply]
  obtain ⟨p, hp⟩ := exists_of_modEq (weilIdx_modEq hN (((ν : ℕ) : ℤ) - x))
  obtain ⟨q, hq⟩ := exists_of_modEq (weilIdx_modEq hN (((μ : ℕ) : ℤ) + y))
  set j₀ : ℤ := ((weilIdx hN (((ν : ℕ) : ℤ) - x) : ℕ) : ℤ) with hj₀
  set i₀ : ℤ := ((weilIdx hN (((μ : ℕ) : ℤ) + y) : ℕ) : ℤ) with hi₀
  have hj : j₀ = ((ν : ℕ) : ℤ) - x - 2 * N * p := by push_cast at hp; linarith
  have hi : i₀ = ((μ : ℕ) : ℤ) + y - 2 * N * q := by push_cast at hq; linarith
  have key : e4 N (2 * j₀ * ((μ : ℕ) : ℤ)) * e4 N (y * (2 * j₀ + x)) =
      e4 N (-x * (2 * ((μ : ℕ) : ℤ) + y)) * e4 N (2 * ((ν : ℕ) : ℤ) * i₀) := by
    rw [← e4_add, ← e4_add]
    refine e4_eq_of_eq hN ⟨-(p * ((μ : ℕ) : ℤ)) - p * y + q * ((ν : ℕ) : ℤ), ?_⟩
    rw [hj, hi]; ring
  linear_combination ((Real.sqrt (2 * N))⁻¹ : ℝ) * key

theorem weilT_mul_weilTinv (N : ℕ) : weilT N * weilTinv N = 1 := by
  rw [weilT, weilTinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext μ; exact mul_inv_cancel₀ (weilPhase_ne_zero _ _)

theorem weilTinv_mul_weilT (N : ℕ) : weilTinv N * weilT N = 1 := by
  rw [weilT, weilTinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext μ; exact inv_mul_cancel₀ (weilPhase_ne_zero _ _)

theorem weilT_heis (hN : 0 < N) (x y : ℤ) :
    weilT N * heis N x y = heis N x (y - x) * weilT N := by
  ext μ ν
  rw [weilT, Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold heis
  split_ifs with h
  · obtain ⟨p, hp⟩ := exists_of_modEq h
    rw [weilPhase_eq, weilPhase_eq]
    have key : e4 N (((μ : ℕ) : ℤ) ^ 2) * e4 N (y * (2 * ((μ : ℕ) : ℤ) + x)) =
        e4 N ((y - x) * (2 * ((μ : ℕ) : ℤ) + x)) * e4 N (((ν : ℕ) : ℤ) ^ 2) := by
      rw [← e4_add, ← e4_add]
      have hν : ((ν : ℕ) : ℤ) = ((μ : ℕ) : ℤ) + x - 2 * N * p := by push_cast at hp; linarith
      refine e4_eq_of_eq hN ⟨p * (((μ : ℕ) : ℤ) + x) - N * p ^ 2, ?_⟩
      rw [hν]; ring
    linear_combination cexp (-(2 * Real.pi * I / 24)) * key
  · simp

theorem weilTinv_heis (hN : 0 < N) (x y : ℤ) :
    weilTinv N * heis N x y = heis N x (y + x) * weilTinv N := by
  have h := weilT_heis hN x (y + x)
  rw [add_sub_cancel_right] at h
  calc weilTinv N * heis N x y
      = weilTinv N * (heis N x y * weilT N) * weilTinv N := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, weilT_mul_weilTinv, Matrix.mul_one]
    _ = heis N x (y + x) * weilTinv N := by
        rw [← h, ← Matrix.mul_assoc, weilTinv_mul_weilT, Matrix.one_mul]

/-! ## Every Weil word intertwines the Heisenberg action through `±γ⁻ᵀ` -/

open ModularGroup in
theorem S_mul_apply' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (S * γ) 0 0 = -γ 1 0 ∧ (S * γ) 0 1 = -γ 1 1 ∧ (S * γ) 1 0 = γ 0 0 ∧ (S * γ) 1 1 = γ 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

open ModularGroup in
theorem Sinv_mul_apply' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (S⁻¹ * γ) 0 0 = γ 1 0 ∧ (S⁻¹ * γ) 0 1 = γ 1 1 ∧ (S⁻¹ * γ) 1 0 = -γ 0 0 ∧
      (S⁻¹ * γ) 1 1 = -γ 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_S,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

open ModularGroup in
theorem T_mul_apply' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (T * γ) 0 0 = γ 0 0 + γ 1 0 ∧ (T * γ) 0 1 = γ 0 1 + γ 1 1 ∧ (T * γ) 1 0 = γ 1 0 ∧
      (T * γ) 1 1 = γ 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.mul_apply, Fin.sum_univ_two]

open ModularGroup in
theorem Tinv_mul_apply' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (T⁻¹ * γ) 0 0 = γ 0 0 - γ 1 0 ∧ (T⁻¹ * γ) 0 1 = γ 0 1 - γ 1 1 ∧ (T⁻¹ * γ) 1 0 = γ 1 0 ∧
      (T⁻¹ * γ) 1 1 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor <;> ring

/-- **Heisenberg covariance of Weil words.** If `A` is a Weil word matrix of
`γ = [[a, b], [c, d]]`, then for a sign `s = ±1`, `A W(x,y) = W(s(dx − cy), s(−bx + ay)) A`. -/
theorem weilWord_heis (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ x y : ℤ, A * heis N x y =
      heis N (s * (γ 1 1 * x - γ 1 0 * y)) (s * (-(γ 0 1) * x + γ 0 0 * y)) * A := by
  induction h with
  | one => exact ⟨1, Or.inl rfl, fun x y => by simp⟩
  | @S γ A _ ih =>
    obtain ⟨s, hs, hA⟩ := ih
    refine ⟨-s, by rcases hs with rfl | rfl <;> norm_num, fun x y => ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := S_mul_apply' γ
    rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, weilS_heis hN, Matrix.mul_assoc, e1, e2, e3, e4]
    congr 2 <;> ring
  | @Sinv γ A _ ih =>
    obtain ⟨s, hs, hA⟩ := ih
    refine ⟨s, hs, fun x y => ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := Sinv_mul_apply' γ
    rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, weilS_heis hN, Matrix.mul_assoc, e1, e2, e3, e4]
    congr 2 <;> ring
  | @T γ A _ ih =>
    obtain ⟨s, hs, hA⟩ := ih
    refine ⟨s, hs, fun x y => ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := T_mul_apply' γ
    rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, weilT_heis hN, Matrix.mul_assoc, e1, e2, e3, e4]
    congr 2; ring
  | @Tinv γ A _ ih =>
    obtain ⟨s, hs, hA⟩ := ih
    refine ⟨s, hs, fun x y => ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := Tinv_mul_apply' γ
    rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, weilTinv_heis hN, Matrix.mul_assoc, e1, e2, e3,
      e4]
    congr 2; ring

/-! ## Weil words of diagonal-mod-`4N` matrices are monomial -/

/-- The index `0 ∈ Fin (2N)`. -/
def fz (hN : 0 < N) : Fin (2 * N) := ⟨0, by omega⟩

theorem det_SL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rw [Matrix.det_fin_two] at this; exact this

/-- **Monomiality.** If `γ ≡ diag(a, d) (mod 4N)` then every Weil word matrix of `γ` is
`A₀₀` times the signed permutation `e_ν ↦ e_{saν}`, `s = ±1`. -/
theorem weilWord_diag (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A)
    (hb : ((4 * N : ℕ) : ℤ) ∣ γ 0 1) (hc : ((4 * N : ℕ) : ℤ) ∣ γ 1 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ μ ν : Fin (2 * N),
      A μ ν = if ((ν : ℕ) : ℤ) ≡ s * γ 0 0 * ((μ : ℕ) : ℤ) [ZMOD (2 * N : ℕ)] then
        A (fz hN) (fz hN) else 0 := by
  obtain ⟨s, hs, hA⟩ := weilWord_heis hN h
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have e42 : ((4 * N : ℕ) : ℤ) = 2 * ((2 * N : ℕ) : ℤ) := by push_cast; ring
  have hb2 : ((2 * N : ℕ) : ℤ) ∣ γ 0 1 := (Dvd.intro_left 2 e42.symm).trans hb
  have had : γ 0 0 * γ 1 1 ≡ 1 [ZMOD (2 * N : ℕ)] := by
    have := det_SL γ
    refine Int.modEq_iff_dvd.2 ?_
    have : 1 - γ 0 0 * γ 1 1 = -(γ 0 1 * γ 1 0) := by linarith
    rw [this]; exact (hb2.mul_right _).neg_right
  -- (1) modulation
  have h1 : ∀ μ ν : Fin (2 * N), A μ ν ≠ 0 →
      ((ν : ℕ) : ℤ) ≡ s * γ 0 0 * ((μ : ℕ) : ℤ) [ZMOD (2 * N : ℕ)] := by
    intro μ ν hne
    have H := hA 0 1
    have hx : heis N (s * (γ 1 1 * 0 - γ 1 0 * 1)) (s * (-(γ 0 1) * 0 + γ 0 0 * 1)) =
        heis N 0 (s * γ 0 0) := by
      refine heis_congr hN (Int.modEq_iff_dvd.2 ?_)
        (by rw [show s * (-(γ 0 1) * 0 + γ 0 0 * 1) = s * γ 0 0 by ring])
      rw [show (0 : ℤ) - s * (γ 1 1 * 0 - γ 1 0 * 1) = s * γ 1 0 by ring]
      exact hc.mul_left s
    rw [hx] at H
    have H' := congrFun (congrFun H μ) ν
    rw [mul_heis_apply hN, heis_mul_apply hN] at H'
    simp only [sub_zero, add_zero, weilIdx_fin, one_mul] at H'
    have he : e4 N (2 * ((ν : ℕ) : ℤ)) = e4 N (s * γ 0 0 * (2 * ((μ : ℕ) : ℤ))) :=
      mul_left_cancel₀ hne (H'.trans (mul_comm _ _))
    have hm := Int.modEq_iff_dvd.1 (modEq_of_e4_eq hN he)
    rw [e42, show s * γ 0 0 * (2 * ((μ : ℕ) : ℤ)) - 2 * ((ν : ℕ) : ℤ) =
      2 * (s * γ 0 0 * ((μ : ℕ) : ℤ) - ((ν : ℕ) : ℤ)) by ring] at hm
    exact Int.modEq_iff_dvd.2 (Int.dvd_of_mul_dvd_mul_left (by norm_num) hm)
  -- (2) translation
  have h2 : ∀ μ ν : Fin (2 * N),
      A μ (weilIdx hN (((ν : ℕ) : ℤ) - 1)) = A (weilIdx hN (((μ : ℕ) : ℤ) + s * γ 1 1)) ν := by
    intro μ ν
    have H := hA 1 0
    have hx : heis N (s * (γ 1 1 * 1 - γ 1 0 * 0)) (s * (-(γ 0 1) * 1 + γ 0 0 * 0)) =
        heis N (s * γ 1 1) 0 := by
      refine heis_congr hN (by rw [show s * (γ 1 1 * 1 - γ 1 0 * 0) = s * γ 1 1 by ring])
        (Int.modEq_iff_dvd.2 ?_)
      rw [show (0 : ℤ) - s * (-(γ 0 1) * 1 + γ 0 0 * 0) = s * γ 0 1 by ring]
      exact hb.mul_left s
    rw [hx] at H
    have H' := congrFun (congrFun H μ) ν
    rw [mul_heis_apply hN, heis_mul_apply hN] at H'
    simpa [e4_zero] using H'
  -- (3) propagation along the diagonal
  have h3 : ∀ k : ℕ, A (weilIdx hN ((k : ℤ) * (s * γ 1 1))) (weilIdx hN k) =
      A (fz hN) (fz hN) := by
    intro k
    induction k with
    | zero =>
      have : weilIdx hN 0 = fz hN := ((eq_weilIdx_iff hN (fz hN) 0).2 (by simp [fz])).symm
      simpa using congrArg (fun i => A i i) this
    | succ k ih =>
      have := h2 (weilIdx hN ((k : ℤ) * (s * γ 1 1))) (weilIdx hN ((k + 1 : ℕ) : ℤ))
      rw [sub_eq_add_neg, weilIdx_cast_add, weilIdx_cast_add] at this
      have e1 : weilIdx hN (((k + 1 : ℕ) : ℤ) + -1) = weilIdx hN (k : ℤ) := by
        congr 1; push_cast; ring
      have e2 : weilIdx hN ((k : ℤ) * (s * γ 1 1) + s * γ 1 1) =
          weilIdx hN (((k + 1 : ℕ) : ℤ) * (s * γ 1 1)) := by congr 1; push_cast; ring
      rw [e1, e2, ih] at this
      exact this.symm
  -- (4) conclusion
  refine ⟨s, hs, fun μ ν => ?_⟩
  split_ifs with hcond
  · have hk := h3 (ν : ℕ)
    rw [weilIdx_fin] at hk
    have hμ : weilIdx hN (((ν : ℕ) : ℤ) * (s * γ 1 1)) = μ := by
      refine ((eq_weilIdx_iff hN μ _).2 ?_).symm
      have := (hcond.mul_right (s * γ 1 1)).trans
        (show s * γ 0 0 * ((μ : ℕ) : ℤ) * (s * γ 1 1) ≡ 1 * 1 * ((μ : ℕ) : ℤ) [ZMOD (2 * N : ℕ)]
          by rw [show s * γ 0 0 * ((μ : ℕ) : ℤ) * (s * γ 1 1) =
              (s * s) * (γ 0 0 * γ 1 1) * ((μ : ℕ) : ℤ) by ring, hs2]
             exact (had.mul_left 1).mul_right _)
      simpa using this.symm
    rw [hμ] at hk; exact hk
  · by_contra hne; exact hcond (h1 μ ν hne)

/-! ## Reduction of `WeilGaloisLaw` to a single matrix entry -/

theorem periodic_congr {v : ℤ → ℂ} (hper : ∀ x, v (x + 2 * N) = v x) {a b : ℤ}
    (h : a ≡ b [ZMOD (2 * N : ℕ)]) : v a = v b := by
  obtain ⟨k, rfl⟩ := exists_of_modEq h
  have key : ∀ k : ℤ, v (a + ((2 * N : ℕ) : ℤ) * k) = v a := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [← ih, show a + ((2 * N : ℕ) : ℤ) * (k + 1) = a + ((2 * N : ℕ) : ℤ) * k + 2 * N by
        push_cast; ring, hper]
    | pred k ih =>
      rw [← ih, show a + ((2 * N : ℕ) : ℤ) * (-(k : ℤ)) =
        a + ((2 * N : ℕ) : ℤ) * (-(k : ℤ) - 1) + 2 * N by push_cast; ring, hper]
  exact (key k).symm

/-- **The Weil scalar law** (the residual after the Heisenberg reduction): for `γ ≡ diag(ℓ, ℓ⁻¹)
(mod M)` every Weil word matrix of `γ` has `(0,0)` entry `(2N/ℓ)`. -/
def WeilScalarLaw : Prop :=
  ∀ (N M : ℕ) (hN : 0 < N), 4 * N ∣ M → 24 ∣ M →
    ∀ ℓ : ℕ, ℓ.Coprime M → ∀ ℓ' : ℤ, (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M] →
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ 0 0 ≡ ℓ [ZMOD M] → γ 1 1 ≡ ℓ' [ZMOD M] → γ 0 1 ≡ 0 [ZMOD M] → γ 1 0 ≡ 0 [ZMOD M] →
      ∀ A, WeilWord N γ A → A (fz hN) (fz hN) = (jacobiSym (2 * (N : ℤ)) ℓ : ℂ)

theorem dvd_of_modEq_zero {M n : ℕ} (hn : n ∣ M) {x : ℤ} (h : x ≡ 0 [ZMOD M]) : (n : ℤ) ∣ x :=
  (Int.natCast_dvd_natCast.2 hn).trans (Int.modEq_zero_iff_dvd.1 h)

/-- **G4 reduction**: the Weil Galois law follows from the scalar law. -/
theorem weilGaloisLaw_of_weilScalarLaw (hS : WeilScalarLaw) : WeilGaloisLaw := by
  intro N M hN h4N h24 ℓ hℓ ℓ' hℓ' γ h00 h11 h01 h10 A hA v hper hev μ
  obtain ⟨s, hs, hd⟩ := weilWord_diag hN hA (dvd_of_modEq_zero h4N h01)
    (dvd_of_modEq_zero h4N h10)
  have hc := hS N M hN h4N h24 ℓ hℓ ℓ' hℓ' γ h00 h11 h01 h10 A hA
  have h2N : 2 * N ∣ M := (Dvd.intro_left 2 (by ring) : 2 * N ∣ 4 * N).trans h4N
  rw [Finset.sum_eq_single (weilIdx hN (s * γ 0 0 * ((μ : ℕ) : ℤ)))]
  · rw [hd, if_pos (weilIdx_modEq hN _), hc]
    congr 1
    refine (periodic_congr hper (weilIdx_modEq hN _)).trans ?_
    have hℓ2 : γ 0 0 ≡ ℓ [ZMOD (2 * N : ℕ)] :=
      Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h2N) h00
    rcases hs with rfl | rfl
    · exact periodic_congr hper (by simpa using hℓ2.mul_right ((μ : ℕ) : ℤ))
    · rw [show -1 * γ 0 0 * ((μ : ℕ) : ℤ) = -(γ 0 0 * ((μ : ℕ) : ℤ)) by ring, hev]
      exact periodic_congr hper (hℓ2.mul_right _)
  · intro j _ hj
    rw [hd, if_neg, zero_mul]
    intro h; exact hj ((eq_weilIdx_iff hN j _).2 h)
  · simp

/-! ## Splitting the scalar law: congruence property + one torus representative -/

/-- **(K) The kernel law**: `Γ(M)` acts trivially (the congruence property of the η-twisted
Weil representation, read on the `(0,0)` entry). -/
def WeilKernelLaw : Prop :=
  ∀ (N M : ℕ) (hN : 0 < N), 4 * N ∣ M → 24 ∣ M →
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ 0 0 ≡ 1 [ZMOD M] → γ 1 1 ≡ 1 [ZMOD M] → γ 0 1 ≡ 0 [ZMOD M] → γ 1 0 ≡ 0 [ZMOD M] →
      ∀ A, WeilWord N γ A → A (fz hN) (fz hN) = 1

/-- **(D) The torus law**: each class `diag(ℓ, ℓ⁻¹) mod M` has *some* lift with *some* Weil word
whose `(0,0)` entry is `(2N/ℓ)`. -/
def WeilTorusLaw : Prop :=
  ∀ (N M : ℕ) (hN : 0 < N), 4 * N ∣ M → 24 ∣ M →
    ∀ ℓ : ℕ, ℓ.Coprime M → ∀ ℓ' : ℤ, (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M] →
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ 0 0 ≡ ℓ [ZMOD M] ∧ γ 1 1 ≡ ℓ' [ZMOD M] ∧ γ 0 1 ≡ 0 [ZMOD M] ∧ γ 1 0 ≡ 0 [ZMOD M] ∧
      ∃ A, WeilWord N γ A ∧ A (fz hN) (fz hN) = (jacobiSym (2 * (N : ℤ)) ℓ : ℂ)

/-- The first row of a monomial Weil word is concentrated at `0`. -/
theorem weilWord_row_zero (hN : 0 < N) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A)
    (hb : ((4 * N : ℕ) : ℤ) ∣ γ 0 1) (hc : ((4 * N : ℕ) : ℤ) ∣ γ 1 0)
    (B : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ) :
    (A * B) (fz hN) (fz hN) = A (fz hN) (fz hN) * B (fz hN) (fz hN) := by
  obtain ⟨s, -, hd⟩ := weilWord_diag hN h hb hc
  rw [Matrix.mul_apply, Finset.sum_eq_single (fz hN)]
  · intro j _ hj
    rw [hd, if_neg, zero_mul]
    intro h'; apply hj
    have idx0 : weilIdx hN 0 = fz hN := ((eq_weilIdx_iff hN (fz hN) 0).2 (by simp [fz])).symm
    exact ((eq_weilIdx_iff hN j 0).2 (h'.trans (by simp [fz]))).trans idx0
  · simp

theorem modEq_zmod {M : ℕ} {a b : ℤ} : a ≡ b [ZMOD M] ↔ (a : ZMod M) = b :=
  (ZMod.intCast_eq_intCast_iff _ _ _).symm

/-- **(K) ∧ (D) → scalar law.** -/
theorem weilScalarLaw_of_kernel_torus (hK : WeilKernelLaw) (hD : WeilTorusLaw) :
    WeilScalarLaw := by
  intro N M hN h4N h24 ℓ hℓ ℓ' hℓ' γ h00 h11 h01 h10 A hA
  obtain ⟨γ₀, g00, g11, g01, g10, A₀, hA₀, hJ⟩ := hD N M hN h4N h24 ℓ hℓ ℓ' hℓ'
  obtain ⟨B, hB⟩ := exists_weilWord N γ₀⁻¹
  have inv_apply : (γ₀⁻¹) 0 0 = γ₀ 1 1 ∧ (γ₀⁻¹) 0 1 = -γ₀ 0 1 ∧ (γ₀⁻¹) 1 0 = -γ₀ 1 0 ∧
      (γ₀⁻¹) 1 1 = γ₀ 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  obtain ⟨i00, i01, i10, i11⟩ := inv_apply
  -- `A₀ B` is a word of `1`
  have h1 := hK N M hN h4N h24 _ (by simp) (by simp) (by simp) (by simp) _
    ((mul_inv_cancel γ₀) ▸ hA₀.mul hB)
  -- `B A` is a word of `γ₀⁻¹ γ ∈ Γ(M)`
  have e : ∀ i j, (γ₀⁻¹ * γ) i j = ∑ k, (γ₀⁻¹) i k * γ k j := fun i j => by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [modEq_zmod] at h00 h11 h01 h10 g00 g11 g01 g10 hℓ'
  push_cast at h00 h11 h01 h10 g00 g11 g01 g10 hℓ'
  have h2 := hK N M hN h4N h24 (γ₀⁻¹ * γ)
    (by rw [modEq_zmod, e]; simp only [Fin.sum_univ_two, i00, i01]; push_cast
        rw [h00, h10, g11, g01]; linear_combination hℓ')
    (by rw [modEq_zmod, e]; simp only [Fin.sum_univ_two, i10, i11]; push_cast
        rw [h01, h11, g10, g00]; linear_combination hℓ')
    (by rw [modEq_zmod, e]; simp only [Fin.sum_univ_two, i00, i01]; push_cast
        rw [h01, h11, g11, g01]; ring)
    (by rw [modEq_zmod, e]; simp only [Fin.sum_univ_two, i10, i11]; push_cast
        rw [h00, h10, g10, g00]; ring)
    _ (hB.mul hA)
  have hdvd : ∀ {x : ℤ}, (x : ZMod M) = 0 → ((4 * N : ℕ) : ℤ) ∣ x := fun hx =>
    dvd_of_modEq_zero h4N ((modEq_zmod).2 (by simpa using hx))
  rw [weilWord_row_zero hN hA₀ (hdvd g01) (hdvd g10)] at h1
  rw [weilWord_row_zero hN hB (by rw [i01]; exact (hdvd g01).neg_right)
    (by rw [i10]; exact (hdvd g10).neg_right)] at h2
  rw [← hJ]
  calc A (fz hN) (fz hN) = A (fz hN) (fz hN) * (A₀ (fz hN) (fz hN) * B (fz hN) (fz hN)) := by
        rw [h1, mul_one]
    _ = A₀ (fz hN) (fz hN) * (B (fz hN) (fz hN) * A (fz hN) (fz hN)) := by ring
    _ = A₀ (fz hN) (fz hN) := by rw [h2, mul_one]

/-- **G4 reduction, split form**: `WeilGaloisLaw` follows from the congruence property (K) and
the torus law (D). -/
theorem weilGaloisLaw_of_kernel_torus (hK : WeilKernelLaw) (hD : WeilTorusLaw) :
    WeilGaloisLaw :=
  weilGaloisLaw_of_weilScalarLaw (weilScalarLaw_of_kernel_torus hK hD)

/-! ## The torus representative `𝔡 = T^ℓ S T^m S T^ℓ S⁻¹` -/

/-- `𝔡(ℓ, m) = T^ℓ S T^m S T^ℓ S⁻¹`; for `ℓm ≡ 1 (mod M)` it is `≡ diag(ℓ, m) (mod M)`. -/
def dl (ℓ m : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ModularGroup.T ^ ℓ * (ModularGroup.S * (ModularGroup.T ^ m * (ModularGroup.S *
    (ModularGroup.T ^ ℓ * (ModularGroup.S⁻¹ * 1)))))

/-- The Weil word matrix of `𝔡(ℓ, m)`. -/
def dlMat (N ℓ m : ℕ) : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  weilT N ^ ℓ * (weilS N * (weilT N ^ m * (weilS N * (weilT N ^ ℓ * (weilS N * 1)))))

theorem _root_.VOA.Classification.COne.WeilWord.Tpow {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {A : Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ} (h : WeilWord N γ A) (n : ℕ) :
    WeilWord N (ModularGroup.T ^ n * γ) (weilT N ^ n * A) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_assoc, Matrix.mul_assoc]
    exact WeilWord.T ih

theorem dl_weilWord (N ℓ m : ℕ) : WeilWord N (dl ℓ m) (dlMat N ℓ m) :=
  ((((WeilWord.one.Sinv.Tpow ℓ).S.Tpow m).S).Tpow ℓ)

open ModularGroup in
theorem dl_apply (ℓ m : ℕ) :
    dl ℓ m 0 0 = ℓ * (1 - (ℓ * m - 1)) ∧ dl ℓ m 0 1 = ℓ * m - 1 ∧
      dl ℓ m 1 0 = -(ℓ * m - 1) ∧ dl ℓ m 1 1 = m := by
  have hT : ∀ n : ℕ, ((T ^ n : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![1, (n : ℤ); 0, 1] := fun n => by rw [← zpow_natCast, coe_T_zpow]
  simp only [dl, mul_one, Matrix.SpecialLinearGroup.coe_mul, hT, coe_S,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The quadratic Gauss sum `G_a = ∑_{k mod 2N} e(a k²/4N)`. -/
def gaussG (N : ℕ) (a : ℤ) : ℂ := ∑ k : Fin (2 * N), e4 N (a * ((k : ℕ) : ℤ) ^ 2)

/-- `ω = e(−1/24)`. -/
def omega24 : ℂ := cexp (-(2 * Real.pi * I / 24))

theorem e4_pow (N n : ℕ) (a : ℤ) : e4 N a ^ n = e4 N (n * a) := by
  induction n with
  | zero => simp [e4_zero]
  | succ n ih => rw [pow_succ, ih, ← e4_add]; congr 1; push_cast; ring

theorem weilT_pow (N n : ℕ) : weilT N ^ n =
    Matrix.diagonal fun μ : Fin (2 * N) => e4 N (n * ((μ : ℕ) : ℤ) ^ 2) * omega24 ^ n := by
  rw [weilT, Matrix.diagonal_pow]
  congr 1; funext μ
  rw [Pi.pow_apply, weilPhase_eq, mul_pow, e4_pow, omega24]

theorem sum_fin_shift (hN : 0 < N) (f : ℤ → ℂ) (hf : ∀ x, f (x + 2 * N) = f x) (t : ℤ) :
    ∑ k : Fin (2 * N), f (((k : ℕ) : ℤ) + t) = ∑ k : Fin (2 * N), f ((k : ℕ) : ℤ) := by
  have hinj : Function.Injective fun k : Fin (2 * N) => weilIdx hN (((k : ℕ) : ℤ) + t) := by
    intro k k' hk
    have h1 := (weilIdx_modEq hN (((k : ℕ) : ℤ) + t)).symm.trans
      ((congrArg (fun i : Fin (2 * N) => ((i : ℕ) : ℤ)) hk ▸ weilIdx_modEq hN (((k' : ℕ) : ℤ) + t)))
    have h2 := Int.ModEq.add_right_cancel' t h1
    rw [← weilIdx_fin hN k, ← weilIdx_fin hN k']
    exact weilIdx_congr hN h2
  let e := Equiv.ofBijective _ hinj.bijective_of_finite
  calc ∑ k : Fin (2 * N), f (((k : ℕ) : ℤ) + t)
      = ∑ k : Fin (2 * N), f (((e k : ℕ) : ℤ)) :=
        Finset.sum_congr rfl fun k _ => periodic_congr hf (weilIdx_modEq hN _).symm
    _ = ∑ k : Fin (2 * N), f ((k : ℕ) : ℤ) := Equiv.sum_comp e (fun k => f ((k : ℕ) : ℤ))

theorem dlMat_apply (hN : 0 < N) (ℓ m : ℕ) (h : (ℓ : ℤ) * m ≡ 1 [ZMOD (4 * N : ℕ)]) :
    dlMat N ℓ m (fz hN) (fz hN) =
      omega24 ^ (2 * ℓ + m) * gaussG N ℓ * ((Real.sqrt (2 * N))⁻¹ : ℝ) := by
  obtain ⟨t, ht⟩ := exists_of_modEq h
  set c : ℂ := (((Real.sqrt (2 * N))⁻¹ : ℝ) : ℂ) with hcdef
  have hc : c ^ 2 * (2 * N) = 1 := by
    have h0 : (0 : ℝ) ≤ 2 * N := by positivity
    have hN' : (2 * N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := Nat.cast_pos.2 hN; positivity
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hcdef, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt h0]
    push_cast; field_simp
  have inner : ∀ j : ℤ, ∑ k : Fin (2 * N), e4 N (2 * ((k : ℕ) : ℤ) * j) *
      e4 N (ℓ * ((k : ℕ) : ℤ) ^ 2) = e4 N (-(m * j ^ 2)) * gaussG N ℓ := by
    intro j
    have hf : ∀ x : ℤ, e4 N (ℓ * (x + 2 * N) ^ 2) = e4 N (ℓ * x ^ 2) := fun x =>
      e4_eq_of_eq hN ⟨ℓ * x + ℓ * N, by ring⟩
    have hs := sum_fin_shift hN (fun x => e4 N (ℓ * x ^ 2)) hf (m * j)
    simp only at hs
    rw [gaussG, ← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e4_add, ← e4_add]
    refine e4_eq_of_eq hN ⟨t * (2 * ((k : ℕ) : ℤ) * j + m * j ^ 2), ?_⟩
    push_cast at ht
    linear_combination (2 * ((k : ℕ) : ℤ) * j + m * j ^ 2) * ht
  have hS : ∀ μ j : Fin (2 * N), weilS N μ j = c * e4 N (2 * ((j : ℕ) : ℤ) * ((μ : ℕ) : ℤ)) :=
    weilS_apply N
  have hfz : (((fz hN : Fin (2 * N)) : ℕ) : ℤ) = 0 := by simp [fz]
  unfold dlMat
  simp only [weilT_pow, Matrix.mul_apply, hS, hfz, Matrix.diagonal_apply, Matrix.one_apply]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [hfz, mul_zero, e4_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, one_mul, zero_mul]
  have hin : ∀ x : Fin (2 * N), (∑ k : Fin (2 * N), c * e4 N (2 * ((k : ℕ) : ℤ) * ((x : ℕ) : ℤ)) *
      (e4 N (ℓ * ((k : ℕ) : ℤ) ^ 2) * omega24 ^ ℓ * c)) =
      c ^ 2 * omega24 ^ ℓ * (e4 N (-(m * ((x : ℕ) : ℤ) ^ 2)) * gaussG N ℓ) := by
    intro x
    rw [← inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hin]
  have hout : ∀ x : Fin (2 * N), c * (e4 N (m * ((x : ℕ) : ℤ) ^ 2) * omega24 ^ m *
      (c ^ 2 * omega24 ^ ℓ * (e4 N (-(m * ((x : ℕ) : ℤ) ^ 2)) * gaussG N ℓ))) =
      c ^ 3 * omega24 ^ (m + ℓ) * gaussG N ℓ := by
    intro x
    have : e4 N (m * ((x : ℕ) : ℤ) ^ 2) * e4 N (-(m * ((x : ℕ) : ℤ) ^ 2)) = 1 := by
      rw [← e4_add, add_neg_cancel, e4_zero]
    linear_combination (c ^ 3 * omega24 ^ (m + ℓ) * gaussG N ℓ) * this
  simp_rw [hout]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linear_combination (omega24 ^ (2 * ℓ + m) * gaussG N ℓ * c) * hc

/-! ## The torus law from the kernel law and the Gauss ratio law -/

/-- **The Gauss ratio law** (classical and sign-free): for `ℓ` prime to `2N`,
`∑_{k mod 2N} e(ℓk²/4N) = (2N/ℓ) e((ℓ−1)/8) ∑_{k mod 2N} e(k²/4N)`. -/
def GaussRatioLaw : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ ℓ : ℕ, ℓ.Coprime (2 * N) →
    gaussG N ℓ = (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) *
      cexp (2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8) * gaussG N 1

theorem self_inverse_mod24 : ∀ x y : ZMod 24, x * y = 1 → x = y := by decide

theorem exists_nat_modEq {M ℓ : ℕ} {ℓ' : ℤ} (h : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M]) :
    ∃ m : ℕ, (m : ℤ) ≡ ℓ' [ZMOD M] := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h1 : (ℓ : ℤ) * ℓ' = 1 := by simpa [Int.ModEq] using h
    have hpos : 0 ≤ ℓ' := by
      by_contra hneg
      have : (ℓ : ℤ) * ℓ' ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith
    exact ⟨ℓ'.toNat, by rw [Int.toNat_of_nonneg hpos]⟩
  · exact ⟨(ℓ' % M).toNat, by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]; exact Int.mod_modEq _ _⟩

/-- **(K) ∧ Gauss ratio law → (D).** The kernel law on the relation word `𝔡(1,1) = 1` gives
`G_1 = e(1/8) √(2N)` (Gauss's sign); the ratio law then evaluates `𝔡(ℓ, m)`. -/
theorem weilTorusLaw_of_kernel_gauss (hK : WeilKernelLaw) (hG : GaussRatioLaw) :
    WeilTorusLaw := by
  intro N M hN h4N h24 ℓ hℓ ℓ' hℓ'
  obtain ⟨m, hm⟩ := exists_nat_modEq hℓ'
  have hlm : (ℓ : ℤ) * m ≡ 1 [ZMOD M] := (hm.mul_left _).trans hℓ'
  have hlm4 : (ℓ : ℤ) * m ≡ 1 [ZMOD (4 * N : ℕ)] :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h4N) hlm
  have hlm24 : (ℓ : ℤ) * m ≡ 1 [ZMOD (24 : ℕ)] :=
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h24) hlm
  obtain ⟨d00, d01, d10, d11⟩ := dl_apply ℓ m
  refine ⟨dl ℓ m, ?_, ?_, ?_, ?_, dlMat N ℓ m, dl_weilWord N ℓ m, ?_⟩
  · rw [d00, modEq_zmod]; rw [modEq_zmod] at hlm; push_cast at hlm ⊢
    linear_combination (-(ℓ : ZMod M)) * hlm
  · rw [d11]; exact hm
  · rw [d01, modEq_zmod]; rw [modEq_zmod] at hlm; push_cast at hlm ⊢
    linear_combination hlm
  · rw [d10, modEq_zmod]; rw [modEq_zmod] at hlm; push_cast at hlm ⊢
    linear_combination -hlm
  -- Gauss's sign from the relation word `𝔡(1,1) = 1`
  have h11 := hK N M hN h4N h24 (dl 1 1)
    (by rw [(dl_apply 1 1).1]; norm_num) (by rw [(dl_apply 1 1).2.2.2]; norm_num)
    (by rw [(dl_apply 1 1).2.1]; norm_num) (by rw [(dl_apply 1 1).2.2.1]; norm_num)
    _ (dl_weilWord N 1 1)
  rw [dlMat_apply hN 1 1 (by norm_num)] at h11
  have h2N : 2 * N ∣ M := (Dvd.intro_left 2 (by ring) : 2 * N ∣ 4 * N).trans h4N
  have hℓ2N : ℓ.Coprime (2 * N) := Nat.Coprime.coprime_dvd_right h2N hℓ
  rw [dlMat_apply hN ℓ m hlm4, hG N hN ℓ hℓ2N]
  -- `m ≡ ℓ (mod 24)`
  have hℓ24 : ℓ.Coprime 24 := Nat.Coprime.coprime_dvd_right h24 hℓ
  have hml : (ℓ : ZMod 24) = m := by
    apply self_inverse_mod24
    have := (modEq_zmod).1 hlm24
    push_cast at this; exact this
  obtain ⟨q, hq⟩ : ∃ q : ℤ, (ℓ : ℤ) = m + 24 * q := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (m : ℤ) (ℓ : ℤ) 24).1 (by exact_mod_cast hml.symm)
    obtain ⟨q, hq⟩ := this
    exact ⟨q, by push_cast at hq; linarith⟩
  have hphase : omega24 ^ (2 * ℓ + m) * cexp (2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8) =
      omega24 ^ 3 := by
    unfold omega24
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hq' : (ℓ : ℂ) = m + 24 * q := by exact_mod_cast hq
    rw [show ((2 * ℓ + m : ℕ) : ℂ) * -(2 * Real.pi * I / 24) + 2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8
        = ((3 : ℕ) : ℂ) * -(2 * Real.pi * I / 24) + (q : ℂ) * (2 * Real.pi * I) by
          push_cast; rw [hq']; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  linear_combination (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) * h11 +
    (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) * gaussG N 1 * (((Real.sqrt (2 * N))⁻¹ : ℝ) : ℂ) * hphase

/-- **G4, reduced**: `WeilGaloisLaw` follows from the congruence property (K) and the classical
sign-free Gauss ratio law. -/
theorem weilGaloisLaw_of_kernel_gauss (hK : WeilKernelLaw) (hG : GaussRatioLaw) :
    WeilGaloisLaw :=
  weilGaloisLaw_of_kernel_torus hK (weilTorusLaw_of_kernel_gauss hK hG)

/-! ## Quadratic Gauss sums `g(c, a) = ∑_{x mod c} e(a x²/c)` -/

/-- `E_c(t) = e(t/c)`. -/
def E (c : ℕ) (t : ℤ) : ℂ := cexp (2 * Real.pi * I * (t : ℂ) / c)

theorem E_add (c : ℕ) (s t : ℤ) : E c (s + t) = E c s * E c t := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem E_zero (c : ℕ) : E c 0 = 1 := by simp [E]

theorem E_mul_self {c : ℕ} (hc : 0 < c) (k : ℤ) : E c (c * k) = 1 := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  unfold E
  rw [show 2 * Real.pi * I * (((c * k : ℤ)) : ℂ) / c = k * (2 * Real.pi * I) by
    push_cast; field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem E_period {c : ℕ} (hc : 0 < c) (t k : ℤ) : E c (t + c * k) = E c t := by
  rw [E_add, E_mul_self hc, mul_one]

theorem E_congr {c : ℕ} (hc : 0 < c) {t t' : ℤ} (h : t ≡ t' [ZMOD c]) : E c t = E c t' := by
  obtain ⟨k, hk⟩ := exists_of_modEq h
  rw [hk, E_period hc]

/-- `E_{rs}(s t) = E_r(t)`. -/
theorem E_mul_left {r s : ℕ} (hs : 0 < s) (t : ℤ) : E (r * s) (s * t) = E r t := by
  have hs' : (s : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hs.ne'
  unfold E; congr 1; push_cast; field_simp

theorem E_eq_one_iff {c : ℕ} (hc : 0 < c) (t : ℤ) : E c t = 1 ↔ (c : ℤ) ∣ t := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  constructor
  · intro h
    unfold E at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (t : ℂ) = c * n := by
      field_simp at hn
      linear_combination hn
    exact ⟨n, by exact_mod_cast this⟩
  · rintro ⟨k, rfl⟩; exact E_mul_self hc k

theorem E_pow (c n : ℕ) (t : ℤ) : E c t ^ n = E c (n * t) := by
  induction n with
  | zero => simp [E_zero]
  | succ n ih => rw [pow_succ, ih, ← E_add]; congr 1; push_cast; ring

/-- Orthogonality: `∑_{z mod c} e(tz/c) = 0` unless `c ∣ t`. -/
theorem sum_E_eq_zero {c : ℕ} (hc : 0 < c) {t : ℤ} (ht : ¬ (c : ℤ) ∣ t) :
    ∑ z : Fin c, E c (t * ((z : ℕ) : ℤ)) = 0 := by
  have h1 : E c t ≠ 1 := fun h => ht ((E_eq_one_iff hc t).1 h)
  have h2 : ∀ z : ℕ, E c (t * (z : ℤ)) = E c t ^ z := fun z => by
    rw [E_pow]; congr 1; ring
  simp_rw [h2]
  rw [Fin.sum_univ_eq_sum_range (fun z => E c t ^ z) c, geom_sum_eq h1, E_pow,
    show ((c : ℤ) * t) = c * t from rfl, E_mul_self hc, sub_self, zero_div]

/-! ### Complete residue systems -/

/-- The representative in `Fin c` of `z mod c`. -/
def idxc {c : ℕ} (hc : 0 < c) (z : ℤ) : Fin c :=
  ⟨(z % c).toNat, by
    have h1 : 0 ≤ z % (c : ℤ) := Int.emod_nonneg _ (by omega)
    have h2 : z % (c : ℤ) < c := Int.emod_lt_of_pos _ (by omega)
    omega⟩

theorem idxc_modEq {c : ℕ} (hc : 0 < c) (z : ℤ) : (((idxc hc z : ℕ)) : ℤ) ≡ z [ZMOD c] := by
  have h1 : 0 ≤ z % (c : ℤ) := Int.emod_nonneg _ (by omega)
  simp only [idxc, Int.toNat_of_nonneg h1]
  exact Int.mod_modEq _ _

theorem fin_eq_of_modEq {c : ℕ} {i j : Fin c} (h : ((i : ℕ) : ℤ) ≡ ((j : ℕ) : ℤ) [ZMOD c]) :
    i = j := by
  have hi : ((i : ℕ) : ℤ) % c = (i : ℕ) := Int.emod_eq_of_lt (by omega) (by have := i.2; omega)
  have hj : ((j : ℕ) : ℤ) % c = (j : ℕ) := Int.emod_eq_of_lt (by omega) (by have := j.2; omega)
  unfold Int.ModEq at h
  rw [hi, hj] at h
  exact Fin.ext (by exact_mod_cast h)

theorem periodic_congr' {c : ℕ} {f : ℤ → ℂ} (hf : ∀ x, f (x + c) = f x) {a b : ℤ}
    (h : a ≡ b [ZMOD c]) : f a = f b := by
  obtain ⟨k, rfl⟩ := exists_of_modEq h
  have key : ∀ k : ℤ, f (a + (c : ℤ) * k) = f a := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [← ih, show a + (c : ℤ) * (k + 1) = a + c * k + c by ring, hf]
    | pred k ih =>
      rw [← ih, show a + (c : ℤ) * (-(k : ℤ)) = a + c * (-(k : ℤ) - 1) + c by ring, hf]
  exact (key k).symm

/-- Summing a `c`-periodic function over any complete residue system. -/
theorem resid_sum {c : ℕ} (hc : 0 < c) (f : ℤ → ℂ) (hf : ∀ x, f (x + c) = f x)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = c) (φ : ι → ℤ)
    (hφ : ∀ i j, φ i ≡ φ j [ZMOD c] → i = j) :
    ∑ i, f (φ i) = ∑ x : Fin c, f ((x : ℕ) : ℤ) := by
  have hinj : Function.Injective fun i => idxc hc (φ i) := by
    intro i j h
    apply hφ
    have := congrArg (fun x : Fin c => ((x : ℕ) : ℤ)) h
    simp only at this
    exact (idxc_modEq hc (φ i)).symm.trans (this ▸ idxc_modEq hc (φ j))
  have hbij : Function.Bijective fun i => idxc hc (φ i) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [hcard]⟩
  let e := Equiv.ofBijective _ hbij
  calc ∑ i, f (φ i) = ∑ i, f (((e i : ℕ) : ℤ)) :=
        Finset.sum_congr rfl fun i _ => periodic_congr' hf (idxc_modEq hc (φ i)).symm
    _ = ∑ x : Fin c, f ((x : ℕ) : ℤ) := Equiv.sum_comp e (fun x => f ((x : ℕ) : ℤ))

/-- `∑_{x mod mn} F(x) = ∑_{y mod m} ∑_{z mod n} F(y + mz)`. -/
theorem sum_split {c m n : ℕ} (hmn : c = m * n) (hc : 0 < c) (F : ℤ → ℂ)
    (hF : ∀ x, F (x + c) = F x) :
    ∑ x : Fin c, F ((x : ℕ) : ℤ) =
      ∑ y : Fin m, ∑ z : Fin n, F (((y : ℕ) : ℤ) + m * ((z : ℕ) : ℤ)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
  rw [← Fintype.sum_prod_type']
  refine (resid_sum hc F hF (by simp [hmn])
    (fun q : Fin m × Fin n => ((q.1 : ℕ) : ℤ) + m * ((q.2 : ℕ) : ℤ))
    ?_).symm
  rintro ⟨y, z⟩ ⟨y', z'⟩ h
  have hc' : ((c : ℕ) : ℤ) = m * n := by rw [hmn]; push_cast; ring
  have hm' : ((y : ℕ) : ℤ) ≡ ((y' : ℕ) : ℤ) [ZMOD m] := by
    have := Int.ModEq.of_dvd (⟨n, hc'⟩ : (m : ℤ) ∣ c) h
    simpa [Int.ModEq] using this
  have hy := fin_eq_of_modEq hm'
  subst hy
  have h2 : (m : ℤ) * ((z : ℕ) : ℤ) ≡ m * ((z' : ℕ) : ℤ) [ZMOD m * n] := by
    rw [← hc']; exact Int.ModEq.add_left_cancel' _ h
  have h3 : ((z : ℕ) : ℤ) ≡ ((z' : ℕ) : ℤ) [ZMOD n] :=
    Int.ModEq.mul_left_cancel' (by exact_mod_cast hm.ne') h2
  rw [fin_eq_of_modEq h3]

/-! ### Gauss sums: definition, CRT, link with `gaussG` -/

/-- `g(c, a) = ∑_{x mod c} e(a x²/c)`. -/
def gs (c : ℕ) (a : ℤ) : ℂ := ∑ x : Fin c, E c (a * ((x : ℕ) : ℤ) ^ 2)

theorem gs_periodic {c : ℕ} (hc : 0 < c) (a x : ℤ) :
    E c (a * (x + c) ^ 2) = E c (a * x ^ 2) := by
  rw [← E_period hc (a * x ^ 2) (a * (2 * x + c))]; congr 1; ring

theorem gs_one_mod (a : ℤ) : gs 1 a = 1 := by simp [gs, E_zero]

/-- **CRT for Gauss sums**: `g(rs, a) = g(r, as) g(s, ar)` for coprime `r, s`. -/
theorem gs_crt {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (h : r.Coprime s) (a : ℤ) :
    gs (r * s) a = gs r (a * s) * gs s (a * r) := by
  have hrs : 0 < r * s := Nat.mul_pos hr hs
  unfold gs
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  rw [← resid_sum hrs (fun x => E (r * s) (a * x ^ 2)) (gs_periodic hrs a) (by simp)
    (fun q : Fin r × Fin s => (s : ℤ) * ((q.1 : ℕ) : ℤ) + r * ((q.2 : ℕ) : ℤ))]
  · refine Finset.sum_congr rfl fun q _ => ?_
    set y : ℤ := ((q.1 : ℕ) : ℤ)
    set z : ℤ := ((q.2 : ℕ) : ℤ)
    have e1 : a * ((s : ℤ) * y + r * z) ^ 2 =
        (s : ℤ) * (a * s * y ^ 2) +
          ((r : ℤ) * (a * r * z ^ 2) + ((r * s : ℕ) : ℤ) * (2 * a * y * z))
        := by push_cast; ring
    rw [e1, E_add, E_add, E_mul_self hrs, mul_one, E_mul_left hs,
      show r * s = s * r from Nat.mul_comm r s, E_mul_left hr]
  · rintro ⟨y, z⟩ ⟨y', z'⟩ hq
    simp only at hq
    have hg : Int.gcd s r = 1 := by rw [Int.gcd_natCast_natCast]; exact h.symm
    have hg1 : Int.gcd r s = 1 := by rw [Int.gcd_natCast_natCast]; exact h
    have hr' : ((y : ℕ) : ℤ) ≡ ((y' : ℕ) : ℤ) [ZMOD r] := by
      have h1 := Int.ModEq.of_dvd (⟨s, by push_cast; ring⟩ : (r : ℤ) ∣ ((r * s : ℕ) : ℤ)) hq
      have h2 : (s : ℤ) * ((y : ℕ) : ℤ) ≡ s * ((y' : ℕ) : ℤ) [ZMOD r] := by
        have := (h1.add_right (-(r * ((z' : ℕ) : ℤ))))
        have e : (s : ℤ) * ((y : ℕ) : ℤ) + r * ((z : ℕ) : ℤ) + -(r * ((z' : ℕ) : ℤ)) =
            s * ((y : ℕ) : ℤ) + r * (((z : ℕ) : ℤ) - ((z' : ℕ) : ℤ)) := by ring
        rw [e, show (s : ℤ) * ((y' : ℕ) : ℤ) + r * ((z' : ℕ) : ℤ) + -(r * ((z' : ℕ) : ℤ)) =
          s * ((y' : ℕ) : ℤ) by ring] at this
        refine this.symm.trans ?_ |>.symm
        exact (Int.modEq_iff_dvd.2 ⟨-(((z : ℕ) : ℤ) - ((z' : ℕ) : ℤ)), by ring⟩)
      have := Int.ModEq.cancel_left_div_gcd (by exact_mod_cast hr) h2
      rwa [hg1, Nat.cast_one, Int.ediv_one] at this
    have hs' : ((z : ℕ) : ℤ) ≡ ((z' : ℕ) : ℤ) [ZMOD s] := by
      have h1 := Int.ModEq.of_dvd (⟨r, by push_cast; ring⟩ : (s : ℤ) ∣ ((r * s : ℕ) : ℤ)) hq
      have h2 : (r : ℤ) * ((z : ℕ) : ℤ) ≡ r * ((z' : ℕ) : ℤ) [ZMOD s] := by
        have := (h1.add_right (-(s * ((y' : ℕ) : ℤ))))
        rw [show (s : ℤ) * ((y : ℕ) : ℤ) + r * ((z : ℕ) : ℤ) + -(s * ((y' : ℕ) : ℤ)) =
            r * ((z : ℕ) : ℤ) + s * (((y : ℕ) : ℤ) - ((y' : ℕ) : ℤ)) by ring,
          show (s : ℤ) * ((y' : ℕ) : ℤ) + r * ((z' : ℕ) : ℤ) + -(s * ((y' : ℕ) : ℤ)) =
            r * ((z' : ℕ) : ℤ) by ring] at this
        refine this.symm.trans ?_ |>.symm
        exact (Int.modEq_iff_dvd.2 ⟨-(((y : ℕ) : ℤ) - ((y' : ℕ) : ℤ)), by ring⟩)
      have := Int.ModEq.cancel_left_div_gcd (by exact_mod_cast hs) h2
      rwa [hg, Nat.cast_one, Int.ediv_one] at this
    rw [fin_eq_of_modEq hr', fin_eq_of_modEq hs']

theorem E_four_mul (N : ℕ) (t : ℤ) : E (4 * N) t = e4 N t := by
  unfold E e4; push_cast; rfl

/-- `g(4N, a) = 2 G_N(a)`. -/
theorem gs_four_mul (hN : 0 < N) (a : ℤ) : gs (4 * N) a = 2 * gaussG N a := by
  have h4 : 0 < 4 * N := by omega
  unfold gs gaussG
  have hsplit := sum_split (c := 4 * N) (m := 2 * N) (n := 2) (by ring) h4
    (fun x => E (4 * N) (a * x ^ 2)) (gs_periodic h4 a)
  simp only at hsplit
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.sum_univ_two]
  have : ∀ t : ℤ, E (4 * N) (a * (((y : ℕ) : ℤ) + ((2 * N : ℕ) : ℤ) * t) ^ 2) =
      e4 N (a * ((y : ℕ) : ℤ) ^ 2) := by
    intro t
    rw [← E_four_mul, ← E_period h4 (a * ((y : ℕ) : ℤ) ^ 2) (a * ((y : ℕ) : ℤ) * t + a * N * t ^ 2)]
    congr 1; push_cast; ring
  have h0 := this 0
  have h1 := this 1
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
  rw [h0, h1]; ring

/-! ### Odd prime-square reduction `g(p²c, b) = p g(c, b)` -/

theorem gs_p2 {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : 0 < c) {b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) : gs (p ^ 2 * c) b = p * gs c b := by
  have hp0 : 0 < p := hp.pos
  have hpc : 0 < p * c := Nat.mul_pos hp0 hc
  have hP : 0 < p ^ 2 * c := by positivity
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hidx : p ^ 2 * c = p * (p * c) := by ring
  -- step 1: split `x = y + pc z`
  have hsplit := sum_split (c := p ^ 2 * c) (m := p * c) (n := p) (by ring) hP
    (fun x => E (p ^ 2 * c) (b * x ^ 2)) (gs_periodic hP b)
  simp only at hsplit
  -- the inner sum
  have inner : ∀ y : ℤ, ∑ z : Fin p, E (p ^ 2 * c) (b * (y + ((p * c : ℕ) : ℤ) * ((z : ℕ) : ℤ)) ^ 2)
      = E (p ^ 2 * c) (b * y ^ 2) * (if (p : ℤ) ∣ y then (p : ℂ) else 0) := by
    intro y
    have e : ∀ z : ℤ, E (p ^ 2 * c) (b * (y + ((p * c : ℕ) : ℤ) * z) ^ 2) =
        E (p ^ 2 * c) (b * y ^ 2) * E p ((2 * b * y) * z) := by
      intro z
      rw [show b * (y + ((p * c : ℕ) : ℤ) * z) ^ 2 = b * y ^ 2 + ((p * c : ℕ) : ℤ) * (2 * b * y * z)
          + ((p ^ 2 * c : ℕ) : ℤ) * (b * c * z ^ 2) by push_cast; ring,
        E_add, E_add, E_mul_self hP, mul_one, hidx, E_mul_left hpc]
    simp_rw [e]
    rw [← Finset.mul_sum]
    congr 1
    split_ifs with hy
    · have : ∀ z : Fin p, E p (2 * b * y * ((z : ℕ) : ℤ)) = 1 := fun z =>
        (E_eq_one_iff hp0 _).2 (by
          obtain ⟨k, hk⟩ := hy; exact ⟨2 * b * k * ((z : ℕ) : ℤ), by rw [hk]; ring⟩)
      simp [this]
    · refine sum_E_eq_zero hp0 ?_
      intro hd
      rcases hpZ.dvd_or_dvd hd with hd | hd
      · rcases hpZ.dvd_or_dvd hd with hd | hd
        · have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
          have h2 : 2 ≤ p := hp.two_le
          omega
        · exact hb hd
      · exact hy hd
  -- the indicator sum is `pc`-periodic
  set G : ℤ → ℂ := fun y => if (p : ℤ) ∣ y then E (p ^ 2 * c) (b * y ^ 2) else 0 with hG
  have hGper : ∀ y, G (y + ((p * c : ℕ) : ℤ)) = G y := by
    intro y
    simp only [hG]
    have hd : (p : ℤ) ∣ y + ((p * c : ℕ) : ℤ) ↔ (p : ℤ) ∣ y :=
      (dvd_add_left (⟨c, by push_cast; ring⟩ : (p : ℤ) ∣ ((p * c : ℕ) : ℤ)))
    by_cases hy : (p : ℤ) ∣ y
    · rw [if_pos (hd.2 hy), if_pos hy]
      obtain ⟨k, rfl⟩ := hy
      rw [← E_period hP (b * (p * k) ^ 2) (2 * b * k + b * c)]
      congr 1; push_cast; ring
    · rw [if_neg (fun h => hy (hd.1 h)), if_neg hy]
  have hsum : gs (p ^ 2 * c) b = p * ∑ y : Fin (p * c), G ((y : ℕ) : ℤ) := by
    unfold gs; rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [inner]; simp only [hG]; split_ifs <;> ring
  rw [hsum]
  have hsplit2 := sum_split (c := p * c) (m := p) (n := c) rfl hpc G hGper
  rw [hsplit2, Finset.sum_eq_single (⟨0, hp0⟩ : Fin p)]
  · unfold gs; congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hG, Nat.cast_zero, zero_add]
    rw [if_pos (dvd_mul_right _ _), show p ^ 2 * c = c * p ^ 2 by ring,
      show b * ((p : ℤ) * ((w : ℕ) : ℤ)) ^ 2 = ((p ^ 2 : ℕ) : ℤ) * (b * ((w : ℕ) : ℤ) ^ 2) by
        push_cast; ring, E_mul_left (by positivity)]
  · intro r _ hr
    refine Finset.sum_eq_zero fun w _ => ?_
    simp only [hG]
    rw [if_neg]
    intro hd
    have h1 : (p : ℤ) ∣ ((r : ℕ) : ℤ) := (dvd_add_left (dvd_mul_right _ _)).1 hd
    have h2 : ((r : ℕ) : ℤ) < p := by exact_mod_cast r.2
    have h3 : 0 ≤ ((r : ℕ) : ℤ) := by positivity
    have : ((r : ℕ) : ℤ) = 0 := by
      obtain ⟨k, hk⟩ := h1
      have : k = 0 := by nlinarith
      rw [hk, this, mul_zero]
    exact hr (Fin.ext (by exact_mod_cast this))
  · simp

/-! ### Prime modulus: `g(p, b) = (b/p) g(p, 1)` -/

theorem gs_zmod (p : ℕ) [NeZero p] (a : ℤ) :
    gs p a = ∑ x : ZMod p, ZMod.stdAddChar ((a : ZMod p) * x ^ 2) := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold gs
  rw [← resid_sum hp0 (fun t => E p (a * t ^ 2)) (gs_periodic hp0 a) (ZMod.card p)
    (fun x : ZMod p => ((x.val : ℕ) : ℤ))]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [show ((a : ZMod p) * x ^ 2) = (((a * ((x.val : ℕ) : ℤ) ^ 2 : ℤ)) : ZMod p) by
      push_cast; rw [ZMod.natCast_zmod_val], ZMod.stdAddChar_coe]
    unfold E; congr 1
  · intro x y h
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 h
    push_cast at this
    simpa [ZMod.natCast_zmod_val] using this

theorem gs_prime {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) {b : ℤ} (hb : (b : ZMod p) ≠ 0) :
    gs p b = (legendreSym p b : ℂ) * gs p 1 := by
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  set χ : ZMod p → ℂ := fun y => ((quadraticChar (ZMod p) y : ℤ) : ℂ)
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  -- fibre count
  have fib : ∀ a : ZMod p, ∑ x : ZMod p, ψ (a * x ^ 2) = ∑ y : ZMod p, (χ y + 1) * ψ (a * y) := by
    intro a
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => ψ (a * y)) (fun x hx => by
      rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := quadraticChar_card_sqrts hF y
    have : ({x : ZMod p | x ^ 2 = y}.toFinset) = Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)
      := by ext; simp
    rw [this] at hc
    simp only [χ]
    exact_mod_cast hc
  -- the additive sum vanishes
  have van : ∀ a : ZMod p, a ≠ 0 → ∑ y : ZMod p, ψ (a * y) = 0 := by
    intro a ha
    have := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
    simpa [AddChar.mulShift_apply] using this
  -- twisting
  have tw : ∀ a : ZMod p, a ≠ 0 →
      ∑ y : ZMod p, χ y * ψ (a * y) = χ a * ∑ y : ZMod p, χ y * ψ y := by
    intro a ha
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun y => ?_)
    rw [show (Equiv.mulLeft₀ a ha) y = a * y from rfl]
    simp only [χ]
    rw [show quadraticChar (ZMod p) (a * y) = quadraticChar (ZMod p) a * quadraticChar (ZMod p) y
      from map_mul _ a y]
    have hsq := quadraticChar_sq_one ha
    push_cast
    have : ((quadraticChar (ZMod p) a : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
    linear_combination (-(((quadraticChar (ZMod p) y : ℤ) : ℂ) * ψ (a * y))) * this
  have main : ∀ a : ZMod p, a ≠ 0 →
      ∑ x : ZMod p, ψ (a * x ^ 2) = χ a * ∑ y : ZMod p, χ y * ψ y := by
    intro a ha
    rw [fib, ← tw a ha]
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib, van a ha, add_zero]
  rw [gs_zmod, gs_zmod, Int.cast_one, main _ hb, main _ one_ne_zero]
  simp [χ, legendreSym]

/-! ### Odd modulus: `g(n, b) = (b/n) g(n, 1)` -/

theorem not_dvd_of_coprime {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) {b : ℤ}
    (hb : Nat.Coprime b.natAbs n) : ¬ (p : ℤ) ∣ b := by
  intro h
  have h1 : p ∣ b.natAbs := Int.natCast_dvd.1 h
  have := Nat.dvd_gcd h1 hpn
  rw [hb] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem gs_jacobi : ∀ n : ℕ, Odd n → ∀ b : ℤ, Nat.Coprime b.natAbs n →
    gs n b = (jacobiSym b n : ℂ) * gs n 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn b hb
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have : n = 1 := by obtain ⟨k, rfl⟩ := hn; omega
    subst this; simp [gs_one_mod, jacobiSym.one_right]
  have hn1 : n ≠ 1 := by omega
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hp2 : p ≠ 2 := by
    intro h; rw [h] at hpn; exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 hpn)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hpn
  have hm0 : 0 < m := by rcases Nat.eq_zero_or_pos m with h | h <;> [simp [h] at hm; exact h]; omega
  have hmn : m < n := by rw [hm]; exact lt_mul_left hm0 hp.one_lt
  have hmodd : Odd m := (Nat.odd_mul.1 (hm ▸ hn)).2
  have hbp : ¬ (p : ℤ) ∣ b := not_dvd_of_coprime hp ⟨m, hm⟩ hb
  have hbm : Nat.Coprime b.natAbs m := Nat.Coprime.coprime_dvd_right ⟨p, by rw [hm]; ring⟩ hb
  by_cases hpm : p ∣ m
  · obtain ⟨c, hc⟩ := hpm
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h <;> [simp [h] at hc; exact h]; omega
    have hnc : n = p ^ 2 * c := by rw [hm, hc]; ring
    have hcn : c < n := by
      rw [hnc]; have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      exact lt_mul_left hc0 this
    have hcodd : Odd c := (Nat.odd_mul.1 (hnc ▸ hn)).2
    have hbc : Nat.Coprime b.natAbs c := Nat.Coprime.coprime_dvd_right ⟨p ^ 2, by rw [hnc]; ring⟩ hb
    have hJ : jacobiSym b n = jacobiSym b c := by
      rw [hnc, jacobiSym.mul_right' b (pow_pos hp.pos 2).ne' hc0.ne', jacobiSym.pow_right,
        jacobiSym.sq_one (by
          rw [Int.gcd, Int.natAbs_natCast]
          exact Nat.Coprime.coprime_dvd_right (⟨m, hm⟩ : p ∣ n) hb), one_mul]
    rw [hnc, gs_p2 hp hp2 hc0 hbp, gs_p2 hp hp2 hc0 (by
        intro h; exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)),
      ih c hcn hcodd b hbc, ← hnc, hJ]
    ring
  · have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    have hbmZ : ((b * m : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h
      rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
      · exact hbp h
      · exact hpm (Int.natCast_dvd_natCast.1 h)
    have hmZ : ((m : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h; exact hpm (Int.natCast_dvd_natCast.1 h)
    have hbpm : Nat.Coprime (b * p).natAbs m := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.Coprime.mul_left hbm hcop
    have hpm' : Nat.Coprime (p : ℤ).natAbs m := by rw [Int.natAbs_natCast]; exact hcop
    have e2 : gs (p * m) 1 = gs p m * gs m p := by rw [gs_crt hp.pos hm0 hcop]; simp
    rw [hm, gs_crt hp.pos hm0 hcop, e2, gs_prime hp2 hbmZ, gs_prime hp2 hmZ,
      ih m hmn hmodd _ hbpm, ih m hmn hmodd _ hpm',
      jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
      jacobiSym.mul_right' b hp.pos.ne' hm0.ne', jacobiSym.mul_left, jacobiSym.mul_left]
    push_cast
    ring

/-! ### Powers of two -/

/-- `g(2^{j+4}, b) = 2 g(2^{j+2}, b)` for odd `b`. -/
theorem gs_two_step (j : ℕ) {b : ℤ} (hb : Odd b) :
    gs (2 ^ (j + 4)) b = 2 * gs (2 ^ (j + 2)) b := by
  set K := 2 ^ (j + 2) with hK
  set K' := 2 ^ (j + 1) with hK'
  have hK0 : 0 < K := by positivity
  have hK'0 : 0 < K' := by positivity
  have h4K : 2 ^ (j + 4) = 4 * K := by rw [hK]; ring
  have hKK : K = 2 * K' := by rw [hK, hK']; ring
  have hP : 0 < 4 * K := by positivity
  -- step 1: `x = y + K z`
  have hsplit := sum_split (c := 4 * K) (m := K) (n := 4) (by ring) hP
    (fun x => E (4 * K) (b * x ^ 2)) (gs_periodic hP b)
  simp only at hsplit
  have inner : ∀ y : ℤ, ∑ z : Fin 4, E (4 * K) (b * (y + (K : ℤ) * ((z : ℕ) : ℤ)) ^ 2) =
      E (4 * K) (b * y ^ 2) * (if (2 : ℤ) ∣ y then 4 else 0) := by
    intro y
    have e : ∀ z : ℤ, E (4 * K) (b * (y + (K : ℤ) * z) ^ 2) =
        E (4 * K) (b * y ^ 2) * E 4 ((2 * b * y) * z) := by
      intro z
      rw [show b * (y + (K : ℤ) * z) ^ 2 = b * y ^ 2 + (K : ℤ) * (2 * b * y * z) +
          ((4 * K : ℕ) : ℤ) * (b * ((2 ^ j : ℕ) : ℤ) * z ^ 2) by
            rw [hK]; push_cast; ring,
        E_add, E_add, E_mul_self hP, mul_one, E_mul_left hK0]
    simp_rw [e]
    rw [← Finset.mul_sum]
    congr 1
    split_ifs with hy
    · have : ∀ z : Fin 4, E 4 (2 * b * y * ((z : ℕ) : ℤ)) = 1 := fun z =>
        (E_eq_one_iff (by norm_num) _).2 (by
          obtain ⟨k, hk⟩ := hy; exact ⟨b * k * ((z : ℕ) : ℤ), by rw [hk]; push_cast; ring⟩)
      simp [this]
    · refine sum_E_eq_zero (by norm_num) ?_
      rintro ⟨k, hk⟩
      apply hy
      obtain ⟨b', rfl⟩ := hb
      refine ⟨k - b' * y, ?_⟩
      push_cast at hk
      linarith
  -- the indicator function
  set G : ℤ → ℂ := fun y => if (2 : ℤ) ∣ y then E (4 * K) (b * y ^ 2) else 0 with hG
  have hGper : ∀ y, G (y + (K : ℤ)) = G y := by
    intro y
    simp only [hG]
    have hd : (2 : ℤ) ∣ y + (K : ℤ) ↔ (2 : ℤ) ∣ y :=
      dvd_add_left (⟨(K' : ℤ), by rw [hKK]; push_cast; ring⟩ : (2 : ℤ) ∣ (K : ℤ))
    by_cases hy : (2 : ℤ) ∣ y
    · rw [if_pos (hd.2 hy), if_pos hy]
      obtain ⟨k, rfl⟩ := hy
      rw [← E_period hP (b * (2 * k) ^ 2) (b * k + b * ((2 ^ j : ℕ) : ℤ))]
      congr 1; rw [hKK, hK']; push_cast; ring
    · rw [if_neg (fun h => hy (hd.1 h)), if_neg hy]
  have hsum : gs (4 * K) b = 4 * ∑ y : Fin K, G ((y : ℕ) : ℤ) := by
    unfold gs; rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [inner]; simp only [hG]; split_ifs <;> ring
  -- reindex the even `y`
  have hsplit2 := sum_split (c := K) (m := 2) (n := K') hKK hK0 G hGper
  have hev : ∑ y : Fin K, G ((y : ℕ) : ℤ) = ∑ w : Fin K', E K (b * ((w : ℕ) : ℤ) ^ 2) := by
    rw [hsplit2, Fin.sum_univ_two]
    have h1 : ∀ w : Fin K', G (((1 : Fin 2) : ℕ) + ((2 : ℕ) : ℤ) * ((w : ℕ) : ℤ)) = 0 := by
      intro w
      simp only [hG, Fin.val_one, Nat.cast_one]
      rw [if_neg]
      rintro ⟨k, hk⟩; push_cast at hk; omega
    simp only [h1, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hG, Fin.val_zero, Nat.cast_zero, zero_add, Nat.cast_ofNat]
    rw [if_pos (dvd_mul_right _ _), show 4 * K = K * 4 by ring,
      show b * (2 * ((w : ℕ) : ℤ)) ^ 2 = ((4 : ℕ) : ℤ) * (b * ((w : ℕ) : ℤ) ^ 2) by push_cast; ring,
      E_mul_left (by norm_num)]
  -- halve `g(K, b)`
  have hhalf : gs K b = 2 * ∑ w : Fin K', E K (b * ((w : ℕ) : ℤ) ^ 2) := by
    have hsplit3 := sum_split (c := K) (m := K') (n := 2) (by rw [hKK]; ring) hK0
      (fun x => E K (b * x ^ 2)) (gs_periodic hK0 b)
    simp only at hsplit3
    unfold gs; rw [hsplit3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two]
    have : ∀ t : ℤ, E K (b * (((w : ℕ) : ℤ) + (K' : ℤ) * t) ^ 2) = E K (b * ((w : ℕ) : ℤ) ^ 2) := by
      intro t
      rw [← E_period hK0 (b * ((w : ℕ) : ℤ) ^ 2)
        (b * ((w : ℕ) : ℤ) * t + b * ((2 ^ j : ℕ) : ℤ) * t ^ 2)]
      congr 1
      have e1 : (K : ℤ) = 2 * (K' : ℤ) := by rw [hKK]; push_cast; ring
      have e2 : (K' : ℤ) = 2 * ((2 ^ j : ℕ) : ℤ) := by rw [hK']; push_cast; ring
      linear_combination (-(b * ((w : ℕ) : ℤ) * t + b * ((2 ^ j : ℕ) : ℤ) * t ^ 2)) * e1 +
        (b * (K' : ℤ) * t ^ 2) * e2
    have h0 := this 0
    have h1 := this 1
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] at h0 h1 ⊢
    rw [h0, h1]; ring
  rw [h4K, hsum, hev, hhalf]; ring

theorem gs_four (b : ℤ) : gs 4 b = 2 + 2 * E 4 b := by
  unfold gs
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have h3 : (((3 : Fin 4) : ℕ) : ℤ) = 3 := rfl
  rw [h3]
  have e2 : E 4 (b * 2 ^ 2) = 1 := by
    rw [show b * 2 ^ 2 = ((4 : ℕ) : ℤ) * b by push_cast; ring, E_mul_self (by norm_num)]
  have e3 : E 4 (b * 3 ^ 2) = E 4 b := by
    rw [show b * 3 ^ 2 = b + ((4 : ℕ) : ℤ) * (2 * b) by push_cast; ring, E_period (by norm_num)]
  rw [e2, e3]; simp [E_zero]; ring

theorem E_eight_four_mul {b : ℤ} (hb : Odd b) : E 8 (4 * b) = -1 := by
  obtain ⟨t, rfl⟩ := hb
  rw [show 4 * (2 * t + 1) = 4 + ((8 : ℕ) : ℤ) * t by push_cast; ring, E_period (by norm_num)]
  unfold E
  rw [show 2 * (Real.pi : ℂ) * I * ((4 : ℤ) : ℂ) / ((8 : ℕ) : ℂ) = Real.pi * I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem gs_eight {b : ℤ} (hb : Odd b) : gs 8 b = 4 * E 8 b := by
  unfold gs
  rw [Fin.sum_univ_eight]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have h3 : (((3 : Fin 8) : ℕ) : ℤ) = 3 := rfl
  have h4 : (((4 : Fin 8) : ℕ) : ℤ) = 4 := rfl
  have h5 : (((5 : Fin 8) : ℕ) : ℤ) = 5 := rfl
  have h6 : (((6 : Fin 8) : ℕ) : ℤ) = 6 := rfl
  have h7 : (((7 : Fin 8) : ℕ) : ℤ) = 7 := rfl
  rw [h3, h4, h5, h6, h7]
  have p : ∀ (a k : ℤ), E 8 (a + ((8 : ℕ) : ℤ) * k) = E 8 a := fun a k => E_period (by norm_num) a k
  have e2 : E 8 (b * 2 ^ 2) = -1 := by rw [show b * 2 ^ 2 = 4 * b by ring, E_eight_four_mul hb]
  have e3 : E 8 (b * 3 ^ 2) = E 8 b := by
    rw [show b * 3 ^ 2 = b + ((8 : ℕ) : ℤ) * b by push_cast; ring, p]
  have e4' : E 8 (b * 4 ^ 2) = 1 := by
    rw [show b * 4 ^ 2 = 0 + ((8 : ℕ) : ℤ) * (2 * b) by push_cast; ring, p, E_zero]
  have e5 : E 8 (b * 5 ^ 2) = E 8 b := by
    rw [show b * 5 ^ 2 = b + ((8 : ℕ) : ℤ) * (3 * b) by push_cast; ring, p]
  have e6 : E 8 (b * 6 ^ 2) = -1 := by
    rw [show b * 6 ^ 2 = 4 * b + ((8 : ℕ) : ℤ) * (4 * b) by push_cast; ring, p, E_eight_four_mul hb]
  have e7 : E 8 (b * 7 ^ 2) = E 8 b := by
    rw [show b * 7 ^ 2 = b + ((8 : ℕ) : ℤ) * (6 * b) by push_cast; ring, p]
  rw [e2, e3, e4', e5, e6, e7]; simp [E_zero]; ring

theorem gs_pow_even (j : ℕ) {b : ℤ} (hb : Odd b) : gs (2 ^ (2 * j + 2)) b = 2 ^ j * gs 4 b := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2 * (j + 1) + 2 = (2 * j) + 4 by ring, gs_two_step _ hb, ih]; ring

theorem gs_pow_odd (j : ℕ) {b : ℤ} (hb : Odd b) : gs (2 ^ (2 * j + 3)) b = 2 ^ j * gs 8 b := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2 * (j + 1) + 3 = (2 * j + 1) + 4 by ring, gs_two_step _ hb,
      show 2 * j + 1 + 2 = 2 * j + 3 by ring, ih]; ring

/-- `(1 + i^b) e(1/8) = χ₈(b) e(b/8) (1 + i)` for odd `b`. -/
theorem one_add_E4 {b : ℤ} (hb : Odd b) :
    (1 + E 4 b) * E 8 1 = (ZMod.χ₈ b : ℂ) * E 8 b * (1 + E 4 1) := by
  set ζ := E 8 1 with hζ
  have hz : ∀ n : ℕ, E 8 n = ζ ^ n := fun n => by rw [hζ, E_pow, mul_one]
  have hz4 : ζ ^ 4 = -1 := by
    rw [← hz 4, show ((4 : ℕ) : ℤ) = 4 * 1 by norm_num, E_eight_four_mul odd_one]
  have h4 : ∀ t : ℤ, E 4 t = E 8 (2 * t) := fun t => by
    have := E_mul_left (r := 4) (s := 2) (by norm_num) t
    simpa using this.symm
  have hr8 : E 8 b = E 8 (b % 8) := E_congr (by norm_num) (Int.mod_modEq b 8).symm
  have hr4 : E 8 (2 * b) = E 8 (2 * (b % 8)) := E_congr (by norm_num) (by
    refine Int.modEq_iff_dvd.2 ⟨-(b / 8) * 2, ?_⟩
    have := Int.emod_add_mul_ediv b 8
    push_cast; linarith)
  have hl : ∀ n : ℕ, E 8 (n : ℤ) = ζ ^ n := hz
  rw [h4, h4, hr4, hr8, ZMod.χ₈_int_eq_if_mod_eight]
  have hodd : b % 2 = 1 := Int.odd_iff.1 hb
  have hr : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
  rw [if_neg (by omega)]
  have e1 : E 8 1 = ζ := rfl
  have e2 : E 8 (2 * 1) = ζ ^ 2 := hl 2
  rcases hr with h | h | h | h <;> rw [h, e2]
  · rw [if_pos (Or.inl rfl)]; simp only [Int.cast_one, e1]; ring
  · rw [if_neg (by omega), show E 8 (2 * 3) = ζ ^ 6 from hl 6, show E 8 3 = ζ ^ 3 from hl 3]
    push_cast
    linear_combination (ζ + ζ ^ 3) * hz4
  · rw [if_neg (by omega), show E 8 (2 * 5) = ζ ^ 10 from hl 10, show E 8 5 = ζ ^ 5 from hl 5]
    push_cast
    linear_combination (ζ + ζ ^ 7) * hz4
  · rw [if_pos (Or.inr rfl), show E 8 (2 * 7) = ζ ^ 14 from hl 14,
      show E 8 7 = ζ ^ 7 from hl 7]
    push_cast
    linear_combination (ζ ^ 11 - ζ ^ 7 - ζ ^ 5 + ζ) * hz4

/-- The reciprocity phase: `e(ℓn/8) = (−1)^{⌊n/2⌋⌊ℓ/2⌋} e((ℓ−1)/8) e(n/8)` for odd `ℓ, n`. -/
theorem E8_recip {ℓ n : ℕ} (hℓ : Odd ℓ) (hn : Odd n) :
    E 8 ((ℓ : ℤ) * n) = (((-1 : ℤ) ^ (n / 2 * (ℓ / 2)) : ℤ) : ℂ) * E 8 ((ℓ : ℤ) - 1) * E 8 n := by
  obtain ⟨u, rfl⟩ := hℓ
  obtain ⟨v, rfl⟩ := hn
  have hu : (2 * u + 1) / 2 = u := by omega
  have hv : (2 * v + 1) / 2 = v := by omega
  rw [hu, hv]
  have hm1 : ((-1 : ℤ) : ℂ) = E 8 4 := by
    rw [show (4 : ℤ) = 4 * 1 by norm_num, E_eight_four_mul odd_one]; simp
  push_cast
  rw [show ((-1 : ℂ)) = E 8 4 by rw [← hm1]; simp, E_pow, ← E_add, ← E_add]
  congr 1; push_cast; ring

/-! ### Assembly: the Gauss ratio law -/

/-- The two-adic identity: for `k = e + 2`, odd `ℓ, n`,
`g(2^k, ℓn) = (2/ℓ)^{e+1} (−1)^{⌊n/2⌋⌊ℓ/2⌋} e((ℓ−1)/8) g(2^k, n)`. -/
theorem gs_two_adic (e : ℕ) {ℓ n : ℕ} (hℓ : Odd ℓ) (hn : Odd n) :
    gs (2 ^ (e + 2)) ((ℓ : ℤ) * n) = ((jacobiSym 2 ℓ ^ (e + 1) : ℤ) : ℂ) *
      (((-1 : ℤ) ^ (n / 2 * (ℓ / 2)) : ℤ) : ℂ) * E 8 ((ℓ : ℤ) - 1) * gs (2 ^ (e + 2)) n := by
  have hℓn : Odd ((ℓ : ℤ) * n) := by
    rw [Int.odd_mul]; exact ⟨by exact_mod_cast hℓ.natCast, by exact_mod_cast hn.natCast⟩
  have hnZ : Odd (n : ℤ) := hn.natCast
  have hg : Int.gcd 2 ℓ = 1 := by
    rw [Int.gcd, Int.natAbs_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (fun h => (Nat.not_even_iff_odd.2 hℓ) (even_iff_two_dvd.2 h)))
  have hsq : (jacobiSym 2 ℓ) ^ 2 = 1 := jacobiSym.sq_one hg
  have hrec := E8_recip hℓ hn
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : e + 2 = 2 * j + 2 := by omega
    rw [hk, gs_pow_even j hℓn, gs_pow_even j hnZ, gs_four, gs_four]
    have hpow : (jacobiSym 2 ℓ) ^ (e + 1) = jacobiSym 2 ℓ := by
      rw [hj, show j + j + 1 = 2 * j + 1 by ring, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [hpow, jacobiSym.at_two hℓ]
    have h1 := one_add_E4 hℓn
    have h2 := one_add_E4 hnZ
    have hζ : E 8 1 ≠ 0 := Complex.exp_ne_zero _
    have hχ : (ZMod.χ₈ (((ℓ : ℤ) * n : ℤ) : ZMod 8) : ℂ) =
        (ZMod.χ₈ (ℓ : ZMod 8) : ℂ) * (ZMod.χ₈ ((n : ℤ) : ZMod 8) : ℂ) := by
      push_cast; rw [map_mul]; push_cast; ring
    apply mul_right_cancel₀ hζ
    rw [show (2 : ℂ) ^ j * (2 + 2 * E 4 ((ℓ : ℤ) * n)) * E 8 1 =
        2 ^ j * 2 * ((1 + E 4 ((ℓ : ℤ) * n)) * E 8 1) by ring, h1, hχ, hrec]
    rw [show ((ZMod.χ₈ (ℓ : ZMod 8) : ℤ) : ℂ) * (((-1 : ℤ) ^ (n / 2 * (ℓ / 2)) : ℤ) : ℂ) *
        E 8 ((ℓ : ℤ) - 1) * (2 ^ j * (2 + 2 * E 4 (n : ℤ))) * E 8 1 =
        ((ZMod.χ₈ (ℓ : ZMod 8) : ℤ) : ℂ) * (((-1 : ℤ) ^ (n / 2 * (ℓ / 2)) : ℤ) : ℂ) *
        E 8 ((ℓ : ℤ) - 1) * 2 ^ j * 2 * ((1 + E 4 (n : ℤ)) * E 8 1) by ring, h2]
    ring
  · have hk : e + 2 = 2 * j + 3 := by omega
    rw [hk, gs_pow_odd j hℓn, gs_pow_odd j hnZ, gs_eight hℓn, gs_eight hnZ, hrec]
    have hpow : (jacobiSym 2 ℓ) ^ (e + 1) = 1 := by
      rw [hj, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, hsq, one_pow]
    rw [hpow]; push_cast; ring

/-- **The Gauss ratio law** (proved). -/
theorem gaussRatioLaw : GaussRatioLaw := by
  intro N hN ℓ hℓ
  obtain ⟨e, n, hnodd, hNe⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hℓ2 : ¬ 2 ∣ ℓ := fun h => by
    have := Nat.dvd_gcd h (dvd_mul_right 2 N)
    rw [hℓ] at this; omega
  have hℓodd : Odd ℓ := Nat.odd_iff.2 (by omega)
  have hn0 : 0 < n := hnodd.pos
  have hcop : Nat.Coprime (2 ^ (e + 2)) n :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (fun h => (Nat.not_even_iff_odd.2 hnodd) (even_iff_two_dvd.2 h)))
  have h4N : 4 * N = 2 ^ (e + 2) * n := by rw [hNe]; ring
  have hℓn : Nat.Coprime ℓ n :=
    Nat.Coprime.coprime_dvd_right ⟨2 * 2 ^ e, by rw [hNe]; ring⟩ hℓ
  have hc1 : Nat.Coprime ((ℓ : ℤ) * ((2 ^ (e + 2) : ℕ) : ℤ)).natAbs n := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left hℓn hcop
  have hc2 : Nat.Coprime ((1 : ℤ) * ((2 ^ (e + 2) : ℕ) : ℤ)).natAbs n := by
    rw [one_mul, Int.natAbs_natCast]; exact hcop
  have hA : gs (4 * N) ℓ = gs (2 ^ (e + 2)) ((ℓ : ℤ) * n) *
      ((jacobiSym ℓ n * jacobiSym 2 n ^ (e + 2) : ℤ) : ℂ) * gs n 1 := by
    rw [h4N, gs_crt (by positivity) hn0 hcop, gs_jacobi n hnodd _ hc1, jacobiSym.mul_left]
    push_cast
    rw [jacobiSym.pow_left]; push_cast; ring
  have hB : gs (4 * N) 1 = gs (2 ^ (e + 2)) n * ((jacobiSym 2 n ^ (e + 2) : ℤ) : ℂ) * gs n 1 := by
    rw [h4N, gs_crt (by positivity) hn0 hcop]
    simp only [one_mul] at hc2 ⊢
    rw [gs_jacobi n hnodd _ hc2]
    push_cast
    rw [jacobiSym.pow_left]; push_cast; ring
  have hJ : jacobiSym (2 * (N : ℤ)) ℓ =
      jacobiSym 2 ℓ ^ (e + 1) * ((-1) ^ (n / 2 * (ℓ / 2)) * jacobiSym ℓ n) := by
    rw [show (2 * (N : ℤ)) = (2 : ℤ) ^ (e + 1) * (n : ℤ) by rw [hNe]; push_cast; ring,
      jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.quadratic_reciprocity hnodd hℓodd]
  have hT := gs_two_adic e hℓodd hnodd
  have hfinal : gs (4 * N) ℓ = (jacobiSym (2 * (N : ℤ)) ℓ : ℂ) *
      cexp (2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8) * gs (4 * N) 1 := by
    have hE : cexp (2 * Real.pi * I * ((ℓ : ℂ) - 1) / 8) = E 8 ((ℓ : ℤ) - 1) := by
      unfold E; push_cast; ring_nf
    rw [hA, hB, hT, hJ, hE]
    push_cast
    ring
  rw [gs_four_mul hN, gs_four_mul hN] at hfinal
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [hfinal]; ring

/-! ## Final form of the reduction -/

/-- **G4, final reduction**: the Weil Galois law follows from the kernel law alone. -/
theorem weilGaloisLaw_of_weilKernelLaw (hK : WeilKernelLaw) : WeilGaloisLaw :=
  weilGaloisLaw_of_kernel_gauss hK gaussRatioLaw

/-- Conversely, the kernel law is the `ℓ = 1`, `v = δ₀` case of the Weil Galois law; so the
residual `WeilKernelLaw` is *equivalent* to `WeilGaloisLaw`. -/
theorem weilKernelLaw_of_weilGaloisLaw (hW : WeilGaloisLaw) : WeilKernelLaw := by
  intro N M hN h4N h24 γ h00 h11 h01 h10 A hA
  set v : ℤ → ℂ := fun x => if ((2 * N : ℕ) : ℤ) ∣ x then 1 else 0 with hv
  have hper : ∀ x, v (x + 2 * N) = v x := by
    intro x; simp only [hv]
    have : ((2 * N : ℕ) : ℤ) ∣ x + 2 * N ↔ ((2 * N : ℕ) : ℤ) ∣ x :=
      dvd_add_left ⟨1, by push_cast; ring⟩
    rw [if_congr this rfl rfl]
  have hev : ∀ x, v (-x) = v x := by intro x; simp only [hv, dvd_neg]
  have h := hW N M hN h4N h24 1 (Nat.coprime_one_left M) 1 (by simp)
    γ (by simpa using h00) h11 h01 h10 A hA v hper hev (fz hN)
  rw [Finset.sum_eq_single (fz hN)] at h
  · simpa [hv, fz, jacobiSym.one_right] using h
  · intro j _ hj
    rw [hv]; simp only
    rw [if_neg, mul_zero]
    intro hd
    apply hj
    have idx0 : weilIdx hN 0 = fz hN := ((eq_weilIdx_iff hN (fz hN) 0).2 (by simp [fz])).symm
    exact ((eq_weilIdx_iff hN j 0).2 ((Int.modEq_zero_iff_dvd).2 hd)).trans idx0
  · simp

theorem weilGaloisLaw_iff_weilKernelLaw : WeilGaloisLaw ↔ WeilKernelLaw :=
  ⟨weilKernelLaw_of_weilGaloisLaw, weilGaloisLaw_of_weilKernelLaw⟩

/-- The theta Galois law (GR Prop. 3.8) from the kernel law. -/
theorem thetaGaloisLaw_of_weilKernelLaw (hK : WeilKernelLaw) : ThetaGaloisLaw :=
  thetaGaloisLaw_of_weilGaloisLaw (weilGaloisLaw_of_weilKernelLaw hK)

end WeilGalois

end VOA.Classification.COne
