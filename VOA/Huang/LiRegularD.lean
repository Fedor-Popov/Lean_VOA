import VOA.Huang.LiRegularBase
import Mathlib.Algebra.Polynomial.HasseDeriv

/-! # The space `D_{P(z)}` of `P(z)`-linear functionals and the regularized action `Y^R`

Li, *Regular representations of vertex operator algebras I* (math/9908108), §3.  Fix an
opposite mode system `Bs` on `M` and `z ≠ 0`.  A functional `α ∈ M*` is **`P(z)`-linear**
(`InD`) if for every state `a` there are `k, N` with

  `Res_x x^p (x − z)^k q(x) Y*(a,x) α = 0`   for all `p ≥ N` and polynomials `q`

(`Wit a α k N`): the matrix coefficients of `Y*(a,x)α` are expansions at `∞` of rational
functions with poles at `0` and `z` of uniformly bounded order (Li, Lemma 3.4 (d)).

The **regularized action** `Y^R(a,x)α` is the expansion of the same rational function at
`x = 0`.  We define its modes with Laurent-polynomial test functions only:
`yR a n α = Y*(a, xⁿ χ) α`, where `χ = B (x − z)^k` comes from a Bézout identity
`A x^L + B (x − z)^k = 1` with `L ≥ N − n`.  The value does not depend on any of the
choices (`yR_eq`).  Proved here:

* `wit_min` — witnesses are closed under `(min, min)` (Bézout);
* `yR_eq` — independence of the choices;
* `yR_trunc` — lower truncation of `Y^R` (Li, Lemma 3.8);
* `yRres_eq_ys` — `Y^R = Y*` on test functions divisible by `(x − z)^k` (Li, Lemma 3.9);
* `inD_ys`, `wit_ys_uniform` — `D` is stable under `Y*` with a *uniform* pole bound at `z`
  (Li, Proposition 3.6);
* `inD_yR` — `Y^R` preserves `D` (Li, Proposition 3.12);
* linearity of `Y^R` in the state and in the functional, packaged as `yRL a n : D →ₗ D`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators Polynomial

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ## Polynomial preliminaries -/

/-- The linear polynomial `x − z`. -/
noncomputable abbrev lz (z : ℂ) : ℂ[X] := Polynomial.X - Polynomial.C z

theorem isCoprime_X_pow_lz_pow {z : ℂ} (hz : z ≠ 0) (d e : ℕ) :
    IsCoprime ((Polynomial.X : ℂ[X]) ^ d) (lz z ^ e) := by
  have h : IsCoprime (Polynomial.X - Polynomial.C (0 : ℂ)) (lz z) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by simpa using hz)
  rw [map_zero, sub_zero] at h
  exact h.pow

/-- Bézout for `x^d` and `(x − z)^e`. -/
theorem bezout {z : ℂ} (hz : z ≠ 0) (d e : ℕ) :
    ∃ A B : ℂ[X], A * Polynomial.X ^ d + B * lz z ^ e = 1 := by
  obtain ⟨A, B, h⟩ := isCoprime_X_pow_lz_pow hz d e
  exact ⟨A, B, h⟩

theorem toLaurent_X_pow' (n : ℕ) : Polynomial.toLaurent ((Polynomial.X : ℂ[X]) ^ n) = T n :=
  Polynomial.toLaurent_X_pow n

/-- `T (N + d) = T N * toLaurent (X^d)` for `d : ℕ`. -/
theorem T_add_nat (N : ℤ) (d : ℕ) :
    (T (N + d) : ℂ[T;T⁻¹]) = T N * Polynomial.toLaurent ((Polynomial.X : ℂ[X]) ^ d) := by
  rw [toLaurent_X_pow', T_add]

/-- Every Laurent polynomial is `T e * toLaurent p`. -/
theorem exists_T_mul_toLaurent (φ : ℂ[T;T⁻¹]) : ∃ (e : ℤ) (p : ℂ[X]),
    φ = T e * Polynomial.toLaurent p := by
  obtain ⟨n, f', h⟩ := exists_T_pow φ
  refine ⟨-(n : ℤ), f', ?_⟩
  rw [h, mul_comm, mul_assoc, ← T_add]
  simp

/-- The divided derivative of a polynomial is its Hasse derivative. -/
theorem dd_toLaurent (i : ℕ) (p : ℂ[X]) :
    dd i (Polynomial.toLaurent p) = Polynomial.toLaurent (Polynomial.hasseDeriv i p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | monomial n c =>
    rw [Polynomial.hasseDeriv_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, Polynomial.toLaurent_C, toLaurent_X_pow']
    rw [dd_CT]
    rcases le_or_gt i n with hin | hin
    · rw [cbz_natCast_eq_choose hin, show ((n : ℤ) - (i : ℤ)) = ((n - i : ℕ) : ℤ) by omega]
      congr 1
      rw [mul_comm, map_mul, map_natCast]
    · rw [cbz_lt (p := (n : ℤ)) (c := (i : ℤ)) (by positivity) (by omega),
        Nat.choose_eq_zero_of_lt hin]
      simp

/-- `(x − z)^K ∣ Q ⟹ (x − z)^{K−t} ∣ Q⁽ᵗ⁾` for the Hasse derivative. -/
theorem lz_pow_dvd_hasseDeriv {z : ℂ} {K : ℕ} {Q : ℂ[X]} (h : lz z ^ K ∣ Q) (t : ℕ) :
    lz z ^ (K - t) ∣ Polynomial.hasseDeriv t Q := by
  have h1 := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd t h
  rw [← Polynomial.factorial_smul_hasseDeriv] at h1
  have hf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  obtain ⟨c, hc⟩ := h1
  refine ⟨Polynomial.C ((t.factorial : ℂ)⁻¹) * c, ?_⟩
  have e : Polynomial.hasseDeriv t Q
      = Polynomial.C ((t.factorial : ℂ)⁻¹) * ((t.factorial • Polynomial.hasseDeriv t) Q) := by
    rw [LinearMap.smul_apply, nsmul_eq_mul, ← mul_assoc, ← Polynomial.C_eq_natCast,
      ← Polynomial.C_mul, inv_mul_cancel₀ hf, map_one, one_mul]
  rw [e, hc]; ring

/-- **Divided derivatives of ideal elements.** For `i ≤ K`,
`∂⁽ⁱ⁾(T^N (x − z)^K q) = T^{N−i} (x − z)^{K−i} q'`. -/
theorem dd_ideal {z : ℂ} (i : ℕ) (N : ℤ) (K : ℕ) (q : ℂ[X]) (hi : i ≤ K) :
    ∃ q' : ℂ[X], dd i (T N * Polynomial.toLaurent (lz z ^ K * q))
      = T (N - i) * Polynomial.toLaurent (lz z ^ (K - i) * q') := by
  rw [dd_mul]
  have hterm : ∀ s ∈ Finset.range (i + 1), ∃ r : ℂ[X],
      dd s (T N) * dd ((i : ℤ) - s) (Polynomial.toLaurent (lz z ^ K * q))
        = T (N - i) * Polynomial.toLaurent (lz z ^ (K - i) * r) := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hsi : s ≤ i := by omega
    rw [show (i : ℤ) - (s : ℤ) = ((i - s : ℕ) : ℤ) by omega, dd_toLaurent, dd_T]
    obtain ⟨c, hc⟩ := lz_pow_dvd_hasseDeriv (z := z) (K := K) (Q := lz z ^ K * q)
      (dvd_mul_right _ _) (i - s)
    refine ⟨Polynomial.C (cbz N s) * Polynomial.X ^ (i - s) * lz z ^ s * c, ?_⟩
    rw [hc, show K - (i - s) = (K - i) + s by omega, pow_add]
    have e1 : (T (N - s) : ℂ[T;T⁻¹]) = T (N - i) * T ((i - s : ℕ) : ℤ) := by
      rw [← T_add]; congr 1; push_cast [Nat.cast_sub hsi]; ring
    rw [e1]
    simp only [map_mul, Polynomial.toLaurent_C, toLaurent_X_pow']
    ring
  choose r hr using hterm
  refine ⟨∑ s ∈ (Finset.range (i + 1)).attach, r s.1 s.2, ?_⟩
  rw [← Finset.sum_attach]
  simp only [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => hr s.1 s.2

namespace OppBase

variable {W : VertexOperatorAlgebra V} {M : Type v} [AddCommGroup M] [Module ℂ M]
variable (Bs : OppBase W M) (z : ℂ)

/-! ## Witnesses and the space `D_{P(z)}` -/

/-- `(k, N)` bounds the poles of `Y*(a,x)α` at `z` and at `0`. -/
def Wit (a : V) (α : Module.Dual ℂ M) (k : ℕ) (N : ℤ) : Prop :=
  ∀ q : ℂ[X], Bs.ys a (T N * Polynomial.toLaurent (lz z ^ k * q)) α = 0

/-- `α` is a `P(z)`-linear functional. -/
def InD (α : Module.Dual ℂ M) : Prop := ∀ a : V, ∃ (k : ℕ) (N : ℤ), Bs.Wit z a α k N

variable {Bs z}

theorem Wit.mono {a : V} {α : Module.Dual ℂ M} {k k' : ℕ} {N N' : ℤ} (h : Bs.Wit z a α k N)
    (hk : k ≤ k') (hN : N ≤ N') : Bs.Wit z a α k' N' := by
  intro q
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, N' = N + d := ⟨(N' - N).toNat, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, k' = k + e := ⟨k' - k, by omega⟩
  have hq : T (N + d) * Polynomial.toLaurent (lz z ^ (k + e) * q)
      = T N * Polynomial.toLaurent (lz z ^ k * (Polynomial.X ^ d * lz z ^ e * q)) := by
    rw [T_add_nat, mul_assoc, ← map_mul, pow_add]
    congr 2
    ring
  rw [hq]
  exact h _

theorem Wit.add_a {a b : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ} (ha : Bs.Wit z a α k N)
    (hb : Bs.Wit z b α k N) : Bs.Wit z (a + b) α k N := fun q => by
  rw [Bs.ys_add_a, ha q, hb q, add_zero]

theorem Wit.smul_a {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ} (c : ℂ)
    (ha : Bs.Wit z a α k N) : Bs.Wit z (c • a) α k N := fun q => by
  rw [Bs.ys_smul_a, ha q, smul_zero]

theorem Wit.add {a : V} {α β : Module.Dual ℂ M} {k : ℕ} {N : ℤ} (hα : Bs.Wit z a α k N)
    (hβ : Bs.Wit z a β k N) : Bs.Wit z a (α + β) k N := fun q => by
  rw [map_add, hα q, hβ q, add_zero]

theorem Wit.smul {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ} (c : ℂ)
    (hα : Bs.Wit z a α k N) : Bs.Wit z a (c • α) k N := fun q => by
  rw [map_smul, hα q, smul_zero]

theorem wit_zero (a : V) (k : ℕ) (N : ℤ) : Bs.Wit z a 0 k N := fun _ => map_zero _

theorem Wit.min_aux (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k₀ k₁ : ℕ} {N₀ N₁ : ℤ}
    (h₀ : Bs.Wit z a α k₀ N₀) (h₁ : Bs.Wit z a α k₁ N₁) (hk : k₀ ≤ k₁) (hN : N₁ ≤ N₀) :
    Bs.Wit z a α k₀ N₁ := by
  intro q
  obtain ⟨d, hd⟩ : ∃ d : ℕ, N₀ = N₁ + d := ⟨(N₀ - N₁).toNat, by omega⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, k₁ = k₀ + e := ⟨k₁ - k₀, by omega⟩
  obtain ⟨A, B, hAB⟩ := bezout hz d e
  have key : lz z ^ k₀ * q
      = Polynomial.X ^ d * (lz z ^ k₀ * (A * q)) + lz z ^ k₁ * (B * q) := by
    rw [he, pow_add]
    linear_combination (-(lz z ^ k₀ * q)) * hAB
  rw [key, map_add, mul_add, Bs.ys_add, map_mul, ← mul_assoc, ← T_add_nat, ← hd, h₀, h₁,
    add_zero]

/-- **Witnesses combine to the componentwise minimum** (Bézout). -/
theorem Wit.min (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k₀ k₁ : ℕ} {N₀ N₁ : ℤ}
    (h₀ : Bs.Wit z a α k₀ N₀) (h₁ : Bs.Wit z a α k₁ N₁) :
    Bs.Wit z a α (min k₀ k₁) (min N₀ N₁) := by
  rcases le_total k₀ k₁ with hk | hk <;> rcases le_total N₀ N₁ with hN | hN
  · rw [min_eq_left hk, min_eq_left hN]; exact h₀
  · rw [min_eq_left hk, min_eq_right hN]; exact Wit.min_aux hz h₀ h₁ hk hN
  · rw [min_eq_right hk, min_eq_left hN]; exact Wit.min_aux hz h₁ h₀ hk hN
  · rw [min_eq_right hk, min_eq_right hN]; exact h₁

/-! ## The regularized modes `Y^R` -/

/-- Bézout coefficients `A, B` with `A x^L + B (x − z)^k = 1`. -/
noncomputable def bzA {z : ℂ} (hz : z ≠ 0) (L k : ℕ) : ℂ[X] := (bezout hz L k).choose

noncomputable def bzB {z : ℂ} (hz : z ≠ 0) (L k : ℕ) : ℂ[X] := (bezout hz L k).choose_spec.choose

theorem bz_spec {z : ℂ} (hz : z ≠ 0) (L k : ℕ) :
    bzA hz L k * Polynomial.X ^ L + bzB hz L k * lz z ^ k = 1 :=
  (bezout hz L k).choose_spec.choose_spec

open Classical in
variable (Bs z) in
/-- **The regularized mode** `a^R_n α` (Li, Definition 3.7): the residue of
`xⁿ B (x − z)^k Y*(a,x)α`, with Bézout data for `(N − n, k)`. -/
noncomputable def yR (hz : z ≠ 0) (a : V) (n : ℤ) (α : Module.Dual ℂ M) : Module.Dual ℂ M :=
  if h : ∃ (k : ℕ) (N : ℤ), Bs.Wit z a α k N then
    Bs.ys a (T n * Polynomial.toLaurent
      (bzB hz (h.choose_spec.choose - n).toNat h.choose * lz z ^ h.choose)) α
  else 0

/-- **Independence of the choices.** Any witness and any Bézout data with `L ≥ N − n`
compute the regularized mode. -/
theorem yR_eq (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) (n : ℤ) (L : ℕ) (hL : N ≤ n + L) (A B : ℂ[X])
    (hAB : A * Polynomial.X ^ L + B * lz z ^ k = 1) :
    Bs.yR z hz a n α = Bs.ys a (T n * Polynomial.toLaurent (B * lz z ^ k)) α := by
  have h : ∃ (k : ℕ) (N : ℤ), Bs.Wit z a α k N := ⟨k, N, hW⟩
  rw [yR, dif_pos h]
  set k₀ := h.choose with hk₀
  set N₀ := h.choose_spec.choose with hN₀
  have hW₀ : Bs.Wit z a α k₀ N₀ := h.choose_spec.choose_spec
  set L₀ := (N₀ - n).toNat with hL₀
  have hAB₀ := bz_spec hz L₀ k₀
  set A₀ := bzA hz L₀ k₀
  set B₀ := bzB hz L₀ k₀
  rw [← sub_eq_zero, ← Bs.ys_sub, ← mul_sub, ← map_sub]
  set P := B₀ * lz z ^ k₀ - B * lz z ^ k with hP
  have hP' : P = A * Polynomial.X ^ L - A₀ * Polynomial.X ^ L₀ := by
    rw [hP]; linear_combination hAB₀ - hAB
  set k' := min k₀ k
  set m := min L₀ L
  have hlz : lz z ^ k' ∣ P := by
    rw [hP]
    exact dvd_sub ((pow_dvd_pow _ (min_le_left _ _)).mul_left _)
      ((pow_dvd_pow _ (min_le_right _ _)).mul_left _)
  have hX : (Polynomial.X : ℂ[X]) ^ m ∣ P := by
    rw [hP']
    exact dvd_sub ((pow_dvd_pow _ (min_le_right _ _)).mul_left _)
      ((pow_dvd_pow _ (min_le_left _ _)).mul_left _)
  obtain ⟨Q, hQ⟩ := (isCoprime_X_pow_lz_pow hz m k').mul_dvd hX hlz
  have hWm := Wit.min hz hW₀ hW
  have hm : min N₀ N ≤ n + m := by
    simp only [m, hL₀]
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n + m = min N₀ N + d := ⟨(n + m - min N₀ N).toNat, by omega⟩
  have e : T n * Polynomial.toLaurent P
      = T (min N₀ N) * Polynomial.toLaurent (lz z ^ k' * (Polynomial.X ^ d * Q)) := by
    have hT : (T n : ℂ[T;T⁻¹]) * T (m : ℤ) = T (min N₀ N) * T (d : ℤ) := by
      rw [← T_add, ← T_add, hd]
    rw [hQ]
    simp only [map_mul, toLaurent_X_pow']
    linear_combination (Polynomial.toLaurent (lz z ^ k') * Polynomial.toLaurent Q) * hT
  rw [e]
  exact hWm _

/-- Lower truncation of `Y^R` (Li, Lemma 3.8). -/
theorem yR_trunc (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) {n : ℤ} (hn : N ≤ n) : Bs.yR z hz a n α = 0 := by
  rw [yR_eq hz hW n 0 (by simpa using hn) 1 0 (by simp), zero_mul, map_zero, mul_zero,
    Bs.ys_zero]

variable (Bs z) in
/-- `Y^R` with a Laurent-polynomial test function. -/
noncomputable def yRres (hz : z ≠ 0) (a : V) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Module.Dual ℂ M :=
  Finsupp.linearCombination ℂ (fun n => Bs.yR z hz a n α) φ

theorem yRres_CT (hz : z ≠ 0) (a : V) (c : ℂ) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.yRres z hz a (LC c * T n) α = c • Bs.yR z hz a n α := by
  rw [yRres, ← single_eq_C_mul_T, Finsupp.linearCombination_single]

theorem yRres_T (hz : z ≠ 0) (a : V) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.yRres z hz a (T n) α = Bs.yR z hz a n α := by
  simpa using Bs.yRres_CT hz a 1 n α

theorem yRres_add (hz : z ≠ 0) (a : V) (φ ψ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.yRres z hz a (φ + ψ) α = Bs.yRres z hz a φ α + Bs.yRres z hz a ψ α := map_add _ _ _

theorem yRres_smul (hz : z ≠ 0) (a : V) (c : ℂ) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.yRres z hz a (c • φ) α = c • Bs.yRres z hz a φ α := map_smul _ _ _

theorem yRres_zero (hz : z ≠ 0) (a : V) (α : Module.Dual ℂ M) :
    Bs.yRres z hz a 0 α = 0 := map_zero _

/-- With one Bézout datum valid for every exponent of the test function. -/
theorem yRres_eq_chi (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) (e : ℤ) (p : ℂ[X]) (L : ℕ) (hL : N ≤ e + L) (A B : ℂ[X])
    (hAB : A * Polynomial.X ^ L + B * lz z ^ k = 1) :
    Bs.yRres z hz a (T e * Polynomial.toLaurent p) α
      = Bs.ys a (T e * Polynomial.toLaurent p * Polynomial.toLaurent (B * lz z ^ k)) α := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, Bs.yRres_add, hp, hq, add_mul, Bs.ys_add]
  | monomial j c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      show T e * (LC c * T (j : ℤ)) = LC c * T (e + j) by rw [T_add]; ring, yRres_CT,
      yR_eq hz hW (e + j) L (by omega) A B hAB, mul_assoc, ← smul_eq_C_mul, Bs.ys_smul]

/-- **`Y^R = Y*` on test functions divisible by `(x − z)^k`** (Li, Lemma 3.9). -/
theorem yRres_eq_ys (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) (ψ : ℂ[T;T⁻¹]) :
    Bs.yRres z hz a (Polynomial.toLaurent (lz z ^ k) * ψ) α
      = Bs.ys a (Polynomial.toLaurent (lz z ^ k) * ψ) α := by
  obtain ⟨e, p, rfl⟩ := exists_T_mul_toLaurent ψ
  have h1 : Polynomial.toLaurent (lz z ^ k) * (T e * Polynomial.toLaurent p)
      = T e * Polynomial.toLaurent (lz z ^ k * p) := by rw [map_mul]; ring
  rw [h1]
  set L := (N - e).toNat
  obtain ⟨A, B, hAB⟩ := bezout hz L k
  rw [yRres_eq_chi hz hW e (lz z ^ k * p) L (by omega) A B hAB]
  have h2 : T e * Polynomial.toLaurent (lz z ^ k * p) * Polynomial.toLaurent (B * lz z ^ k)
      = T e * Polynomial.toLaurent (lz z ^ k * p)
        - T (e + L) * Polynomial.toLaurent (lz z ^ k * (p * A)) := by
    rw [T_add_nat, show B * lz z ^ k = 1 - A * Polynomial.X ^ L by linear_combination hAB]
    simp only [map_mul, map_sub, map_one]
    ring
  rw [h2, Bs.ys_sub, Wit.mono hW le_rfl (by omega) (p * A), sub_zero]

/-! ## Stability of `D` -/

/-- A finite family of integers is bounded above. -/
theorem exists_bound_range (R : ℕ) (f : ℕ → ℤ) : ∃ B : ℤ, ∀ i < R, f i ≤ B := by
  obtain ⟨B, hB⟩ := ((Finset.range R).image f).exists_le
  exact ⟨B, fun i hi => hB _ (Finset.mem_image_of_mem f (Finset.mem_range.2 hi))⟩

theorem exists_bound_range_nat (R : ℕ) (f : ℕ → ℕ) : ∃ B : ℕ, ∀ i < R, f i ≤ B := by
  obtain ⟨B, hB⟩ := ((Finset.range R).image f).exists_le
  exact ⟨B, fun i hi => hB _ (Finset.mem_image_of_mem f (Finset.mem_range.2 hi))⟩

/-- **`D` is stable under `Y*`, with a pole bound at `z` independent of the test
function** (Li, Proposition 3.6). -/
theorem wit_ys {α : Module.Dual ℂ M} (hD : Bs.InD z α) (a b : V) :
    ∃ K : ℕ, ∀ ψ : ℂ[T;T⁻¹], ∃ N : ℤ, Bs.Wit z b (Bs.ys a ψ α) K N := by
  obtain ⟨R₀, hR₀⟩ := W.regularity b a
  set R : ℕ := R₀.toNat
  have hR : ∀ i : ℤ, (R : ℤ) ≤ i → W.smul b i a = 0 := fun i hi => hR₀ i (by omega)
  choose kf Nf hf using hD
  obtain ⟨K₁, hK₁⟩ := exists_bound_range_nat R (fun i => kf (W.smul b i a) + i)
  refine ⟨max (kf b) K₁, fun ψ => ?_⟩
  obtain ⟨e, p, rfl⟩ := exists_T_mul_toLaurent ψ
  obtain ⟨N₁, hN₁⟩ := exists_bound_range R (fun i => Nf (W.smul b i a) + i - e)
  refine ⟨max (Nf b) N₁, fun q => ?_⟩
  set K := max (kf b) K₁
  set N := max (Nf b) N₁
  set φ := T N * Polynomial.toLaurent (lz z ^ K * q)
  have hcomm := Bs.ys_commutator b a α φ (T e * Polynomial.toLaurent p)
  have h0 : Bs.ys b φ α = 0 :=
    Wit.mono (hf b) (le_max_left _ _) (le_max_left _ _) q
  have hterm : ∀ i : ℤ,
      Bs.ys (W.smul b i a) (dd i φ * (T e * Polynomial.toLaurent p)) α = 0 := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [dd_neg hi, zero_mul, Bs.ys_zero]
    rcases le_or_gt (R : ℤ) i with hiR | hiR
    · rw [hR i hiR, Bs.ys_zero_a]
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j := ⟨i.toNat, by omega⟩
    have hjR : j < R := by omega
    have hjK : kf (W.smul b j a) + j ≤ K := le_trans (hK₁ j hjR) (le_max_right _ _)
    obtain ⟨q', hq'⟩ := dd_ideal (z := z) j N K q (by omega)
    rw [hq']
    have e2 : T (N - j) * Polynomial.toLaurent (lz z ^ (K - j) * q')
          * (T e * Polynomial.toLaurent p)
        = T (N - j + e) * Polynomial.toLaurent (lz z ^ (K - j) * (q' * p)) := by
      rw [T_add, map_mul, map_mul, map_mul]; ring
    rw [e2]
    exact Wit.mono (hf _) (by omega) (by have := hN₁ j hjR; have := le_max_right (Nf b) N₁; omega) _
  rw [h0, map_zero, sub_zero] at hcomm
  rw [hcomm, finsum_congr hterm, finsum_zero]

theorem inD_ys {α : Module.Dual ℂ M} (hD : Bs.InD z α) (a : V) (ψ : ℂ[T;T⁻¹]) :
    Bs.InD z (Bs.ys a ψ α) := fun b => by
  obtain ⟨K, hK⟩ := wit_ys hD a b
  obtain ⟨N, hN⟩ := hK ψ
  exact ⟨K, N, hN⟩

theorem yR_eq_ys_exists (hz : z ≠ 0) (a : V) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.yR z hz a n α = 0 ∨ ∃ ψ : ℂ[T;T⁻¹], Bs.yR z hz a n α = Bs.ys a ψ α := by
  unfold yR
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem inD_zero : Bs.InD z (0 : Module.Dual ℂ M) := fun a => ⟨0, 0, wit_zero a 0 0⟩

/-- `Y^R` preserves `D` (Li, Proposition 3.12). -/
theorem inD_yR (hz : z ≠ 0) {α : Module.Dual ℂ M} (hD : Bs.InD z α) (a : V) (n : ℤ) :
    Bs.InD z (Bs.yR z hz a n α) := by
  rcases yR_eq_ys_exists hz a n α with h | ⟨ψ, h⟩
  · rw [h]; exact inD_zero
  · rw [h]; exact inD_ys hD a ψ

theorem inD_add {α β : Module.Dual ℂ M} (hα : Bs.InD z α) (hβ : Bs.InD z β) :
    Bs.InD z (α + β) := fun a => by
  obtain ⟨k₁, N₁, h₁⟩ := hα a
  obtain ⟨k₂, N₂, h₂⟩ := hβ a
  exact ⟨max k₁ k₂, max N₁ N₂, Wit.add (h₁.mono (le_max_left _ _) (le_max_left _ _))
    (h₂.mono (le_max_right _ _) (le_max_right _ _))⟩

theorem inD_smul (c : ℂ) {α : Module.Dual ℂ M} (hα : Bs.InD z α) : Bs.InD z (c • α) :=
  fun a => by
    obtain ⟨k, N, h⟩ := hα a
    exact ⟨k, N, Wit.smul c h⟩

/-! ## Linearity of `Y^R` -/

/-- Common Bézout data for a witness: the regularized mode is a single `Y*` residue. -/
theorem yR_eq_common (hz : z ≠ 0) {a : V} {α : Module.Dual ℂ M} {k : ℕ} {N : ℤ}
    (hW : Bs.Wit z a α k N) (n : ℤ) :
    Bs.yR z hz a n α = Bs.ys a (T n * Polynomial.toLaurent
      (bzB hz (N - n).toNat k * lz z ^ k)) α :=
  yR_eq hz hW n _ (by omega) _ _ (bz_spec hz _ k)

theorem yR_add (hz : z ≠ 0) {α β : Module.Dual ℂ M} (hα : Bs.InD z α) (hβ : Bs.InD z β)
    (a : V) (n : ℤ) : Bs.yR z hz a n (α + β) = Bs.yR z hz a n α + Bs.yR z hz a n β := by
  obtain ⟨k₁, N₁, h₁⟩ := hα a
  obtain ⟨k₂, N₂, h₂⟩ := hβ a
  have W₁ := h₁.mono (le_max_left k₁ k₂) (le_max_left N₁ N₂)
  have W₂ := h₂.mono (le_max_right k₁ k₂) (le_max_right N₁ N₂)
  rw [yR_eq_common hz (Wit.add W₁ W₂), yR_eq_common hz W₁, yR_eq_common hz W₂, map_add]

theorem yR_smul (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (c : ℂ) (a : V)
    (n : ℤ) : Bs.yR z hz a n (c • α) = c • Bs.yR z hz a n α := by
  obtain ⟨k, N, h⟩ := hα a
  rw [yR_eq_common hz (Wit.smul c h), yR_eq_common hz h, map_smul]

theorem yR_add_a (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (a b : V) (n : ℤ) :
    Bs.yR z hz (a + b) n α = Bs.yR z hz a n α + Bs.yR z hz b n α := by
  obtain ⟨k₁, N₁, h₁⟩ := hα a
  obtain ⟨k₂, N₂, h₂⟩ := hα b
  have W₁ := h₁.mono (le_max_left k₁ k₂) (le_max_left N₁ N₂)
  have W₂ := h₂.mono (le_max_right k₁ k₂) (le_max_right N₁ N₂)
  rw [yR_eq_common hz (Wit.add_a W₁ W₂), yR_eq_common hz W₁, yR_eq_common hz W₂, Bs.ys_add_a]

theorem yR_smul_a (hz : z ≠ 0) {α : Module.Dual ℂ M} (hα : Bs.InD z α) (c : ℂ) (a : V)
    (n : ℤ) : Bs.yR z hz (c • a) n α = c • Bs.yR z hz a n α := by
  obtain ⟨k, N, h⟩ := hα a
  rw [yR_eq_common hz (Wit.smul_a c h), yR_eq_common hz h, Bs.ys_smul_a]

/-! ## The subspace `D` and the linear modes -/

variable (Bs z) in
/-- **`D_{P(z)}(M)`**, the space of `P(z)`-linear functionals (Li, Definition 3.1). -/
def Dsub : Submodule ℂ (Module.Dual ℂ M) where
  carrier := {α | Bs.InD z α}
  zero_mem' := inD_zero
  add_mem' := inD_add
  smul_mem' c _ h := inD_smul c h

variable (Bs z) in
/-- The regularized mode `a^R_n` as a linear endomorphism of `D`. -/
noncomputable def yRL (hz : z ≠ 0) (a : V) (n : ℤ) : Module.End ℂ (Bs.Dsub z) where
  toFun α := ⟨Bs.yR z hz a n α, inD_yR hz α.2 a n⟩
  map_add' α β := Subtype.ext (yR_add hz α.2 β.2 a n)
  map_smul' c α := Subtype.ext (yR_smul hz α.2 c a n)

@[simp] theorem yRL_coe (hz : z ≠ 0) (a : V) (n : ℤ) (α : Bs.Dsub z) :
    ((Bs.yRL z hz a n α : Bs.Dsub z) : Module.Dual ℂ M) = Bs.yR z hz a n α := rfl

end OppBase

end VOA.Huang.LiRegular
