/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkChar
import VOA.Classification.COne.SerreStarkEasy

/-!
# Serre–Stark S3-1a: the coset matrices of Shimura's `T(p²)`

For a prime `p`, the right cosets of `Γ₀(N)` in `Γ₀(N) diag(1, p²) Γ₀(N)` (`p ∤ N`) are
represented by the upper-triangular matrices

* `(1 b; 0 p²)`, `b mod p²`;  `(p h; 0 p)`, `h mod p` (`h = 0` is the scalar `pI`, which carries
  weight `0` in `T(p²)` and is kept only to make the index set uniform);  `(p² 0; 0 1)`.

This file is pure integer-matrix algebra:

* `cosetMat`, `mobZ` (the Möbius action of an integer matrix) and the explicit action;
* `cosetMat_unique`: the representatives are pairwise `SL₂(ℤ)`-inequivalent;
* the generic consequences of a factorisation `A_i γ = δ A_j` (`det δ = 1`, `δ ∈ Γ₀(N)`, the
  lower-right entry of `δ` modulo `N`);
* explicit factorisations for the three generators used later: `T`, `L^N = (1 0; N 1)` and the
  elements `γ ≡ diag(ℓ, ℓ') (mod N p²)`, with the induced permutations of the index set.
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## The index set and the coset matrices -/

/-- Index set: `b mod p²`, `h mod p`, `∞`. -/
abbrev HIdx (p : ℕ) := Fin (p ^ 2) ⊕ Fin p ⊕ Unit

/-- The coset representatives. -/
def cosetMat (p : ℕ) : HIdx p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl b => !![1, ((b : ℕ) : ℤ); 0, (p : ℤ) ^ 2]
  | .inr (.inl h) => !![(p : ℤ), ((h : ℕ) : ℤ); 0, (p : ℤ)]
  | .inr (.inr _) => !![(p : ℤ) ^ 2, 0; 0, 1]

/-- Upper-left entry `a_i ∈ {1, p, p²}`. -/
def aCo (p : ℕ) : HIdx p → ℤ
  | .inl _ => 1
  | .inr (.inl _) => p
  | .inr (.inr _) => (p : ℤ) ^ 2

/-- Lower-right entry `d_i ∈ {p², p, 1}`. -/
def dCo (p : ℕ) : HIdx p → ℤ
  | .inl _ => (p : ℤ) ^ 2
  | .inr (.inl _) => p
  | .inr (.inr _) => 1

theorem cosetMat_00 (p : ℕ) (i : HIdx p) : cosetMat p i 0 0 = aCo p i := by
  rcases i with b | h | _ <;> simp [cosetMat, aCo]

theorem cosetMat_10 (p : ℕ) (i : HIdx p) : cosetMat p i 1 0 = 0 := by
  rcases i with b | h | _ <;> simp [cosetMat]

theorem cosetMat_11 (p : ℕ) (i : HIdx p) : cosetMat p i 1 1 = dCo p i := by
  rcases i with b | h | _ <;> simp [cosetMat, dCo]

theorem aCo_mul_dCo (p : ℕ) (i : HIdx p) : aCo p i * dCo p i = (p : ℤ) ^ 2 := by
  rcases i with b | h | _ <;> simp [aCo, dCo] <;> ring

theorem det_cosetMat (p : ℕ) (i : HIdx p) : (cosetMat p i).det = (p : ℤ) ^ 2 := by
  rcases i with b | h | _ <;> simp [cosetMat, Matrix.det_fin_two] <;> ring

theorem aCo_pos {p : ℕ} (hp : 0 < p) (i : HIdx p) : 0 < aCo p i := by
  rcases i with b | h | _ <;> simp [aCo] <;> positivity

theorem dCo_pos {p : ℕ} (hp : 0 < p) (i : HIdx p) : 0 < dCo p i := by
  rcases i with b | h | _ <;> simp [dCo] <;> positivity

/-! ## The Möbius action of integer matrices -/

/-- `X · τ = (aτ + b)/(cτ + d)` for an integer matrix `X`. -/
def mobZ (X : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  ((X 0 0 : ℂ) * τ + X 0 1) / ((X 1 0 : ℂ) * τ + X 1 1)

theorem mobZ_SL (γ : SL(2, ℤ)) (τ : ℂ) : mobZ (γ : Matrix (Fin 2) (Fin 2) ℤ) τ = mobius γ τ :=
  rfl

/-- The denominator `cτ + d` of an integer matrix. -/
def denZ (X : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) : ℂ := (X 1 0 : ℂ) * τ + X 1 1

theorem denZ_mul (X Y : Matrix (Fin 2) (Fin 2) ℤ) {τ : ℂ} (hY : denZ Y τ ≠ 0) :
    denZ (X * Y) τ = denZ X (mobZ Y τ) * denZ Y τ := by
  unfold denZ at hY
  simp only [denZ, mobZ, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

theorem div_frac_aux (a b c d A D : ℂ) (hD : D ≠ 0) :
    (a * (A / D) + b) / (c * (A / D) + d) = (a * A + b * D) / (c * A + d * D) := by
  rw [show a * (A / D) + b = (a * A + b * D) / D by field_simp,
    show c * (A / D) + d = (c * A + d * D) / D by field_simp, div_div_div_cancel_right₀ hD]

theorem mobZ_mul (X Y : Matrix (Fin 2) (Fin 2) ℤ) {τ : ℂ} (hY : denZ Y τ ≠ 0) :
    mobZ (X * Y) τ = mobZ X (mobZ Y τ) := by
  unfold denZ at hY
  rw [mobZ, mobZ, mobZ, div_frac_aux _ _ _ _ _ _ hY]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  congr 1 <;> ring

theorem mobZ_cosetMat_inl {p : ℕ} (b : Fin (p ^ 2)) (τ : ℂ) :
    mobZ (cosetMat p (.inl b)) τ = (τ + ((b : ℕ) : ℂ)) / ((p : ℂ) ^ 2) := by
  simp [mobZ, cosetMat]

theorem mobZ_cosetMat_inr_inl {p : ℕ} (hp : 0 < p) (h : Fin p) (τ : ℂ) :
    mobZ (cosetMat p (.inr (.inl h))) τ = τ + ((h : ℕ) : ℂ) / p := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  simp [mobZ, cosetMat]
  field_simp

theorem mobZ_cosetMat_inr_inr {p : ℕ} (u : Unit) (τ : ℂ) :
    mobZ (cosetMat p (.inr (.inr u))) τ = (p : ℂ) ^ 2 * τ := by
  simp [mobZ, cosetMat]

theorem denZ_cosetMat (p : ℕ) (i : HIdx p) (τ : ℂ) : denZ (cosetMat p i) τ = dCo p i := by
  simp [denZ, cosetMat_10, cosetMat_11]

theorem im_mobZ_cosetMat {p : ℕ} (hp : 0 < p) (i : HIdx p) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (mobZ (cosetMat p i) τ).im := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.2 hp
  rcases i with b | h | u
  · rw [mobZ_cosetMat_inl]
    have : ((τ + ((b : ℕ) : ℂ)) / ((p : ℂ) ^ 2)).im = τ.im / (p : ℝ) ^ 2 := by
      rw [show ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this]; positivity
  · rw [mobZ_cosetMat_inr_inl hp]
    have : (τ + ((h : ℕ) : ℂ) / p).im = τ.im := by
      rw [show ((h : ℕ) : ℂ) / p = (((h : ℕ) / p : ℝ) : ℂ) by push_cast; ring]
      simp
    rw [this]; exact hτ
  · rw [mobZ_cosetMat_inr_inr,
      show ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
    positivity

/-- For `δ ∈ SL₂(ℤ)` and a coset matrix, `(δ A) · τ = δ · (A · τ)`. -/
theorem mobZ_SL_mul_cosetMat {p : ℕ} (hp : 0 < p) (δ : SL(2, ℤ)) (j : HIdx p) (τ : ℂ) :
    mobZ ((δ : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p j) τ =
      mobius δ (mobZ (cosetMat p j) τ) := by
  rw [mobZ_mul _ _ (by rw [denZ_cosetMat]; exact_mod_cast (dCo_pos hp j).ne')]
  rfl

/-- `(A γ) · τ = A · (γ · τ)` for `γ ∈ SL₂(ℤ)`. -/
theorem mobZ_cosetMat_mul_SL {p : ℕ} (i : HIdx p) (γ : SL(2, ℤ)) {τ : ℂ}
    (hτ : 0 < τ.im) :
    mobZ (cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ =
      mobZ (cosetMat p i) (mobius γ τ) := by
  rw [mobZ_mul _ _ (denom_ne_zero γ hτ)]
  rfl

/-! ## Uniqueness of the representatives -/

theorem fin_val_eq_of_emod {n : ℕ} {x y : Fin n} (h : ((x : ℕ) : ℤ) ≡ ((y : ℕ) : ℤ) [ZMOD n]) :
    x = y := by
  have hx : ((x : ℕ) : ℤ) % n = (x : ℕ) := Int.emod_eq_of_lt (by positivity) (by
    have := x.2; omega)
  have hy : ((y : ℕ) : ℤ) % n = (y : ℕ) := Int.emod_eq_of_lt (by positivity) (by
    have := y.2; omega)
  unfold Int.ModEq at h
  rw [hx, hy] at h
  exact Fin.ext (by exact_mod_cast h)

/-- **The representatives are inequivalent**: `A_i = δ A_j` with `det δ = 1` forces `i = j`. -/
theorem cosetMat_unique {p : ℕ} (hp : 2 ≤ p) {i j : HIdx p} {δ : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : δ.det = 1) (h : cosetMat p i = δ * cosetMat p j) : i = j := by
  have e : ∀ a b, cosetMat p i a b = (δ * cosetMat p j) a b := fun a b => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cosetMat_10, cosetMat_00, cosetMat_11,
    mul_zero, add_zero] at e00 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have ha := aCo_pos (by omega : 0 < p) j
  have hd := dCo_pos (by omega : 0 < p) j
  have hai := aCo_pos (by omega : 0 < p) i
  have h10 : δ 1 0 = 0 := by
    rcases mul_eq_zero.1 e10.symm with h | h
    · exact h
    · exact absurd h ha.ne'
  rw [h10, zero_mul, zero_add] at e11
  rw [h10, mul_zero, sub_zero] at hdet
  have h00 : δ 0 0 = 1 := by
    have hpos : 0 < δ 0 0 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h11 : δ 1 1 = 1 := by rw [h00, one_mul] at hdet; exact hdet
  rw [h00, one_mul] at e00
  rw [h11, one_mul] at e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, one_mul] at e01
  rcases i with b | h | u <;> rcases j with b' | h' | u' <;>
    simp [aCo, dCo, cosetMat] at e00 e11 e01 ⊢
  all_goals first
    | (nlinarith)
    | skip
  · -- `b`, `b'`
    apply fin_val_eq_of_emod
    refine Int.modEq_iff_dvd.2 ⟨-(δ 0 1), ?_⟩
    push_cast
    linarith
  · apply fin_val_eq_of_emod
    refine Int.modEq_iff_dvd.2 ⟨-(δ 0 1), ?_⟩
    linarith

/-! ## Factorisations `A_i γ = δ A_j` -/

/-- From `A_i γ = δ A_j` (`γ ∈ SL₂(ℤ)`), `det δ = 1`. -/
theorem det_of_fact {p : ℕ} (hp : 0 < p) {i j : HIdx p} (γ : SL(2, ℤ))
    {δ : Matrix (Fin 2) (Fin 2) ℤ}
    (h : cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = δ * cosetMat p j) : δ.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, γ.det_coe, det_cosetMat, det_cosetMat, mul_one] at this
  have hp2 : ((p : ℤ) ^ 2) ≠ 0 := by positivity
  have h1 : (1 : ℤ) * (p : ℤ) ^ 2 = δ.det * (p : ℤ) ^ 2 := by rw [one_mul]; exact this
  exact (mul_right_cancel₀ hp2 h1).symm

/-- The factor as an element of `SL₂(ℤ)`. -/
def factSL {p : ℕ} (hp : 0 < p) {i j : HIdx p} (γ : SL(2, ℤ)) (δ : Matrix (Fin 2) (Fin 2) ℤ)
    (h : cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = δ * cosetMat p j) : SL(2, ℤ) :=
  ⟨δ, det_of_fact hp γ h⟩

/-- The lower-left entry: `δ₁₀ a_j = d_i c`. -/
theorem fact_10 {p : ℕ} {i j : HIdx p} {γ δ : Matrix (Fin 2) (Fin 2) ℤ}
    (h : cosetMat p i * γ = δ * cosetMat p j) : δ 1 0 * aCo p j = dCo p i * γ 1 0 := by
  have := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cosetMat_10, cosetMat_00, cosetMat_11,
    zero_mul, zero_add, mul_zero, add_zero] at this
  linarith

/-- The lower-right entry: `δ₁₀ b_j + δ₁₁ d_j = d_i d`. -/
theorem fact_11 {p : ℕ} {i j : HIdx p} {γ δ : Matrix (Fin 2) (Fin 2) ℤ}
    (h : cosetMat p i * γ = δ * cosetMat p j) :
    δ 1 0 * cosetMat p j 0 1 + δ 1 1 * dCo p j = dCo p i * γ 1 1 := by
  have := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cosetMat_10, cosetMat_11,
    zero_mul, zero_add] at this
  linarith

theorem aCo_coprime {p N : ℕ} (hpN : Nat.Coprime p N) (i : HIdx p) :
    IsCoprime (aCo p i) (N : ℤ) := by
  have h1 : IsCoprime (p : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 hpN
  rcases i with b | h | _
  · exact isCoprime_one_left
  · exact h1
  · simpa [aCo] using h1.pow_left (m := 2)

theorem dCo_coprime {p N : ℕ} (hpN : Nat.Coprime p N) (i : HIdx p) :
    IsCoprime (dCo p i) (N : ℤ) := by
  have h1 : IsCoprime (p : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 hpN
  rcases i with b | h | _
  · simpa [dCo] using h1.pow_left (m := 2)
  · exact h1
  · exact isCoprime_one_left

/-- `δ ∈ Γ₀(N)` when `γ ∈ Γ₀(N)` and `p ∤ N`. -/
theorem fact_dvd_10 {p N : ℕ} (hpN : Nat.Coprime p N) {i j : HIdx p}
    {γ δ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : (N : ℤ) ∣ γ 1 0)
    (h : cosetMat p i * γ = δ * cosetMat p j) : (N : ℤ) ∣ δ 1 0 := by
  have h1 := fact_10 h
  have h2 : (N : ℤ) ∣ δ 1 0 * aCo p j := h1 ▸ dvd_mul_of_dvd_right hγ _
  exact (aCo_coprime hpN j).symm.dvd_of_dvd_mul_right h2

/-- The lower-right entry of `δ` modulo `N`: `δ₁₁ d_j ≡ d_i d`. -/
theorem fact_11_mod {p N : ℕ} (hpN : Nat.Coprime p N) {i j : HIdx p}
    {γ δ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : (N : ℤ) ∣ γ 1 0)
    (h : cosetMat p i * γ = δ * cosetMat p j) :
    ((δ 1 1 : ℤ) : ZMod N) * (dCo p j : ZMod N) = (dCo p i : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) := by
  have h1 := fact_11 h
  have h2 := fact_dvd_10 hpN hγ h
  have h3 : ((δ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  have := congrArg (fun x : ℤ => (x : ZMod N)) h1
  push_cast at this
  rw [h3, zero_mul, zero_add] at this
  exact this


/-- **Injectivity of the induced permutation.** -/
theorem sigma_injective {p : ℕ} (hp : 2 ≤ p) (γ : SL(2, ℤ)) (σ : HIdx p → HIdx p)
    (δ : HIdx p → Matrix (Fin 2) (Fin 2) ℤ)
    (hfact : ∀ i, cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = δ i * cosetMat p (σ i)) :
    Function.Injective σ := by
  intro i i' hii
  have hp0 : 0 < p := by omega
  set g := factSL hp0 γ (δ i) (hfact i)
  set g' := factSL hp0 γ (δ i') (hfact i')
  have hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = δ i := rfl
  have hg' : (g' : Matrix (Fin 2) (Fin 2) ℤ) = δ i' := rfl
  have h1 := hfact i
  have h2 := hfact i'
  rw [← hii] at h2
  refine cosetMat_unique hp (δ := ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
    (g * g'⁻¹).det_coe ?_
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hg'i : ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g' : Matrix (Fin 2) (Fin 2) ℤ)
      = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc cosetMat p i = cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) *
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [Matrix.mul_assoc, hγ, Matrix.mul_one]
    _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * (((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (g' : Matrix (Fin 2) (Fin 2) ℤ)) * cosetMat p (σ i) *
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [h1, hg'i, Matrix.mul_one, hg]
    _ = ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (cosetMat p i' *
        (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [h2, ← hg', Matrix.SpecialLinearGroup.coe_mul]
        simp only [Matrix.mul_assoc]
    _ = ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p i' := by
        rw [Matrix.mul_assoc, hγ, Matrix.mul_one]

/-! ## Residues -/

/-- A residue representative in `Fin m`. -/
def rep (m : ℕ) (hm : 0 < m) (x : ℤ) : Fin m := WeilGalois.idxc hm x

theorem rep_modEq {m : ℕ} (hm : 0 < m) (x : ℤ) : (((rep m hm x : ℕ)) : ℤ) ≡ x [ZMOD m] :=
  WeilGalois.idxc_modEq hm x

/-- An inverse of `u` modulo `m` (meaningful when `u` is prime to `m`). -/
def binv (m : ℕ) (u : ℤ) : ℤ := if h : IsCoprime u (m : ℤ) then Classical.choose h else 0

theorem binv_spec {m : ℕ} {u : ℤ} (h : IsCoprime u (m : ℤ)) : u * binv m u ≡ 1 [ZMOD m] := by
  rw [binv, dif_pos h]
  obtain ⟨b, hb⟩ := Classical.choose_spec h
  exact Int.modEq_iff_dvd.2 ⟨b, by linear_combination (-1 : ℤ) * hb⟩

theorem isCoprime_of_not_dvd {p : ℕ} (hp : p.Prime) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    IsCoprime u (p : ℤ) :=
  ((Int.prime_iff_natAbs_prime.2 (by simpa using hp)).coprime_iff_not_dvd.2 hu).symm

theorem isCoprime_sq_of_not_dvd {p : ℕ} (hp : p.Prime) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    IsCoprime u (((p ^ 2 : ℕ)) : ℤ) := by
  push_cast; exact (isCoprime_of_not_dvd hp hu).pow_right

theorem dvd_of_modEq' {m : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD m]) : (m : ℤ) ∣ b - a :=
  Int.ModEq.dvd h

/-! ## The generator `L^N = (1 0; N 1)` -/

/-- `L^N = (1 0; N 1)`. -/
def matL (N : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by simp [Matrix.det_fin_two]⟩

theorem matL_coe (N : ℕ) : ((matL N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (N : ℤ), 1] :=
  rfl

section LN

variable {p : ℕ} (hp : p.Prime) (N : ℕ)

include hp in
theorem hp0 : 0 < p := hp.pos

include hp in
theorem hp2 : 0 < p ^ 2 := pow_pos hp.pos 2

/-- The permutation induced by `L^N`. -/
def sigmaL : HIdx p → HIdx p
  | .inl b =>
    let u : ℤ := 1 + N * ((b : ℕ) : ℤ)
    if ¬ (p : ℤ) ∣ u then .inl (rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * binv (p ^ 2) u))
    else if ¬ ((p : ℤ) ^ 2) ∣ u then
      .inr (.inl (rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p (u / p))))
    else .inr (.inr ())
  | .inr (.inl h) =>
    if (h : ℕ) = 0 then .inr (.inl h)
    else .inl (rep (p ^ 2) (hp2 hp) (((h : ℕ) : ℤ) * binv (p ^ 2) (p + ((h : ℕ) : ℤ) * N)))
  | .inr (.inr _) => .inl (rep (p ^ 2) (hp2 hp) (binv (p ^ 2) N))

/-- The `SL₂(ℤ)` factors for `L^N`. -/
def deltaL : HIdx p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl b =>
    let u : ℤ := 1 + N * ((b : ℕ) : ℤ)
    if ¬ (p : ℤ) ∣ u then
      let b' : ℤ := ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * binv (p ^ 2) u) : ℕ) : ℤ)
      !![u, (((b : ℕ) : ℤ) - b' * u) / (p : ℤ) ^ 2; N * (p : ℤ) ^ 2, 1 - N * b']
    else if ¬ ((p : ℤ) ^ 2) ∣ u then
      let w : ℤ := u / p
      let h : ℤ := ((rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p w) : ℕ) : ℤ)
      !![w, (((b : ℕ) : ℤ) - h * w) / p; N * p, p - N * h]
    else !![u / (p : ℤ) ^ 2, ((b : ℕ) : ℤ); N, (p : ℤ) ^ 2]
  | .inr (.inl h) =>
    if (h : ℕ) = 0 then !![1, 0; (N : ℤ), 1]
    else
      let v : ℤ := p + ((h : ℕ) : ℤ) * N
      let b'' : ℤ := ((rep (p ^ 2) (hp2 hp) (((h : ℕ) : ℤ) * binv (p ^ 2) v) : ℕ) : ℤ)
      !![v, (((h : ℕ) : ℤ) - b'' * v) / (p : ℤ) ^ 2; p * N, (1 - N * b'') / p]
  | .inr (.inr _) =>
    let b' : ℤ := ((rep (p ^ 2) (hp2 hp) (binv (p ^ 2) N) : ℕ) : ℤ)
    !![(p : ℤ) ^ 2, -b'; N, (1 - N * b') / (p : ℤ) ^ 2]

theorem eq_fin_two {a b c d a' b' c' d' : ℤ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4; rfl

include hp in
/-- **Factorisation for `L^N`**: `A_i L^N = δ_i A_{σ i}`. -/
theorem factL (hpN : ¬ (p : ℤ) ∣ N) (i : HIdx p) :
    cosetMat p i * ((matL N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      deltaL hp N i * cosetMat p (sigmaL hp N i) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases i with b | h | u
  · simp only [sigmaL, deltaL]
    by_cases h1 : (p : ℤ) ∣ 1 + N * ((b : ℕ) : ℤ)
    · by_cases h2 : ((p : ℤ) ^ 2) ∣ 1 + N * ((b : ℕ) : ℤ)
      · rw [if_neg (not_not.2 h1), if_neg (not_not.2 h1), if_neg (not_not.2 h2),
          if_neg (not_not.2 h2)]
        have hq := Int.ediv_mul_cancel h2
        simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
        generalize (1 + N * ((b : ℕ) : ℤ)) / (p : ℤ) ^ 2 = q at hq ⊢
        apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq
      · rw [if_neg (not_not.2 h1), if_neg (not_not.2 h1), if_pos h2, if_pos h2]
        have hwu := Int.ediv_mul_cancel h1
        have hwp : ¬ (p : ℤ) ∣ (1 + N * ((b : ℕ) : ℤ)) / p := by
          rintro ⟨k, hk⟩; apply h2; exact ⟨k, by rw [← hwu, hk]; ring⟩
        have hmod : ((rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p ((1 + N * ((b : ℕ) : ℤ)) / p))
            : ℕ) : ℤ) * ((1 + N * ((b : ℕ) : ℤ)) / p) ≡ ((b : ℕ) : ℤ) [ZMOD p] := by
          have e1 := rep_modEq (hp0 hp) (((b : ℕ) : ℤ) * binv p ((1 + N * ((b : ℕ) : ℤ)) / p))
          have e2 := binv_spec (isCoprime_of_not_dvd hp hwp)
          refine (e1.mul_right _).trans ?_
          rw [mul_assoc, mul_comm (binv _ _)]
          simpa using e2.mul_left ((b : ℕ) : ℤ)
        have hq := Int.ediv_mul_cancel (Int.ModEq.dvd hmod)
        simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
        generalize (1 + N * ((b : ℕ) : ℤ)) / (p : ℤ) = w at hq hwu ⊢
        generalize ((rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p w) : ℕ) : ℤ) = hh at hq ⊢
        generalize (((b : ℕ) : ℤ) - hh * w) / p = y at hq ⊢
        apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq |
          linear_combination (-1 : ℤ) * hwu
    · rw [if_pos h1, if_pos h1]
      have hcop := isCoprime_sq_of_not_dvd hp h1
      have hmod : ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * binv (p ^ 2) (1 + N * ((b : ℕ) : ℤ)))
          : ℕ) : ℤ) * (1 + N * ((b : ℕ) : ℤ)) ≡ ((b : ℕ) : ℤ) [ZMOD (p ^ 2 : ℕ)] := by
        have e1 := rep_modEq (hp2 hp) (((b : ℕ) : ℤ) * binv (p ^ 2) (1 + N * ((b : ℕ) : ℤ)))
        have e2 := binv_spec hcop
        refine (e1.mul_right _).trans ?_
        rw [mul_assoc, mul_comm (binv _ _)]
        simpa using e2.mul_left ((b : ℕ) : ℤ)
      have hd := Int.ModEq.dvd hmod
      push_cast at hd
      have hq := Int.ediv_mul_cancel hd
      simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
      generalize ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * binv (p ^ 2) (1 + N * ((b : ℕ) : ℤ)))
          : ℕ) : ℤ) = b' at hq ⊢
      generalize (((b : ℕ) : ℤ) - b' * (1 + N * ((b : ℕ) : ℤ))) / (p : ℤ) ^ 2 = y at hq ⊢
      apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq
  · rcases h with ⟨h, hlt⟩
    simp only [sigmaL, deltaL]
    by_cases h0 : h = 0
    · subst h0
      simp only [if_true]
      simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
      apply eq_fin_two <;> simp; ring
    · rw [if_neg h0, if_neg h0]
      have hhp : ¬ (p : ℤ) ∣ (h : ℤ) := by
        intro hd
        have : p ∣ h := by exact_mod_cast hd
        exact h0 (Nat.eq_zero_of_dvd_of_lt this hlt)
      have hvp : ¬ (p : ℤ) ∣ (p + (h : ℤ) * N) := by
        intro hd
        have : (p : ℤ) ∣ (h : ℤ) * N := by
          have := (dvd_sub hd (dvd_refl (p : ℤ))); simpa using this
        rcases hpp.dvd_or_dvd this with h' | h'
        · exact hhp h'
        · exact hpN h'
      have hcop := isCoprime_sq_of_not_dvd hp hvp
      have hmod : ((rep (p ^ 2) (hp2 hp) ((h : ℤ) * binv (p ^ 2) (p + (h : ℤ) * N)) : ℕ) : ℤ) *
          (p + (h : ℤ) * N) ≡ (h : ℤ) [ZMOD (p ^ 2 : ℕ)] := by
        have e1 := rep_modEq (hp2 hp) ((h : ℤ) * binv (p ^ 2) (p + (h : ℤ) * N))
        have e2 := binv_spec hcop
        refine (e1.mul_right _).trans ?_
        rw [mul_assoc, mul_comm (binv _ _)]
        simpa using e2.mul_left (h : ℤ)
      set b'' : ℤ := ((rep (p ^ 2) (hp2 hp) ((h : ℤ) * binv (p ^ 2) (p + (h : ℤ) * N)) : ℕ) : ℤ)
        with hb''
      have hd : (p : ℤ) ^ 2 ∣ (h : ℤ) - b'' * (p + (h : ℤ) * N) := by
        have := Int.ModEq.dvd hmod; push_cast at this; exact this
      have hd2 : (p : ℤ) ∣ 1 - N * b'' := by
        have h3 : (p : ℤ) ∣ (h : ℤ) - b'' * (p + (h : ℤ) * N) :=
          (dvd_pow_self (p : ℤ) two_ne_zero).trans hd
        have h4 : (p : ℤ) ∣ (h : ℤ) * (1 - N * b'') := by
          have : (h : ℤ) * (1 - N * b'') = ((h : ℤ) - b'' * (p + (h : ℤ) * N)) + p * b'' := by ring
          rw [this]; exact dvd_add h3 (dvd_mul_right _ _)
        rcases hpp.dvd_or_dvd h4 with h' | h'
        · exact absurd h' hhp
        · exact h'
      have hq := Int.ediv_mul_cancel hd
      have hq2 := Int.ediv_mul_cancel hd2
      simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
      generalize ((h : ℤ) - b'' * (p + (h : ℤ) * N)) / (p : ℤ) ^ 2 = y at hq ⊢
      generalize (1 - N * b'') / (p : ℤ) = z at hq2 ⊢
      apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq |
        linear_combination (-(p : ℤ)) * hq2
  · simp only [sigmaL, deltaL]
    have hcop := isCoprime_sq_of_not_dvd hp hpN
    have hmod : (N : ℤ) * ((rep (p ^ 2) (hp2 hp) (binv (p ^ 2) N) : ℕ) : ℤ) ≡ 1
        [ZMOD (p ^ 2 : ℕ)] := by
      have e1 := rep_modEq (hp2 hp) (binv (p ^ 2) N)
      exact (e1.mul_left _).trans (binv_spec hcop)
    have hd := Int.ModEq.dvd hmod
    push_cast at hd
    have hq := Int.ediv_mul_cancel hd
    simp only [cosetMat, matL_coe, Matrix.mul_fin_two]
    generalize ((rep (p ^ 2) (hp2 hp) (binv (p ^ 2) N) : ℕ) : ℤ) = b' at hq ⊢
    generalize (1 - N * b') / (p : ℤ) ^ 2 = z at hq ⊢
    apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq

end LN


/-! ## The diagonal generators `γ ≡ diag(ℓ, ℓ') (mod p²)` -/

section G3

variable {p : ℕ} (hp : p.Prime) (ℓ' : ℤ)

/-- The permutation induced by `γ ≡ diag(ℓ, ℓ')`: `b ↦ b ℓ'²`, `h ↦ h ℓ'²`, `∞ ↦ ∞`. -/
def sigmaG : HIdx p → HIdx p
  | .inl b => .inl (rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * ℓ' ^ 2))
  | .inr (.inl h) => .inr (.inl (rep p (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2)))
  | .inr (.inr u) => .inr (.inr u)

/-- The factors for `γ ≡ diag(ℓ, ℓ')`. -/
def deltaG (γ : Matrix (Fin 2) (Fin 2) ℤ) : HIdx p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl b =>
    let b' : ℤ := ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * ℓ' ^ 2) : ℕ) : ℤ)
    !![γ 0 0 + (b : ℤ) * γ 1 0,
      (γ 0 1 + (b : ℤ) * γ 1 1 - b' * (γ 0 0 + (b : ℤ) * γ 1 0)) / (p : ℤ) ^ 2;
      (p : ℤ) ^ 2 * γ 1 0, γ 1 1 - b' * γ 1 0]
  | .inr (.inl h) =>
    let h' : ℤ := ((rep p (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2) : ℕ) : ℤ)
    !![γ 0 0 + (h : ℤ) * (γ 1 0 / p),
      ((p : ℤ) * γ 0 1 + (h : ℤ) * γ 1 1 - (γ 0 0 + (h : ℤ) * (γ 1 0 / p)) * h') / p;
      γ 1 0, γ 1 1 - (γ 1 0 / p) * h']
  | .inr (.inr _) => !![γ 0 0, (p : ℤ) ^ 2 * γ 0 1; γ 1 0 / (p : ℤ) ^ 2, γ 1 1]

theorem zmod_eq_of_dvd {m : ℕ} {x y : ℤ} (h : (m : ℤ) ∣ x - y) : (x : ZMod m) = y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y m).2 (by
    rw [show y - x = -(x - y) by ring]; exact (dvd_neg).2 h)

include hp in
/-- **Factorisation for `γ ≡ diag(ℓ, ℓ') (mod p²)`.** -/
theorem factG (ℓ : ℤ) (γ : Matrix (Fin 2) (Fin 2) ℤ) (h00 : (p : ℤ) ^ 2 ∣ γ 0 0 - ℓ)
    (h11 : (p : ℤ) ^ 2 ∣ γ 1 1 - ℓ') (h01 : (p : ℤ) ^ 2 ∣ γ 0 1) (h10 : (p : ℤ) ^ 2 ∣ γ 1 0)
    (hℓ : (p : ℤ) ^ 2 ∣ ℓ * ℓ' - 1) (i : HIdx p) :
    cosetMat p i * γ = deltaG hp ℓ' γ i * cosetMat p (sigmaG hp ℓ' i) := by
  have hpd : (p : ℤ) ∣ (p : ℤ) ^ 2 := dvd_pow_self _ two_ne_zero
  rw [Matrix.eta_fin_two γ]
  rcases i with b | h | u
  · simp only [sigmaG, deltaG, cosetMat, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hb' := rep_modEq (hp2 hp) (((b : ℕ) : ℤ) * ℓ' ^ 2)
    generalize ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) * ℓ' ^ 2) : ℕ) : ℤ) = b' at hb' ⊢
    have hd : (p : ℤ) ^ 2 ∣ γ 0 1 + (b : ℤ) * γ 1 1 - b' * (γ 0 0 + (b : ℤ) * γ 1 0) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (γ 0 1 + (b : ℤ) * γ 1 1 - b' * (γ 0 0 + (b : ℤ) * γ 1 0)) (p ^ 2)).1
      push_cast at this
      apply this
      have e1 : ((γ 0 0 : ℤ) : ZMod (p ^ 2)) = ℓ := zmod_eq_of_dvd (by push_cast; exact h00)
      have e2 : ((γ 1 1 : ℤ) : ZMod (p ^ 2)) = ℓ' := zmod_eq_of_dvd (by push_cast; exact h11)
      have e3 : ((γ 0 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
        have := zmod_eq_of_dvd (m := p ^ 2) (x := γ 0 1) (y := 0) (by push_cast; simpa using h01)
        simpa using this
      have e4 : ((γ 1 0 : ℤ) : ZMod (p ^ 2)) = 0 := by
        have := zmod_eq_of_dvd (m := p ^ 2) (x := γ 1 0) (y := 0) (by push_cast; simpa using h10)
        simpa using this
      have e5 : ((b' : ℤ) : ZMod (p ^ 2)) = ((b : ℕ) : ZMod (p ^ 2)) * (ℓ' : ZMod (p ^ 2)) ^ 2 := by
        have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hb'
        push_cast at this ⊢; exact this
      have e6 : (ℓ : ZMod (p ^ 2)) * ℓ' = 1 := by
        have := zmod_eq_of_dvd (m := p ^ 2) (x := ℓ * ℓ') (y := 1) (by push_cast; exact hℓ)
        push_cast at this; exact this
      rw [e1, e2, e3, e4, e5]
      linear_combination (-((b : ℕ) : ZMod (p ^ 2)) * (ℓ' : ZMod (p ^ 2))) * e6
    have hq := Int.ediv_mul_cancel hd
    generalize (γ 0 1 + (b : ℤ) * γ 1 1 - b' * (γ 0 0 + (b : ℤ) * γ 1 0)) / (p : ℤ) ^ 2 = y
      at hq ⊢
    apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq
  · simp only [sigmaG, deltaG, cosetMat, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hh' := rep_modEq (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2)
    generalize ((rep p (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2) : ℕ) : ℤ) = h' at hh' ⊢
    have hc : (p : ℤ) ∣ γ 1 0 := hpd.trans h10
    have he := Int.ediv_mul_cancel hc
    have hep : (p : ℤ) ∣ γ 1 0 / p := by
      obtain ⟨k, hk⟩ := h10
      refine ⟨k, ?_⟩
      rw [hk, show (p : ℤ) ^ 2 * k = p * (p * k) by ring,
        Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)]
    generalize γ 1 0 / (p : ℤ) = e at he hep ⊢
    have hd : (p : ℤ) ∣ (p : ℤ) * γ 0 1 + (h : ℤ) * γ 1 1 - (γ 0 0 + (h : ℤ) * e) * h' := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd
        ((p : ℤ) * γ 0 1 + (h : ℤ) * γ 1 1 - (γ 0 0 + (h : ℤ) * e) * h') p).1
      apply this
      push_cast
      have e1 : ((γ 0 0 : ℤ) : ZMod p) = ℓ := zmod_eq_of_dvd (hpd.trans h00)
      have e2 : ((γ 1 1 : ℤ) : ZMod p) = ℓ' := zmod_eq_of_dvd (hpd.trans h11)
      have e4 : ((e : ℤ) : ZMod p) = 0 := by
        have := zmod_eq_of_dvd (m := p) (x := e) (y := 0) (by simpa using hep)
        simpa using this
      have e5 : ((h' : ℤ) : ZMod p) = ((h : ℕ) : ZMod p) * (ℓ' : ZMod p) ^ 2 := by
        have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hh'
        push_cast at this ⊢; exact this
      have e6 : (ℓ : ZMod p) * ℓ' = 1 := by
        have := zmod_eq_of_dvd (m := p) (x := ℓ * ℓ') (y := 1) (hpd.trans hℓ)
        push_cast at this; exact this
      have e7 : ((p : ℤ) : ZMod p) = 0 := by simp
      rw [e1, e2, e4, e5]
      push_cast at e7 ⊢
      rw [e7]
      linear_combination (-((h : ℕ) : ZMod p) * (ℓ' : ZMod p)) * e6
    have hq := Int.ediv_mul_cancel hd
    generalize ((p : ℤ) * γ 0 1 + (h : ℤ) * γ 1 1 - (γ 0 0 + (h : ℤ) * e) * h') / p = y at hq ⊢
    apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq |
      linear_combination (-(h : ℤ)) * he | linear_combination (-(h' : ℤ)) * he |
      linear_combination (h' : ℤ) * he
  · simp only [sigmaG, deltaG, cosetMat, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hq := Int.ediv_mul_cancel h10
    generalize γ 1 0 / (p : ℤ) ^ 2 = y at hq ⊢
    apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq

end G3

/-! ## The translation `T` -/

section Tsec

variable {p : ℕ} (hp : p.Prime)

/-- The permutation induced by `T`. -/
def sigmaT : HIdx p → HIdx p
  | .inl b => .inl (rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) + 1))
  | .inr x => .inr x

/-- The factors for `T`. -/
def deltaT : HIdx p → Matrix (Fin 2) (Fin 2) ℤ
  | .inl b => !![1, (((b : ℕ) : ℤ) + 1 - ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) + 1) : ℕ) : ℤ))
      / (p : ℤ) ^ 2; 0, 1]
  | .inr (.inl _) => !![1, 1; 0, 1]
  | .inr (.inr _) => !![1, (p : ℤ) ^ 2; 0, 1]

include hp in
theorem factT (i : HIdx p) :
    cosetMat p i * ((matT : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      deltaT hp i * cosetMat p (sigmaT hp i) := by
  have hT : ((matT : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 1; 0, 1] := rfl
  rw [hT]
  rcases i with b | h | u
  · simp only [sigmaT, deltaT, cosetMat, Matrix.mul_fin_two]
    have hb' := rep_modEq (hp2 hp) (((b : ℕ) : ℤ) + 1)
    generalize ((rep (p ^ 2) (hp2 hp) (((b : ℕ) : ℤ) + 1) : ℕ) : ℤ) = b' at hb' ⊢
    have hd : (p : ℤ) ^ 2 ∣ ((b : ℕ) : ℤ) + 1 - b' := by
      have := Int.ModEq.dvd hb'; push_cast at this; exact this
    have hq := Int.ediv_mul_cancel hd
    generalize (((b : ℕ) : ℤ) + 1 - b') / (p : ℤ) ^ 2 = y at hq ⊢
    apply eq_fin_two <;> first | ring1 | linear_combination (-1 : ℤ) * hq
  · simp only [sigmaT, deltaT, cosetMat, Matrix.mul_fin_two]
    apply eq_fin_two <;> ring
  · simp only [sigmaT, deltaT, cosetMat, Matrix.mul_fin_two]
    apply eq_fin_two <;> ring

end Tsec

end SSHecke

end VOA.Classification.COne
