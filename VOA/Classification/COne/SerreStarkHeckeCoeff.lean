/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeStable

/-!
# Serre–Stark S3-2: the `q`-expansion of `T(p²) f`

`SSHecke.coeff_heckeT`: if `f = Σ a(n) qⁿ ∈ M_{1/2}(N, χ)` then
`T(p²) f = Σ b(n) qⁿ` with

`b(n) = a(p² n) + χ(p) (n/p) p⁻¹ a(n) + χ(p)² p⁻¹ a(n/p²)`

(`a(n/p²) = 0` unless `p² ∣ n`) — Shimura's formula at weight `½`.
-/

open Complex Filter Topology
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

/-! ## The twisted additive sum `Σ_h (h/p) e(nh/p) = (n/p) g_p` -/

section Twist

variable {p : ℕ} [hpf : Fact p.Prime]

/-- The quadratic character with complex values. -/
def chq (p : ℕ) [Fact p.Prime] (y : ZMod p) : ℂ := ((quadraticChar (ZMod p) y : ℤ) : ℂ)

theorem sum_chq_mulShift (hp2 : p ≠ 2) (a : ZMod p) :
    ∑ y : ZMod p, chq p y * ZMod.stdAddChar (a * y) =
      chq p a * ∑ y : ZMod p, chq p y * ZMod.stdAddChar y := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one, chq, quadraticChar_zero,
      Int.cast_zero]
    have := quadraticChar_sum_zero hF
    exact_mod_cast this
  · rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun y => ?_)
    rw [show (Equiv.mulLeft₀ a ha) y = a * y from rfl]
    simp only [chq]
    rw [show quadraticChar (ZMod p) (a * y) = quadraticChar (ZMod p) a * quadraticChar (ZMod p) y
      from map_mul _ a y]
    have hsq := quadraticChar_sq_one ha
    push_cast
    have : ((quadraticChar (ZMod p) a : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
    linear_combination (-(((quadraticChar (ZMod p) y : ℤ) : ℂ) *
      ZMod.stdAddChar (a * y))) * this

theorem gs_one_eq_chq (hp2 : p ≠ 2) :
    gs p 1 = ∑ y : ZMod p, chq p y * ZMod.stdAddChar y := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [gs_zmod]
  simp only [Int.cast_one, one_mul]
  rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
  have fib : ∀ y : ZMod p, ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y),
      (ZMod.stdAddChar (x ^ 2) : ℂ) = (chq p y + 1) * ZMod.stdAddChar y := by
    intro y
    rw [Finset.sum_congr rfl (g := fun _ => (ZMod.stdAddChar y : ℂ)) (fun x hx => by
      rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hc := quadraticChar_card_sqrts hF y
    have : ({x : ZMod p | x ^ 2 = y}.toFinset) = Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)
      := by ext; simp
    rw [this] at hc
    simp only [chq]
    exact_mod_cast hc
  simp_rw [fib, add_mul, one_mul, Finset.sum_add_distrib]
  have van : ∑ y : ZMod p, (ZMod.stdAddChar y : ℂ) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p one_ne_zero |> fun h => by
      intro h1; have := h; simpa [AddChar.mulShift_apply, h1] using this)
  rw [van, add_zero]

/-- **The twisted sum**: `Σ_{h mod p} (h/p) e(nh/p) = (n/p) g(p, 1)`. -/
theorem sum_leg_E (hp2 : p ≠ 2) (n : ℤ) :
    ∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) * E p (n * ((h : ℕ) : ℤ)) =
      (legendreSym p n : ℂ) * gs p 1 := by
  have hp0 := hpf.out.pos
  have hF : ∀ x : ℤ, (legendreSym p (x + p) : ℂ) * E p (n * (x + p)) =
      (legendreSym p x : ℂ) * E p (n * x) := by
    intro x
    congr 1
    · rw [legendreSym.mod, Int.add_emod_right, ← legendreSym.mod]
    · rw [show n * (x + p) = n * x + p * n by ring, E_period hp0]
  rw [← resid_sum hp0 (fun x => (legendreSym p x : ℂ) * E p (n * x)) hF (ZMod.card p)
    (fun y : ZMod p => ((y.val : ℕ) : ℤ))]
  · have e : ∀ y : ZMod p, (legendreSym p ((y.val : ℕ) : ℤ) : ℂ) * E p (n * ((y.val : ℕ) : ℤ)) =
        chq p y * ZMod.stdAddChar ((n : ZMod p) * y) := by
      intro y
      congr 1
      · simp [chq, legendreSym]
      · rw [show ((n : ZMod p) * y) = (((n * ((y.val : ℕ) : ℤ) : ℤ)) : ZMod p) by
          push_cast; rw [ZMod.natCast_zmod_val], ZMod.stdAddChar_coe]
        rfl
    simp_rw [e]
    rw [sum_chq_mulShift hp2, gs_one_eq_chq hp2]
    simp [chq, legendreSym]
  · intro x y h
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 h
    push_cast at this
    simpa [ZMod.natCast_zmod_val] using this

end Twist


/-! ## The three pieces of `T(p²) f` -/

section Pieces

variable {N : ℕ} {p : ℕ} [hpf : Fact p.Prime] {f : ℂ → ℂ}

theorem hasSum_nat_reindex {s : ℕ} (hs : 0 < s) {F : ℕ → ℂ} (hF : ∀ n, ¬ s ∣ n → F n = 0)
    {a : ℂ} (h : HasSum (fun m => F (s * m)) a) : HasSum F a := by
  have hinj : Function.Injective (fun m : ℕ => s * m) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hs hxy
  refine (hinj.hasSum_iff ?_).1 h
  rintro x hx
  apply hF
  rintro ⟨k, rfl⟩
  exact hx ⟨k, rfl⟩

theorem hasSum_nat_reindex' {s : ℕ} (hs : 0 < s) {F : ℕ → ℂ} (hF : ∀ n, ¬ s ∣ n → F n = 0)
    {a : ℂ} (h : HasSum F a) : HasSum (fun m => F (s * m)) a := by
  have hinj : Function.Injective (fun m : ℕ => s * m) := fun x y hxy =>
    Nat.eq_of_mul_eq_mul_left hs hxy
  refine (hinj.hasSum_iff ?_).2 h
  rintro x hx
  apply hF
  rintro ⟨k, rfl⟩
  exact hx ⟨k, rfl⟩

theorem cexp_nat_mul (n : ℕ) (w : ℂ) : cexp (2 * Real.pi * I * n * w) =
    cexp (2 * Real.pi * I * w) ^ n := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

/-- The `b`-cosets: `Σ_b f((τ+b)/p²) = p² Σ_m a(p² m) q^m`. -/
theorem hasSum_piece_b (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℕ => (p : ℂ) ^ 2 * thetaTypeCoeff f (p ^ 2 * m) *
      cexp (2 * Real.pi * I * m * τ))
      (∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ)) := by
  have hp0 := hpf.out.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have H : HasSum (fun n : ℕ => ∑ b : Fin (p ^ 2), thetaTypeCoeff f n *
      cexp (2 * Real.pi * I * n * mobZ (cosetMat p (.inl b)) τ))
      (∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ)) :=
    hasSum_sum fun b _ => hf.hasSum_coeff (im_mobZ_cosetMat hp0 _ hτ)
  have e : ∀ n : ℕ, ∑ b : Fin (p ^ 2), thetaTypeCoeff f n *
      cexp (2 * Real.pi * I * n * mobZ (cosetMat p (.inl b)) τ) =
      thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * τ / (p : ℂ) ^ 2) *
        (if ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) then ((p ^ 2 : ℕ) : ℂ) else 0) := by
    intro n
    rw [← sum_E_lin hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mobZ_cosetMat_inl, E_eq, mul_assoc (thetaTypeCoeff f n), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
  simp_rw [e] at H
  have H2 := hasSum_nat_reindex' hP (fun n hn => by
    rw [if_neg (fun h => hn (by exact_mod_cast h)), mul_zero]) H
  refine H2.congr_fun fun m => ?_
  rw [if_pos (by push_cast; exact dvd_mul_right _ _)]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * I * ((p : ℂ) ^ 2 * m) * τ / (p : ℂ) ^ 2 =
    2 * Real.pi * I * m * τ by field_simp]
  ring

/-- The `h`-cosets: `Σ_h (h/p) f(τ + h/p) = g_p Σ_n (n/p) a(n) qⁿ`. -/
theorem hasSum_piece_h (hp2 : p ≠ 2) (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => thetaTypeCoeff f n * ((legendreSym p (n : ℤ) : ℂ) * gs p 1) *
      cexp (2 * Real.pi * I * n * τ))
      (∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) *
        f (mobZ (cosetMat p (.inr (.inl h))) τ)) := by
  have hp0 := hpf.out.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have H : HasSum (fun n : ℕ => ∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) *
      (thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * mobZ (cosetMat p (.inr (.inl h))) τ)))
      (∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) *
        f (mobZ (cosetMat p (.inr (.inl h))) τ)) :=
    hasSum_sum fun h _ => (hf.hasSum_coeff (im_mobZ_cosetMat hp0 _ hτ)).mul_left _
  refine H.congr_fun fun n => ?_
  rw [← sum_leg_E hp2, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mobZ_cosetMat_inr_inl hp0, E_eq]
  have : cexp (2 * Real.pi * I * n * (τ + ((h : ℕ) : ℂ) / p)) =
      cexp (2 * Real.pi * I * ((n * ((h : ℕ) : ℤ) : ℤ) : ℂ) / p) * cexp (2 * Real.pi * I * n * τ) := by
    rw [← Complex.exp_add]; congr 1; push_cast; field_simp; ring
  rw [this]
  ring

/-- The `∞`-coset: `f(p²τ) = Σ_m a(m/p²) q^m`. -/
theorem hasSum_piece_inf (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℕ => (if p ^ 2 ∣ m then thetaTypeCoeff f (m / p ^ 2) else 0) *
      cexp (2 * Real.pi * I * m * τ)) (f (mobZ (cosetMat p (.inr (.inr ()))) τ)) := by
  have hp0 := hpf.out.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  refine hasSum_nat_reindex hP (fun n hn => by rw [if_neg hn, zero_mul]) ?_
  have H := hf.hasSum_coeff (im_mobZ_cosetMat hp0 (.inr (.inr ())) hτ)
  refine H.congr_fun fun m => ?_
  rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hP, mobZ_cosetMat_inr_inr]
  push_cast
  ring_nf

end Pieces

/-! ## Shimura's formula -/

/-- The coefficient sequence of `T(p²) f`. -/
def heckeCoeff {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) [Fact p.Prime] (a : ℕ → ℂ)
    (n : ℕ) : ℂ :=
  a (p ^ 2 * n) + χ (p : ZMod N) * (legendreSym p (n : ℤ) : ℂ) / p * a n +
    χ (p : ZMod N) ^ 2 / p * (if p ^ 2 ∣ n then a (n / p ^ 2) else 0)

theorem heckeT_eq_pieces {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} [Fact p.Prime]
    (f : ℂ → ℂ) (τ : ℂ) :
    heckeT χ p f τ = 1 / (p : ℂ) ^ 2 * ∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ) +
      χ (p : ZMod N) / ((p : ℂ) * gs p 1) * ∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) *
        f (mobZ (cosetMat p (.inr (.inl h))) τ) +
      χ (p : ZMod N) ^ 2 / p * f (mobZ (cosetMat p (.inr (.inr ()))) τ) := by
  unfold heckeT
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have e1 : ∑ b : Fin (p ^ 2), hw p (.inl b) * kap χ p (.inl b) *
      f (mobZ (cosetMat p (.inl b)) τ) =
      1 / (p : ℂ) ^ 2 * ∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hw, kap, aCo]
  have e2 : ∑ h : Fin p, hw p (.inr (.inl h)) * kap χ p (.inr (.inl h)) *
      f (mobZ (cosetMat p (.inr (.inl h))) τ) =
      χ (p : ZMod N) / ((p : ℂ) * gs p 1) * ∑ h : Fin p, (legendreSym p ((h : ℕ) : ℤ) : ℂ) *
        f (mobZ (cosetMat p (.inr (.inl h))) τ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [hw, kap, aCo]
    push_cast
    ring
  have e3 : ∑ u : Unit, hw p (.inr (.inr u)) * kap χ p (.inr (.inr u)) *
      f (mobZ (cosetMat p (.inr (.inr u))) τ) =
      χ (p : ZMod N) ^ 2 / p * f (mobZ (cosetMat p (.inr (.inr ()))) τ) := by
    simp only [Finset.univ_unique, Finset.sum_singleton, hw, kap, aCo]
    push_cast
    rw [map_pow]
    ring
  rw [e1, e2, e3]
  ring

/-- **Shimura's formula for `T(p²)` at weight `½`.** -/
theorem coeff_heckeT {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} [hpf : Fact p.Prime]
    (hp2 : p ≠ 2) (h24 : 24 ∣ N) (hpN : Nat.Coprime p N) {f : ℂ → ℂ}
    (hf : IsThetaTypeFormChar N χ f) (n : ℕ) :
    thetaTypeCoeff (heckeT χ p f) n = heckeCoeff χ p (thetaTypeCoeff f) n := by
  have hp0 := hpf.out.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have hG := gs_p_one_ne_zero hpf.out hp2
  have hF := isThetaTypeFormChar_heckeT χ hp2 h24 hpN hf
  refine hF.thetaType.coeff_eq_of_hasSum (fun τ hτ => ?_) n
  have H := (((hasSum_piece_b (p := p) hf.thetaType hτ).mul_left (1 / (p : ℂ) ^ 2)).add
    ((hasSum_piece_h (p := p) hp2 hf.thetaType hτ).mul_left
      (χ (p : ZMod N) / ((p : ℂ) * gs p 1)))).add
    ((hasSum_piece_inf (p := p) hf.thetaType hτ).mul_left (χ (p : ZMod N) ^ 2 / p))
  rw [heckeT_eq_pieces]
  refine H.congr_fun fun m => ?_
  simp only [heckeCoeff]
  field_simp

end SSHecke

end VOA.Classification.COne
