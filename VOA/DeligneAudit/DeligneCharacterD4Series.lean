/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Euler

/-!
# The D₄ kernel `M` as a power series in `s` (layer 2)

* `R = 𝕜[x^{±1}, z₁^{±1}, …, z₄^{±1}]` (`AddMonoidAlgebra 𝕜 (Fin 5 → ℤ)`, coordinate `0 = x`, `1..4 = z`),
  `S = R⟦s⟧`.
* `EInv c v k = 1/(c·z^v s^k; q)_∞` and `EPos c v k = (c·z^v s^k; q)_∞`, obtained from layer 1 by
  `liftS`, `rescale (single v c)` and `expand k`.
* Their transported laws `EInv_mul_one_sub`, `EPos_eq`, `EPos_mul_EInv`.
* `twist χ b`: the `𝕜`-algebra automorphism `z^v ↦ b^{χ(v)} z^v` of `R` (all the `q`- and `√q`-shifts
  of the paper are twists), with `map_twist_EInv`, `map_twist_EPos`.
* `rescale` in `s`: `rescale_EInv`, `rescale_EPos`.
* The kernel `kernelM = (t)(tx²)(tx⁻²) / ∏_{ε, a} (s x^ε a)` with `t = s²`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- Exponent lattice: `x, z₁, …, z₄`. -/
abbrev V := Fin 5 → ℤ

/-- `R = 𝕜[x^{±1}, z^{±1}]`. -/
abbrev R := AddMonoidAlgebra Kq V

/-- `S = R⟦s⟧`. -/
abbrev S := PowerSeries R

/-- Monomial `c · z^v`. -/
def mon (v : V) (c : Kq) : R := AddMonoidAlgebra.single v c

theorem mon_mul_mon (v w : V) (c d : Kq) : mon v c * mon w d = mon (v + w) (c * d) := by
  rw [mon, mon, mon, AddMonoidAlgebra.single_mul_single]

theorem mon_pow (v : V) (c : Kq) (n : ℕ) : mon v c ^ n = mon (n • v) (c ^ n) := by
  simp [mon, AddMonoidAlgebra.single_pow]

theorem algebraMap_mul_mon (a c : Kq) (v : V) : algebraMap Kq R a * mon v c = mon v (a * c) := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mon, mon,
    AddMonoidAlgebra.smul_single', mul_comm]

/-- Coefficients from `𝕜` to `R`. -/
def liftS : PowerSeries Kq →+* S := PowerSeries.map (algebraMap Kq R)

theorem liftS_X : liftS X = X := map_X _

/-- `map φ` commutes with `expand`. -/
theorem map_expand (φ : R →+* R) (k : ℕ) (hk : k ≠ 0) (f : S) :
    PowerSeries.map φ (expand k hk f) = expand k hk (PowerSeries.map φ f) := by
  ext n : 1
  rw [coeff_map, coeff_expand, coeff_expand]
  split_ifs <;> simp [coeff_map]

/-- `1/(c z^v s^k; q)_∞`. -/
def EInv (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) : S :=
  expand k hk (rescale (mon v c) (liftS eInv))

/-- `(c z^v s^k; q)_∞`. -/
def EPos (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) : S :=
  expand k hk (rescale (mon v c) (liftS ePos))

theorem liftS_rescale_qq (f : PowerSeries Kq) :
    liftS (rescale qq f) = rescale (algebraMap Kq R qq) (liftS f) := by
  rw [liftS, rescale_map]

theorem expand_rescale_one_sub (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    expand k hk (rescale (mon v c) (1 - X : S)) = 1 - mon v c • X ^ k := by
  rw [map_sub, map_one, rescale_X, map_sub, map_one, ← smul_eq_C_mul, expand_smul, expand_X]

/-- `1/(a;q)_∞ · (1 - a) = 1/(qa;q)_∞`. -/
theorem EInv_mul_one_sub (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    EInv c v k hk * (1 - mon v c • X ^ k) = EInv (qq * c) v k hk := by
  have h := congrArg (fun f => expand k hk (rescale (mon v c) (liftS f))) eInv_mul_one_sub
  simp only [map_mul, liftS_rescale_qq, rescale_rescale, algebraMap_mul_mon] at h
  rw [map_sub, map_one, liftS_X] at h
  rw [EInv, EInv, ← h, ← expand_rescale_one_sub]

/-- `(a;q)_∞ = (1 - a)(qa;q)_∞`. -/
theorem EPos_eq (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    EPos c v k hk = (1 - mon v c • X ^ k) * EPos (qq * c) v k hk := by
  have h := congrArg (fun f => expand k hk (rescale (mon v c) (liftS f))) ePos_eq
  simp only [map_mul, liftS_rescale_qq, rescale_rescale, algebraMap_mul_mon] at h
  rw [map_sub, map_one, liftS_X] at h
  rw [EPos, EPos, h, ← expand_rescale_one_sub]

theorem EPos_mul_EInv (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    EPos c v k hk * EInv c v k hk = 1 := by
  rw [EPos, EInv, ← map_mul, ← map_mul, ← map_mul, ePos_mul_eInv, map_one, map_one, map_one]

/-! ## Twists -/

/-- The character twist `z^v ↦ b^{χ v} z^v` as a monoid hom. -/
def twistHom (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) : Multiplicative V →* R where
  toFun v := mon (Multiplicative.toAdd v) (b ^ χ (Multiplicative.toAdd v))
  map_one' := by simp [mon]; rfl
  map_mul' v w := by
    rw [mon_mul_mon, toAdd_mul, map_add, zpow_add₀ hb]

/-- The twist `z^v ↦ b^{χ(v)} z^v`, a `𝕜`-algebra endomorphism of `R`. -/
def twist (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) : R →ₐ[Kq] R :=
  AddMonoidAlgebra.lift Kq R V (twistHom χ b hb)

theorem twist_mon (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (v : V) (c : Kq) :
    twist χ b hb (mon v c) = mon v (b ^ χ v * c) := by
  rw [twist, mon, AddMonoidAlgebra.lift_single]
  simp only [twistHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [mon, mon, AddMonoidAlgebra.smul_single', mul_comm]

theorem map_twist_liftS (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (f : PowerSeries Kq) :
    PowerSeries.map (twist χ b hb : R →+* R) (liftS f) = liftS f := by
  rw [liftS, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 2
  exact (twist χ b hb).comp_algebraMap

theorem map_twist_EInv (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.map (twist χ b hb : R →+* R) (EInv c v k hk) = EInv (b ^ χ v * c) v k hk := by
  rw [EInv, EInv, map_expand, ← rescale_map, map_twist_liftS]
  rw [show ((twist χ b hb : R →+* R) (mon v c)) = mon v (b ^ χ v * c) from twist_mon χ b hb v c]

theorem map_twist_EPos (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.map (twist χ b hb : R →+* R) (EPos c v k hk) = EPos (b ^ χ v * c) v k hk := by
  rw [EPos, EPos, map_expand, ← rescale_map, map_twist_liftS]
  rw [show ((twist χ b hb : R →+* R) (mon v c)) = mon v (b ^ χ v * c) from twist_mon χ b hb v c]

/-! ## Rescaling `s` -/

theorem rescale_expand (b : R) (k : ℕ) (hk : k ≠ 0) (f : S) :
    rescale b (expand k hk f) = expand k hk (rescale (b ^ k) f) := by
  ext n : 1
  rw [coeff_rescale, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_rescale, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk), pow_mul]
  · rw [mul_zero]

/-- `s ↦ a s` on `1/(c z^v s^k)`: `c ↦ a^k c`. -/
theorem rescale_EInv (a c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    rescale (algebraMap Kq R a) (EInv c v k hk) = EInv (a ^ k * c) v k hk := by
  rw [EInv, EInv, rescale_expand, rescale_rescale, ← map_pow, mul_comm, algebraMap_mul_mon]

theorem rescale_EPos (a c : Kq) (v : V) (k : ℕ) (hk : k ≠ 0) :
    rescale (algebraMap Kq R a) (EPos c v k hk) = EPos (a ^ k * c) v k hk := by
  rw [EPos, EPos, rescale_expand, rescale_rescale, ← map_pow, mul_comm, algebraMap_mul_mon]

/-! ## The kernel -/

/-- The `x` direction. -/
def xv : V := Pi.single 0 1

/-- The `zᵢ` direction. -/
def zv (i : Fin 4) : V := Pi.single i.succ 1

/-- The sixteen hypermultiplet weights `x^ε z_i^σ`. -/
def hyperVecs : List V :=
  [1, -1].flatMap fun ε : ℤ => (List.finRange 4).flatMap fun i => [1, -1].map fun σ : ℤ =>
    ε • xv + σ • zv i

/-- `(t;q)(tx²;q)(tx⁻²;q)` with `t = s²`. -/
def tFactors : S :=
  EPos 1 0 2 two_ne_zero * EPos 1 (2 • xv) 2 two_ne_zero * EPos 1 (-2 • xv) 2 two_ne_zero

/-- `1/∏_{ε,a}(s x^ε a; q)_∞`. -/
def hyperFactors : S := (hyperVecs.map fun v => EInv 1 v 1 one_ne_zero).prod

/-- **The D₄ kernel** `M = (t)(tx²)(tx⁻²)/∏(s x^{±1} z_i^{±1})`, so that `K = ½ Θ(x) M`. -/
def kernelM : S := tFactors * hyperFactors

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.EInv_mul_one_sub
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.EPos_eq
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.map_twist_EInv
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.rescale_EInv
end AxiomAudit
