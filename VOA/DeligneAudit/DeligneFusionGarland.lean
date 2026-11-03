import VOA.DeligneAudit.DeligneFusionKernel

/-!
# Garland-type identities for `sl₂[t]` and `RavinderKernelTrunc`

Route chosen (minimal formalization): **not** the full Chari–Pressley generating function
`(e⊗t)^{(s)}(f)^{(s+r)} w = (-1)^s (x⁻(u)^{(r)} P(u))_s w`, but its special case with `P(u) = 1`
(all `h ⊗ t^k`, `k ≥ 1`, kill `w`), proved through the single operator `E₁ = e ⊗ t`:

* `E₁ · F(u)^{q+2} ≡ -(q+2)(q+1) F(u)^q F'(u)` modulo the left ideal of series killing `w`, where
  `F(u) = ∑ f⊗t^k u^k`.  Since `F^q F' = (F^{q+1})'/(q+1)`, this reads
  `E₁ Q(q+2, j) = -(q+2)(j+1) Q(q+1, j+1)` for `Q(q, j) = [u^j] F(u)^q w`;
* iterating, `E₁^s f^{s+2} w` is a nonzero multiple of `Q(2, s) = ∑_{i+j=s} (f⊗t^i)(f⊗t^j) w`,
  so `Q(2, s) = 0` once `f^{s+2} w = 0`.

For the `θ`-triple of `sl₃` the needed `f_θ^{2n+1} w = 0` comes from the Heisenberg algebra
`⟨f₁, f₂, f_θ⟩` (part A).  Then `RavinderKernelTrunc` follows by extracting single terms (part D).
-/

namespace VOA.DeligneAudit.Garland

/-! ## Part A: a Heisenberg nilpotency lemma -/

section Heis

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {X Y Z : Module.End ℂ V} (hXY : X * Y - Y * X = Z) (hXZ : X * Z = Z * X)
  (hYZ : Y * Z = Z * Y)
include hXY hYZ

theorem pow_mul_X : ∀ k : ℕ, Y ^ (k + 1) * X = X * Y ^ (k + 1) - (k + 1) • (Z * Y ^ k)
  | 0 => by rw [← hXY]; simp
  | k + 1 => by
      have ih := pow_mul_X k
      have hYX : Y * X = X * Y - Z := by rw [← hXY]; abel
      calc Y ^ (k + 2) * X = Y * (Y ^ (k + 1) * X) := by rw [pow_succ' Y (k + 1), mul_assoc]
        _ = Y * (X * Y ^ (k + 1) - (k + 1) • (Z * Y ^ k)) := by rw [ih]
        _ = (Y * X) * Y ^ (k + 1) - (k + 1) • ((Y * Z) * Y ^ k) := by
            rw [mul_sub, mul_smul_comm, mul_assoc, mul_assoc]
        _ = (X * Y - Z) * Y ^ (k + 1) - (k + 1) • ((Z * Y) * Y ^ k) := by rw [hYX, hYZ]
        _ = X * Y ^ (k + 2) - (k + 2) • (Z * Y ^ (k + 1)) := by
            rw [pow_succ' Y (k + 1), mul_assoc Z Y, sub_mul, mul_assoc, ← pow_succ' Y (k + 1)]
            rw [show (k + 2) • (Z * Y ^ (k + 1)) = (k + 1) • (Z * Y ^ (k + 1)) + Z * Y ^ (k + 1) by
              rw [succ_nsmul]]
            rw [← pow_succ']; abel

theorem Ypow_Xpow_apply {m : ℕ} {u : V} (hu : (Y ^ m) u = 0) :
    ∀ j : ℕ, (Y ^ (m + j)) ((X ^ j) u) = 0
  | 0 => by simpa using hu
  | j + 1 => by
      have ih := Ypow_Xpow_apply hu j
      rw [pow_succ' X j, Module.End.mul_apply, ← Module.End.mul_apply (Y ^ (m + (j + 1))),
        show m + (j + 1) = m + j + 1 by omega, pow_mul_X hXY hYZ (m + j), LinearMap.sub_apply,
        Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, pow_succ',
        Module.End.mul_apply, ih]
      simp

/-- The commutator with `X`. -/
def adX (X : Module.End ℂ V) (T : Module.End ℂ V) : Module.End ℂ V := X * T - T * X

omit hXY hYZ in
theorem adX_Zmul (hXZ : X * Z = Z * X) (n : ℕ) (T : Module.End ℂ V) :
    adX X (n • (Z * T)) = n • (Z * adX X T) := by
  simp only [adX, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  congr 1
  rw [mul_sub, ← mul_assoc, hXZ, mul_assoc, mul_assoc]

omit hXY hYZ in
theorem iterate_adX_Zmul (hXZ : X * Z = Z * X) :
    ∀ (i n : ℕ) (T : Module.End ℂ V), (adX X)^[i] (n • (Z * T)) = n • (Z * (adX X)^[i] T)
  | 0, _, _ => rfl
  | i + 1, n, T => by
      rw [Function.iterate_succ_apply, adX_Zmul hXZ, iterate_adX_Zmul hXZ i,
        Function.iterate_succ_apply]

theorem iterate_adX_pow (hXZ : X * Z = Z * X) :
    ∀ (i r : ℕ), (adX X)^[i] (Y ^ (i + r)) = ((i + r).descFactorial i) • (Z ^ i * Y ^ r)
  | 0, r => by simp
  | i + 1, r => by
      rw [Function.iterate_succ_apply]
      have h1 : adX X (Y ^ (i + 1 + r)) = (i + r + 1) • (Z * Y ^ (i + r)) := by
        rw [adX, show i + 1 + r = i + r + 1 by omega, pow_mul_X hXY hYZ (i + r)]; abel
      rw [h1, iterate_adX_Zmul hXZ, iterate_adX_pow hXZ i r, mul_smul_comm, smul_smul,
        ← mul_assoc, ← pow_succ', show i + 1 + r = (i + r) + 1 by omega,
        Nat.succ_descFactorial_succ]

omit hXY hYZ in
theorem adX_kills {w : V} {T : Module.End ℂ V} (hT : ∀ j, T ((X ^ j) w) = 0) :
    ∀ j, (adX X T) ((X ^ j) w) = 0 := by
  intro j
  rw [adX, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hT j,
    ← Module.End.mul_apply X, ← pow_succ', hT (j + 1), map_zero, sub_zero]

/-- **Heisenberg nilpotency**: if `[X, Y] = Z` is central in `⟨X, Y⟩` and `X^{p+1} w = Y^{p+1} w = 0`,
then `Z^{2p+1} w = 0`. -/
theorem heis_nilpotent (hXZ : X * Z = Z * X) {p : ℕ} {w : V} (hX : (X ^ (p + 1)) w = 0)
    (hY : (Y ^ (p + 1)) w = 0) : (Z ^ (2 * p + 1)) w = 0 := by
  have h0 : ∀ j, (Y ^ (2 * p + 1)) ((X ^ j) w) = 0 := by
    intro j
    by_cases hj : j ≤ p
    · rw [show 2 * p + 1 = (p - j) + (p + 1 + j) by omega, pow_add, Module.End.mul_apply,
        Ypow_Xpow_apply hXY hYZ hY j, map_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + (p + 1) := ⟨j - (p + 1), by omega⟩
      rw [pow_add X, Module.End.mul_apply, hX, map_zero, map_zero]
  have hit : ∀ i, ∀ j, ((adX X)^[i] (Y ^ (2 * p + 1))) ((X ^ j) w) = 0 := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih => rw [Function.iterate_succ_apply']; exact adX_kills ih
  have h := hit (2 * p + 1) 0
  rw [show Y ^ (2 * p + 1) = Y ^ ((2 * p + 1) + 0) from rfl, iterate_adX_pow hXY hYZ hXZ,
    pow_zero, mul_one, Nat.descFactorial_self, pow_zero, Module.End.one_apply,
    LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)

end Heis

/-! ## Part B: the `P(u) = 1` Garland identity, quadratic case -/

noncomputable section

open PowerSeries

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Series whose coefficients all kill `w`. -/
def Kills (w : V) (P : PowerSeries (Module.End ℂ V)) : Prop := ∀ n, (coeff n P) w = 0

theorem kills_mul_left {w : V} {P : PowerSeries (Module.End ℂ V)} (S : PowerSeries (Module.End ℂ V))
    (h : Kills w P) : Kills w (S * P) := by
  intro n
  rw [coeff_mul, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun x _ => by rw [Module.End.mul_apply, h, map_zero]

theorem kills_add {w : V} {P Q : PowerSeries (Module.End ℂ V)} (hP : Kills w P) (hQ : Kills w Q) :
    Kills w (P + Q) := by
  intro n; rw [map_add, LinearMap.add_apply, hP, hQ, add_zero]

theorem kills_smul {w : V} {P : PowerSeries (Module.End ℂ V)} (c : ℂ) (hP : Kills w P) :
    Kills w (c • P) := by
  intro n; rw [coeff_smul, LinearMap.smul_apply, hP, smul_zero]

theorem kills_of_eq {w : V} {P Q : PowerSeries (Module.End ℂ V)} (hP : Kills w P) (h : P = Q) :
    Kills w Q := h ▸ hP

/-- The formal derivative (no commutativity needed). -/
def Dop (P : PowerSeries (Module.End ℂ V)) : PowerSeries (Module.End ℂ V) :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℂ) • coeff (n + 1) P

theorem Dop_mul (P Q : PowerSeries (Module.End ℂ V)) : Dop (P * Q) = Dop P * Q + P * Dop Q := by
  refine PowerSeries.ext fun n => ?_
  simp only [Dop, coeff_mk, map_add, coeff_mul]
  have h1 : ∀ x ∈ Finset.antidiagonal (n + 1), ((n + 1 : ℕ) : ℂ) • (coeff x.1 P * coeff x.2 Q) =
      (x.1 : ℂ) • (coeff x.1 P * coeff x.2 Q) + (x.2 : ℂ) • (coeff x.1 P * coeff x.2 Q) := by
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [← add_smul, ← hx]; push_cast; ring_nf
  rw [Finset.smul_sum, Finset.sum_congr rfl h1, Finset.sum_add_distrib,
    Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_smul, zero_add]
  simp only [smul_mul_assoc, mul_smul_comm]

variable (E1 : Module.End ℂ V) (H F : ℕ → Module.End ℂ V)

/-- `F(u) = ∑ F_k u^k`. -/
def Fs : PowerSeries (Module.End ℂ V) := PowerSeries.mk F
/-- `∑ H_{k+1} u^k`. -/
def Hs : PowerSeries (Module.End ℂ V) := PowerSeries.mk fun k => H (k + 1)

theorem rel_EF (hEF : ∀ k, E1 * F k - F k * E1 = H (k + 1)) :
    PowerSeries.C E1 * Fs F = Fs F * PowerSeries.C E1 + Hs H := by
  refine PowerSeries.ext fun n => ?_
  simp only [map_add, coeff_C_mul, coeff_mul_C, Fs, Hs, coeff_mk]
  rw [← hEF n]; abel

theorem rel_HF (hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) = (-2 : ℂ) • F (m + 1 + k)) :
    Hs H * Fs F = Fs F * Hs H + (-2 : ℂ) • Dop (Fs F) := by
  refine PowerSeries.ext fun n => ?_
  simp only [map_add, coeff_smul, coeff_mul, Fs, Hs, Dop, coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap (f := fun x : ℕ × ℕ => F x.1 * H (x.2 + 1))]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  have : ∀ x ∈ Finset.antidiagonal n, H (x.1 + 1) * F x.2 - F x.2 * H (x.1 + 1) =
      (-2 : ℂ) • F (n + 1) := by
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [hHF, show x.1 + 1 + x.2 = n + 1 by omega]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.Nat.card_antidiagonal, smul_comm,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem rel_FD (hFF : ∀ j k, F j * F k = F k * F j) :
    Fs F * Dop (Fs F) = Dop (Fs F) * Fs F := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_mul, Fs, Dop, coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap (f := fun x : ℕ × ℕ => (((x.1 + 1 : ℕ) : ℂ) • F (x.1 + 1)) * F x.2)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [mul_smul_comm, smul_mul_assoc, hFF]

section Kill

variable {E1 H F} (hEF : ∀ k, E1 * F k - F k * E1 = H (k + 1))
  (hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) = (-2 : ℂ) • F (m + 1 + k))
  (hFF : ∀ j k, F j * F k = F k * F j) {w : V} (hE : E1 w = 0) (hH : ∀ m, H (m + 1) w = 0)
include hHF hFF hH

omit hHF hFF in
theorem kills_Hs : Kills w (Hs H) := fun n => by simp [Hs, coeff_mk, hH]

theorem kills_H_pow : ∀ p : ℕ,
    Kills w (Hs H * Fs F ^ (p + 1) + ((2 * (p + 1) : ℕ) : ℂ) • (Fs F ^ p * Dop (Fs F)))
  | 0 => by
      refine kills_of_eq (kills_mul_left (Fs F) (kills_Hs hH)) ?_
      rw [zero_add, pow_one, pow_zero, one_mul, rel_HF H F hHF]; push_cast; module
  | p + 1 => by
      have ih := kills_H_pow p
      have hDB : Dop (Fs F) * Fs F ^ (p + 1) = Fs F ^ (p + 1) * Dop (Fs F) :=
        ((Commute.pow_right (rel_FD F hFF).symm (p + 1))).eq
      refine kills_of_eq (kills_mul_left (Fs F) ih) ?_
      rw [pow_succ' (Fs F) (p + 1), ← mul_assoc, rel_HF H F hHF, add_mul, mul_assoc, smul_mul_assoc,
        hDB, mul_add, mul_smul_comm, ← mul_assoc (Fs F) (Fs F ^ p), ← pow_succ']
      push_cast; module

include hEF hE in
theorem kills_E1 : Kills w (PowerSeries.C E1 * Fs F) := by
  rw [rel_EF E1 H F hEF]
  refine kills_add (kills_mul_left _ fun n => ?_) (kills_Hs hH)
  rw [coeff_C]; split_ifs <;> simp [hE]

omit hHF hFF hH in
theorem C_mul_pow_succ (hEF : ∀ k, E1 * F k - F k * E1 = H (k + 1)) (k : ℕ) :
    PowerSeries.C E1 * Fs F ^ (k + 1) = Fs F * (PowerSeries.C E1 * Fs F ^ k) + Hs H * Fs F ^ k := by
  rw [pow_succ', ← mul_assoc, rel_EF E1 H F hEF, add_mul, mul_assoc]

omit hHF hFF hH in
theorem F_mul_powD (k : ℕ) : Fs F * (Fs F ^ k * Dop (Fs F)) = Fs F ^ (k + 1) * Dop (Fs F) := by
  rw [← mul_assoc, ← pow_succ']

include hEF hE in
theorem kills_E_pow : ∀ q : ℕ,
    Kills w (PowerSeries.C E1 * Fs F ^ (q + 1 + 1) +
      (((q + 2) * (q + 1) : ℕ) : ℂ) • (Fs F ^ q * Dop (Fs F)))
  | 0 => by
      refine kills_of_eq (kills_add (kills_mul_left (Fs F) (kills_E1 hEF hHF hFF hE hH))
        (kills_H_pow hHF hFF hH 0)) ?_
      rw [C_mul_pow_succ hEF (0 + 1), pow_one]
      push_cast; module
  | q + 1 => by
      refine kills_of_eq (kills_add (kills_mul_left (Fs F) (kills_E_pow q))
        (kills_H_pow hHF hFF hH (q + 1))) ?_
      rw [C_mul_pow_succ hEF (q + 1 + 1), mul_add, mul_smul_comm, F_mul_powD]
      push_cast; module

omit hHF hH in
theorem Dop_pow : ∀ q : ℕ, Dop (Fs F ^ (q + 1)) = ((q + 1 : ℕ) : ℂ) • (Fs F ^ q * Dop (Fs F))
  | 0 => by simp
  | q + 1 => by
      rw [pow_succ (Fs F) (q + 1), Dop_mul, Dop_pow q, smul_mul_assoc, mul_assoc,
        ← rel_FD F hFF, ← mul_assoc, ← pow_succ]
      push_cast; module

include hEF hE in
/-- **One Garland step**: `E₁ Q(q+2, j) = -(q+2)(j+1) Q(q+1, j+1)`. -/
theorem E_step (q j : ℕ) : E1 ((coeff j (Fs F ^ (q + 2))) w) =
    (-(((q + 2) * (j + 1) : ℕ) : ℂ)) • (coeff (j + 1) (Fs F ^ (q + 1))) w := by
  have h := kills_E_pow hEF hHF hFF hE hH q j
  rw [map_add, coeff_C_mul, coeff_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at h
  have hD := congrArg (coeff j) (Dop_pow hFF q)
  rw [Dop, coeff_mk, coeff_smul] at hD
  have hX : coeff j (Fs F ^ q * Dop (Fs F)) =
      (((j + 1 : ℕ) : ℂ) / ((q + 1 : ℕ) : ℂ)) • coeff (j + 1) (Fs F ^ (q + 1)) := by
    rw [div_eq_inv_mul, mul_smul, hD, inv_smul_smul₀ (by exact_mod_cast Nat.succ_ne_zero q)]
  rw [hX, LinearMap.smul_apply, smul_smul] at h
  rw [eq_neg_of_add_eq_zero_left h, ← neg_smul]
  congr 2
  push_cast
  field_simp

include hEF hE in
theorem E_iter (q : ℕ) : ∀ (s j : ℕ), ∃ c : ℂ, c ≠ 0 ∧
    (E1 ^ s) ((coeff j (Fs F ^ (q + 1 + s)) : Module.End ℂ V) w) =
      c • ((coeff (j + s) (Fs F ^ (q + 1)) : Module.End ℂ V) w)
  | 0, j => ⟨1, one_ne_zero, by simp⟩
  | s + 1, j => by
      obtain ⟨c, hc, h⟩ := E_iter q s (j + 1)
      refine ⟨(-(((q + s + 2) * (j + 1) : ℕ) : ℂ)) * c, mul_ne_zero (by
        rw [neg_ne_zero]; exact_mod_cast (by positivity : (q + s + 2) * (j + 1) ≠ 0)) hc, ?_⟩
      rw [pow_succ, Module.End.mul_apply, show q + 1 + (s + 1) = (q + s) + 2 by omega,
        E_step hEF hHF hFF hE hH (q + s) j, map_smul, show q + s + 1 = q + 1 + s by omega, h,
        smul_smul, show j + 1 + s = j + (s + 1) by omega]

include hEF hE in
/-- **Garland identity with `P(u) = 1`**: if `F₀^N w = 0` then `[u^s] F(u)^r w = 0`, i.e.
`∑_{k₁+⋯+k_r = s} F_{k₁} ⋯ F_{k_r} w = 0`, for all `r ≥ 1` and `r + s ≥ N`. -/
theorem garland (r : ℕ) (hr : 1 ≤ r) {N : ℕ} (hN : (F 0 ^ N) w = 0) (s : ℕ) (hs : N ≤ r + s) :
    (coeff s (Fs F ^ r) : Module.End ℂ V) w = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, hc, h⟩ := E_iter hEF hHF hFF hE hH q s 0
  have h0 : (coeff 0 (Fs F ^ (q + 1 + s))) w = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, Fs, constantCoeff_mk,
      show q + 1 + s = (q + 1 + s - N) + N by omega, pow_add, Module.End.mul_apply, hN, map_zero]
  rw [h0, map_zero, zero_add, eq_comm, smul_eq_zero] at h
  exact h.resolve_left hc

include hEF hE in
/-- **Quadratic Garland identity with `P(u) = 1`**: if `F₀^N w = 0` then
`∑_{i+j=s} F_i F_j w = 0` for all `s ≥ N - 2`. -/
theorem garland_two {N : ℕ} (hN : (F 0 ^ N) w = 0) (s : ℕ) (hs : N ≤ s + 2) :
    ∑ x ∈ Finset.antidiagonal s, F x.1 (F x.2 w) = 0 := by
  have h2 := garland hEF hHF hFF hE hH 2 (by norm_num) hN s (by omega)
  rw [pow_two, coeff_mul, LinearMap.coe_sum, Finset.sum_apply] at h2
  simpa [Fs, coeff_mk, Module.End.mul_apply] using h2

end Kill

end

end VOA.DeligneAudit.Garland
