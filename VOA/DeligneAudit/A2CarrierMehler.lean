/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierMehlerFinite

/-!
# The shifted Mehler identity `U_m (q)_∞³ (1 - q^{m+1}) = m + 1`

Proof (all infinite sums are handled modulo `X^{N+1}` with the truncation toolkit):

1. `tser_one_mul`: `T_p := ∑_i q^i (q)_{i+p}/(q)_i` satisfies `T_p (1 - q^{p+1}) = 1`, from two
   linear relations between `T_c(p) = ∑_i q^{c i}(q)_{i+p}/(q)_i` for `c = 1, 2`;
2. `trunc_rsy_sum`: `∑_k q^k H_k(q^c)/(q)_k = (q)_c/(q)_∞²` (two Euler sums);
3. `trunc_wsum`: `∑_w q^w/(q)_w ∑_i [w,i] q^{p i} (q)_{w-i+p} = (q)_p T_p/(q)_∞`;
4. `shiftedU_mul_euler`: `U_m (q)_∞³ = ∑_{j ≤ m} [m,j] (q)_{m-j} T_{m-j}`, from
   `G_{k+w+m} = ∑_j [m,j] ∑_i [w,i] q^{(m-j) i} H_k(q^{w-i+m-j})` (`rogersSzego_add`, `rsy_add`);
5. `shiftedMehler`: multiply by `1 - q^{m+1}`, use `[m,j](1-q^{m+1}) = [m+1,j](1-q^{m+1-j})`,
   `T_p (1-q^{p+1}) = 1` and `∑_{j < n} [n,j](q)_{n-1-j} = n`.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.QSeries VOA.DeligneGaussian

noncomputable section

local notation "q" => (PowerSeries.X : PowerSeries ℤ)
local notation "cc" => (reciprocalQFactorial : ℕ → PowerSeries ℤ)

/-! ### Step 1: `T_p (1 - q^{p+1}) = 1` -/

/-- `T_c(p) = ∑_i q^{c i} (q)_{i+p}/(q)_i`. -/
def tser (c p : ℕ) : PowerSeries ℤ := powerShiftSum c fun i => qFactorial q (i + p) * cc i

theorem tser_rel1 (c p : ℕ) (hc : 0 < c) :
    tser c (p + 1) = tser c p - q ^ (p + 1) * tser (c + 1) p := by
  rw [tser, tser, tser, powerShiftSum_add_exponent c 1, mul_comm (q ^ (p + 1)),
    ← powerShiftSum_mul c hc, ← powerShiftSum_sub c hc]
  apply powerShiftSum_congr
  intro i
  rw [show i + (p + 1) = (i + p) + 1 by omega, qFactorial_succ]
  rw [show i + p + 1 = (p + 1) + 1 * i by ring, pow_add]
  ring

theorem tser_rel2 (c p : ℕ) (hc : 0 < c) :
    q ^ c * tser c (p + 1) = tser c p - tser (c + 1) p := by
  have h1 := powerShiftSum_succ c hc (fun i => qFactorial q (i + p) * cc i)
  have h2 := powerShiftSum_succ (c + 1) (by omega) (fun i => qFactorial q (i + p) * cc i)
  have key : (powerShiftSum c fun i => qFactorial q (i + (p + 1)) * cc i) =
      (powerShiftSum c fun j => qFactorial q (j + 1 + p) * cc (j + 1)) -
        q * powerShiftSum c (fun j => q ^ (1 * j) * (qFactorial q (j + 1 + p) * cc (j + 1))) := by
    rw [mul_comm q, ← powerShiftSum_mul c hc, ← powerShiftSum_sub c hc]
    apply powerShiftSum_congr
    intro i
    have h := one_sub_X_pow_mul_reciprocalQFactorial (R := ℤ) i
    rw [show i + 1 + p = i + (p + 1) by omega, one_mul]
    calc qFactorial q (i + (p + 1)) * cc i
        = qFactorial q (i + (p + 1)) * ((1 - q ^ (i + 1)) * cc (i + 1)) := by rw [h]
      _ = _ := by rw [pow_succ]; ring
  rw [tser, tser, tser, h1, h2, powerShiftSum_add_exponent c 1, key, pow_succ]
  ring

theorem tser_one_zero : tser 1 0 * (1 - q) = 1 := by
  have hs := powerShiftSum_succ 1 one_pos (fun _ : ℕ => (1 : PowerSeries ℤ))
  have ht : tser 1 0 = powerShiftSum 1 (fun _ : ℕ => (1 : PowerSeries ℤ)) := by
    rw [tser]
    apply powerShiftSum_congr
    intro i
    rw [Nat.add_zero, qFactorial_mul_reciprocal]
  rw [ht]
  rw [pow_one] at hs
  set S := powerShiftSum 1 (fun _ : ℕ => (1 : PowerSeries ℤ))
  linear_combination hs

/-- **`T_p (1 - q^{p+1}) = 1`**, i.e. `∑_i q^i [i+p, p] = 1/(q)_{p+1}` up to `(q)_p`. -/
theorem tser_one_mul : ∀ p, tser 1 p * (1 - q ^ (p + 1)) = 1
  | 0 => by rw [zero_add, pow_one]; exact tser_one_zero
  | p + 1 => by
    have h1 := tser_rel1 1 p one_pos
    have h2 := tser_rel2 1 p one_pos
    have ih := tser_one_mul p
    rw [pow_one] at h2
    -- `T(1,p+1)(1 - q^{p+2}) = T(1,p)(1 - q^{p+1})`
    have key : tser 1 (p + 1) * (1 - q ^ (p + 1 + 1)) = tser 1 p * (1 - q ^ (p + 1)) := by
      rw [show (q : PowerSeries ℤ) ^ (p + 1 + 1) = q ^ (p + 1) * q by rw [pow_succ]]
      linear_combination h1 - q ^ (p + 1) * h2
    rw [key, ih]

/-! ### Step 2: `∑_k q^k H_k(q^c)/(q)_k = (q)_c/(q)_∞²` -/

theorem trunc_eulerSum (N A : ℕ) (hA : 0 < A) :
    trunc N (∑ j ∈ Finset.range (N + 1), q ^ (A * j) * cc j) =
      trunc N (qFactorial q (A - 1) * reciprocalEuler) := by
  rw [← trunc_powerShiftSum N A hA, ← eulerSum, eulerSum_eq A hA]

theorem trunc_rsy_sum (N c : ℕ) :
    trunc N (∑ k ∈ Finset.range (N + 1), q ^ k * (cc k * rsy c k)) =
      trunc N (qFactorial q c * reciprocalEuler ^ 2) := by
  have hdiag : (∑ k ∈ Finset.range (N + 1), q ^ k * (cc k * rsy c k)) =
      ∑ n ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
        (fun a b => q ^ (a + b) * (q ^ (c * a) * (cc a * cc b))) i (n - i) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_comm (cc n), rsy_mul_c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    dsimp only
    rw [show i + (n - i) = n by omega]
  rw [hdiag, trunc_diag N (fun a b => q ^ (a + b) * (q ^ (c * a) * (cc a * cc b)))
    (fun a b hab => trunc_X_pow_mul N (a + b) hab _)]
  have hbox : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
      q ^ (a + b) * (q ^ (c * a) * (cc a * cc b))) =
      (∑ a ∈ Finset.range (N + 1), q ^ ((c + 1) * a) * cc a) *
        (∑ b ∈ Finset.range (N + 1), q ^ (1 * b) * cc b) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show (c + 1) * a = a + c * a by ring, pow_add, pow_add, one_mul]
    ring
  rw [hbox, map_mul, trunc_eulerSum N (c + 1) (by omega), trunc_eulerSum N 1 one_pos, ← map_mul]
  congr 1
  rw [Nat.add_sub_cancel, Nat.sub_self, qFactorial_zero]
  ring

/-! ### Step 3: the `w`-sum -/

theorem trunc_wsum (N p : ℕ) :
    trunc N (∑ w ∈ Finset.range (N + 1), q ^ w * (cc w *
      ∑ i ∈ Finset.range (w + 1), gaussian q w i * q ^ (p * i) * qFactorial q (w - i + p))) =
      trunc N (qFactorial q p * reciprocalEuler * tser 1 p) := by
  have hdiag : (∑ w ∈ Finset.range (N + 1), q ^ w * (cc w *
      ∑ i ∈ Finset.range (w + 1), gaussian q w i * q ^ (p * i) * qFactorial q (w - i + p))) =
      ∑ n ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
        (fun a b => q ^ (a + b) * (q ^ (p * a) * cc a * (qFactorial q (b + p) * cc b)))
          i (n - i) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    dsimp only
    have hg := gauss_mul_c n i (by omega)
    rw [show i + (n - i) = n by omega]
    calc q ^ n * (cc n * (gaussian q n i * q ^ (p * i) * qFactorial q (n - i + p)))
        = q ^ n * (gaussian q n i * cc n * q ^ (p * i) * qFactorial q (n - i + p)) := by ring
      _ = _ := by rw [hg]; ring
  rw [hdiag, trunc_diag N
    (fun a b => q ^ (a + b) * (q ^ (p * a) * cc a * (qFactorial q (b + p) * cc b)))
    (fun a b hab => trunc_X_pow_mul N (a + b) hab _)]
  have hbox : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
      q ^ (a + b) * (q ^ (p * a) * cc a * (qFactorial q (b + p) * cc b))) =
      (∑ a ∈ Finset.range (N + 1), q ^ ((p + 1) * a) * cc a) *
        (∑ b ∈ Finset.range (N + 1), q ^ (1 * b) * (qFactorial q (b + p) * cc b)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show (p + 1) * a = a + p * a by ring, pow_add, pow_add, one_mul]
    ring
  rw [hbox, map_mul, trunc_eulerSum N (p + 1) (by omega), ← trunc_powerShiftSum N 1 one_pos,
    ← tser, ← map_mul, Nat.add_sub_cancel]

/-! ### Step 4: `U_m (q)_∞³` -/

/-- One term of the expanded `U_m`. -/
def t4 (m w j i k : ℕ) : PowerSeries ℤ :=
  q ^ w * cc w * gaussian q m j * gaussian q w i * q ^ ((m - j) * i) *
    (q ^ k * (cc k * rsy (w - i + (m - j)) k))

theorem t4_expand (m k w : ℕ) :
    q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m)) =
      ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (w + 1), t4 m w j i k := by
  rw [rogersSzego_add]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rsy_add]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [t4, pow_add]
  ring

theorem trunc_t4_sum (N m w j i : ℕ) :
    (∑ k ∈ Finset.range (N + 1), trunc N (t4 m w j i k)) =
      trunc N (q ^ w * cc w * gaussian q m j * gaussian q w i * q ^ ((m - j) * i) *
        (qFactorial q (w - i + (m - j)) * reciprocalEuler ^ 2)) := by
  rw [← map_sum]
  have : (∑ k ∈ Finset.range (N + 1), t4 m w j i k) =
      q ^ w * cc w * gaussian q m j * gaussian q w i * q ^ ((m - j) * i) *
        ∑ k ∈ Finset.range (N + 1), q ^ k * (cc k * rsy (w - i + (m - j)) k) := by
    rw [Finset.mul_sum]; rfl
  rw [this, map_mul, trunc_rsy_sum, ← map_mul]

theorem trunc_shiftedU_expand (N m : ℕ) :
    trunc N (shiftedU m) = trunc N (∑ j ∈ Finset.range (m + 1),
      gaussian q m j * (qFactorial q (m - j) * tser 1 (m - j)) * reciprocalEuler ^ 3) := by
  rw [trunc_shiftedU]
  have hA : (∑ k ∈ Finset.range (N + 1), ∑ w ∈ Finset.range (N + 1),
      q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m))) =
      ∑ w ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (w + 1),
        ∑ k ∈ Finset.range (N + 1), t4 m w j i k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl fun k _ => t4_expand m k w, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_comm
  have hD : (∑ w ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (m + 1),
      ∑ i ∈ Finset.range (w + 1),
        q ^ w * cc w * gaussian q m j * gaussian q w i * q ^ ((m - j) * i) *
          (qFactorial q (w - i + (m - j)) * reciprocalEuler ^ 2)) =
      ∑ j ∈ Finset.range (m + 1), gaussian q m j * reciprocalEuler ^ 2 *
        ∑ w ∈ Finset.range (N + 1), q ^ w * (cc w * ∑ i ∈ Finset.range (w + 1),
          gaussian q w i * q ^ ((m - j) * i) * qFactorial q (w - i + (m - j))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc trunc N (∑ k ∈ Finset.range (N + 1), ∑ w ∈ Finset.range (N + 1),
        q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m)))
      = ∑ w ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (w + 1),
          ∑ k ∈ Finset.range (N + 1), trunc N (t4 m w j i k) := by
        rw [hA]; simp only [map_sum]
    _ = ∑ w ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (w + 1),
          trunc N (q ^ w * cc w * gaussian q m j * gaussian q w i * q ^ ((m - j) * i) *
            (qFactorial q (w - i + (m - j)) * reciprocalEuler ^ 2)) := by
        simp only [trunc_t4_sum]
    _ = trunc N (∑ j ∈ Finset.range (m + 1), gaussian q m j * reciprocalEuler ^ 2 *
          ∑ w ∈ Finset.range (N + 1), q ^ w * (cc w * ∑ i ∈ Finset.range (w + 1),
            gaussian q w i * q ^ ((m - j) * i) * qFactorial q (w - i + (m - j)))) := by
        rw [← hD]; simp only [map_sum]
    _ = ∑ j ∈ Finset.range (m + 1), trunc N (gaussian q m j * reciprocalEuler ^ 2) *
          trunc N (qFactorial q (m - j) * reciprocalEuler * tser 1 (m - j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, trunc_wsum]
    _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← map_mul]
        congr 1
        ring

theorem shiftedU_eq_sum (m : ℕ) :
    shiftedU m = ∑ j ∈ Finset.range (m + 1),
      gaussian q m j * (qFactorial q (m - j) * tser 1 (m - j)) * reciprocalEuler ^ 3 :=
  eq_of_trunc _ _ fun N => trunc_shiftedU_expand N m

/-! ### Step 5: the shifted Mehler identity -/

/-- **`ShiftedMehler` holds**: `U_m (q)_∞³ (1 - q^{m+1}) = m + 1`. -/
theorem shiftedMehler : ShiftedMehler := by
  refine ⟨fun m => ?_⟩
  have he : (euler : PowerSeries ℤ) * reciprocalEuler = 1 := euler_mul_reciprocal
  have hterm : ∀ j ∈ Finset.range (m + 1),
      gaussian q m j * (qFactorial q (m - j) * tser 1 (m - j)) * reciprocalEuler ^ 3 *
        euler ^ 3 * (1 - q ^ (m + 1)) =
      gaussian q (m + 1) j * qFactorial q (m + 1 - 1 - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := gaussian_succ_mul m j (by omega)
    have h2 := tser_one_mul (m - j)
    rw [show m - j + 1 = m + 1 - j by omega] at h2
    rw [show m + 1 - 1 - j = m - j by omega]
    calc gaussian q m j * (qFactorial q (m - j) * tser 1 (m - j)) * reciprocalEuler ^ 3 *
          euler ^ 3 * (1 - q ^ (m + 1))
        = (gaussian q m j * (1 - q ^ (m + 1))) * qFactorial q (m - j) * tser 1 (m - j) *
            (euler * reciprocalEuler) ^ 3 := by ring
      _ = gaussian q (m + 1) j * qFactorial q (m - j) * (tser 1 (m - j) * (1 - q ^ (m + 1 - j))) := by
          rw [← h1, he]; ring
      _ = _ := by rw [h2, mul_one]
  rw [shiftedU_eq_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_congr rfl hterm,
    sum_gaussian_qFactorial]

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms tser_one_mul
#print axioms trunc_rsy_sum
#print axioms trunc_wsum
#print axioms shiftedU_eq_sum
#print axioms shiftedMehler
end AxiomAudit

namespace VOA.DeligneAudit.A2

/-- **The A₂ star identity rests only on `FourTriangular`.** -/
theorem starIdentity_of_fourTriangular (hT : FourTriangular) : StarIdentity :=
  starIdentity_of_mehler_triangular shiftedMehler hT

end VOA.DeligneAudit.A2

#print axioms VOA.DeligneAudit.A2.starIdentity_of_fourTriangular
