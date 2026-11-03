import VOA.Huang.DLNLiftingReduction
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Congruence of all modular-group characters

The abelianization of the integral modular group kills `Γ(12)`. We prove this
using two small residue calculations, modulo 3 and modulo 4, and generation
by `S,T`. The finite calculations use kernel-checked `decide`.

This proves the level-one case of the relative-commutator containment; it
does not assert that the containment holds at arbitrary levels.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN CongruenceSubgroup Matrix

private def weight3 (a b c d : ZMod 3) : ZMod 3 :=
  if c = 0 then a * b else (a + d) * c

private def weight4 (a b c d : ZMod 4) : ZMod 4 :=
  if c = 1 ∨ c = 3 then (a + d + 1) * c else (b - c + 1) * a - 1

private theorem weight3_S : ∀ a b c d : ZMod 3, a * d - b * c = 1 →
    weight3 (-c) (-d) a b = weight3 a b c d := by decide

private theorem weight3_T : ∀ a b c d : ZMod 3, a * d - b * c = 1 →
    weight3 (a + c) (b + d) c d = 1 + weight3 a b c d := by decide

private theorem weight4_S : ∀ a b c d : ZMod 4, a * d - b * c = 1 →
    weight4 (-c) (-d) a b = 1 + weight4 a b c d := by decide

private theorem weight4_T : ∀ a b c d : ZMod 4, a * d - b * c = 1 →
    weight4 (a + c) (b + d) c d = 1 + weight4 a b c d := by decide

private def residue3 (γ : SL2Z) : ZMod 3 :=
  weight3 (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

private def residue4 (γ : SL2Z) : ZMod 4 :=
  weight4 (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

private theorem det_mod (γ : SL2Z) (n : ℕ) :
    (γ 0 0 : ZMod n) * (γ 1 1 : ZMod n) -
      (γ 0 1 : ZMod n) * (γ 1 0 : ZMod n) = 1 := by
  have h : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  simpa only [Int.cast_mul, Int.cast_sub, Int.cast_one] using
    congrArg (fun z : ℤ => (z : ZMod n)) h

private theorem residue3_S (γ : SL2Z) : residue3 (ModularGroup.S * γ) = residue3 γ := by
  simpa [residue3, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two] using
    weight3_S _ _ _ _ (det_mod γ 3)

private theorem residue3_T (γ : SL2Z) :
    residue3 (ModularGroup.T * γ) = 1 + residue3 γ := by
  simpa [residue3, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two] using
    weight3_T _ _ _ _ (det_mod γ 3)

private theorem residue4_S (γ : SL2Z) :
    residue4 (ModularGroup.S * γ) = 1 + residue4 γ := by
  simpa [residue4, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two] using
    weight4_S _ _ _ _ (det_mod γ 4)

private theorem residue4_T (γ : SL2Z) :
    residue4 (ModularGroup.T * γ) = 1 + residue4 γ := by
  simpa [residue4, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two] using
    weight4_T _ _ _ _ (det_mod γ 4)

private theorem ST_cube : (ModularGroup.S * ModularGroup.T) ^ 3 = ModularGroup.S ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem character_S_mul_T_cube {A : Type*} [CommGroup A] (χ : SL2Z →* A) :
    χ ModularGroup.S * χ ModularGroup.T ^ 3 = 1 := by
  have h := congrArg χ ST_cube
  simp only [map_pow, map_mul, mul_pow] at h
  apply mul_left_cancel (a := χ ModularGroup.S ^ 2)
  calc
    χ ModularGroup.S ^ 2 * (χ ModularGroup.S * χ ModularGroup.T ^ 3) =
        χ ModularGroup.S ^ 3 * χ ModularGroup.T ^ 3 := by rw [← mul_assoc, ← pow_succ]
    _ = χ ModularGroup.S ^ 2 * 1 := by simpa using h

private theorem character_S_four {A : Type*} [CommGroup A] (χ : SL2Z →* A) :
    χ ModularGroup.S ^ 4 = 1 := by
  rw [← map_pow]
  have h : ModularGroup.S ^ 4 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h, map_one]

private theorem character_S_cube {A : Type*} [CommGroup A] (χ : SL2Z →* A) :
    χ ModularGroup.S ^ 3 = χ ModularGroup.T ^ 3 := by
  have h := congrArg (fun x : A => x ^ 3) (character_S_mul_T_cube χ)
  have he : χ ModularGroup.S ^ 3 * χ ModularGroup.T ^ 9 =
      χ ModularGroup.T ^ 3 * χ ModularGroup.T ^ 9 := by
    calc
      χ ModularGroup.S ^ 3 * χ ModularGroup.T ^ 9 = 1 := by
        simpa only [mul_pow, ← pow_mul, one_pow] using h
      _ = _ := by rw [← pow_add]; exact (character_pow_twelve χ ModularGroup.T).symm
  exact mul_right_cancel he

private theorem pow_residue_succ {A : Type*} [Group A] {n : ℕ} [NeZero n] [Fact (1 < n)]
    (x : A) (hx : x ^ n = 1) (a : ZMod n) :
    x ^ (1 + a).val = x * x ^ a.val := by
  rw [ZMod.val_add, ZMod.val_one, ← pow_eq_pow_mod _ hx, pow_add, pow_one]

private theorem induction_ST (P : SL2Z → Prop) (h1 : P 1)
    (hS : ∀ γ, P γ → P (ModularGroup.S * γ))
    (hT : ∀ γ, P γ → P (ModularGroup.T * γ)) (γ : SL2Z) : P γ := by
  induction γ using (FixedDetMatrices.induction_on one_ne_zero) with
  | h0 γ h10 h00 _ h01 =>
    rw [FixedDetMatrices.reps_one_id γ h10 h00 h01]
    exact h1
  | hS γ ih => exact hS γ ih
  | hT γ ih => exact hT γ ih

/-- The fourth power of a character is determined by reduction modulo 3. -/
private theorem character_four_residue {A : Type*} [CommGroup A] (χ : SL2Z →* A) (γ : SL2Z) :
    χ γ ^ 4 = (χ ModularGroup.T ^ 4) ^ (residue3 γ).val := by
  have ht : (χ ModularGroup.T ^ 4) ^ 3 = 1 := by
    simpa only [← pow_mul] using character_pow_twelve χ ModularGroup.T
  induction γ using induction_ST with
  | h1 =>
    simp [residue3, weight3]
  | hS γ ih =>
    change χ (ModularGroup.S * (γ : SL2Z)) ^ 4 = _
    rw [residue3_S, map_mul, mul_pow, character_S_four, one_mul, ih]
  | hT γ ih =>
    change χ (ModularGroup.T * (γ : SL2Z)) ^ 4 = _
    rw [residue3_T, map_mul, mul_pow, ih, pow_residue_succ _ ht]

/-- The cube of a character is determined by reduction modulo 4. -/
private theorem character_cube_residue {A : Type*} [CommGroup A] (χ : SL2Z →* A) (γ : SL2Z) :
    χ γ ^ 3 = (χ ModularGroup.T ^ 3) ^ (residue4 γ).val := by
  letI : Fact (1 < 4) := ⟨by decide⟩
  have ht : (χ ModularGroup.T ^ 3) ^ 4 = 1 := by
    simpa only [← pow_mul] using character_pow_twelve χ ModularGroup.T
  induction γ using induction_ST with
  | h1 =>
    simp [residue4, weight4]
  | hS γ ih =>
    change χ (ModularGroup.S * (γ : SL2Z)) ^ 3 = _
    rw [residue4_S, map_mul, mul_pow, character_S_cube, ih, pow_residue_succ _ ht]
  | hT γ ih =>
    change χ (ModularGroup.T * (γ : SL2Z)) ^ 3 = _
    rw [residue4_T, map_mul, mul_pow, ih, pow_residue_succ _ ht]

/-- Characters on `Γ(3)` have fourth power one. -/
theorem character_four_eq_one_of_mem_gamma_three {A : Type*} [CommGroup A]
    (χ : SL2Z →* A) {γ : SL2Z} (hγ : γ ∈ Gamma 3) : χ γ ^ 4 = 1 := by
  rw [character_four_residue]
  obtain ⟨ha, hb, hc, _⟩ := Gamma_mem.mp hγ
  simp [residue3, weight3, ha, hb, hc]

/-- Characters on `Γ(4)` have cube one. -/
theorem character_cube_eq_one_of_mem_gamma_four {A : Type*} [CommGroup A]
    (χ : SL2Z →* A) {γ : SL2Z} (hγ : γ ∈ Gamma 4) : χ γ ^ 3 = 1 := by
  rw [character_cube_residue]
  obtain ⟨ha, hb, hc, _⟩ := Gamma_mem.mp hγ
  simp [residue4, weight4, ha, hb, hc]

/-- Every homomorphism to a commutative group kills the principal subgroup `Γ(12)`. -/
theorem character_eq_one_of_mem_gamma_twelve {A : Type*} [CommGroup A]
    (χ : SL2Z →* A) {γ : SL2Z} (hγ : γ ∈ Gamma 12) : χ γ = 1 := by
  have h4 := character_four_eq_one_of_mem_gamma_three χ
    (gamma_le_of_dvd (by norm_num : 3 ∣ 12) hγ)
  have h3 := character_cube_eq_one_of_mem_gamma_four χ
    (gamma_le_of_dvd (by norm_num : 4 ∣ 12) hγ)
  simpa only [show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul] using h4

/-- The commutator subgroup of the integral modular group contains `Γ(12)`. -/
theorem gamma_twelve_le_commutator : Gamma 12 ≤ commutator SL2Z := by
  rw [← Abelianization.ker_of]
  intro γ hγ
  exact character_eq_one_of_mem_gamma_twelve Abelianization.of hγ

/-- The exact level-one case of the arithmetic relative-commutator contract. -/
theorem relativeCommutatorCongruence_one :
    Gamma (12 * 1) ≤ ⁅(⊤ : Subgroup SL2Z), Gamma 1⁆ := by
  simpa only [Nat.mul_one, Gamma_one_top, ← commutator_def] using
    gamma_twelve_le_commutator

/-- A representation which is scalar on the entire modular group kills `Γ(12)`. -/
theorem matrixDLNLifting_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) (hp : DLNBridge.MatrixProjectiveCongruence ρ 1) :
    KernelContainsGamma ρ 12 := by
  intro γ hγ
  have h := relativeCommutator_le_ker ρ hp (relativeCommutatorCongruence_one hγ)
  exact congrArg (fun a : (Matrix κ κ ℂ)ˣ => (a : Matrix κ κ ℂ)) h

end VOA.Huang.DLNLifting
