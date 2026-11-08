/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStatement
import VOA.Moonshine.MoonshineCNGammaZeroShimizu

/-!
# Hecke coset matching for the `Γ₁ ⇒ Γ₀` upgrade

Blueprint: the `Γ₀` upgrade argument of `Notes/moonshine/MOON_MONSTER.md`. Fix `M`, a prime
`p`, and integers `m, n` with
`m p - n M = 1`; put `σ = (m n; M p) ∈ Γ₀(M)` (`diamondLift`) and `L_M = (1 0; M 1)`.

* `diamondLift_mul_upperSL`: `σ T σ⁻¹ ∈ Γ₁(M)`, so `f ∘ σ` is `1`-periodic for a `Γ₁(M)`-invariant
  `f`.
* `heckeLevelSum_lowerSL`: the sum `S(τ) = Σ_{j<p} f((τ+j)/p) + f(σ(pτ))` satisfies
  `S(L_M τ) = S(τ)`. Three explicit matrix identities (`glUpperTri` for the Hecke matrices) and the
  Möbius bijection `j ↦ j / (1 + j M)` of `ℙ¹(𝔽_p)` (`heckeIndexMap`, `heckeIndexInv`).
* `diamond_sub_replicate_lowerUnipotent`: with the replication formula
  `Φ(f τ) = Σ_{j<p} f((τ+j)/p) + f′(pτ)`, the difference `ψ = f ∘ σ - f′` is invariant under
  `τ ↦ τ / ((M/p) τ + 1)`.
* `diamond_eq_replicate_add_const`: with Shimizu (`MoonshineCNGammaZeroShimizu`), `ψ` is constant
  when `0 < M < p`.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology CongruenceSubgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

/-! ### Integral and real matrices -/

/-- The element `(a b; c d)` of `SL(2, ℤ)`. -/
def slOfDetOne (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by rw [det_fin_two_of, h]⟩

@[simp] lemma slOfDetOne_coe (a b c d : ℤ) (h : a * d - b * c = 1) :
    ((slOfDetOne a b c d h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] :=
  rfl

@[simp] lemma mapGL_slOfDetOne_val (a b c d : ℤ) (h : a * d - b * c = 1) :
    ((mapGL ℝ (slOfDetOne a b c d h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(a : ℝ), b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma slOfDetOne_mem_Gamma1 {N : ℕ} {a b c d : ℤ} (h : a * d - b * c = 1)
    (ha : (a : ZMod N) = 1) (hd : (d : ZMod N) = 1) (hc : (c : ZMod N) = 0) :
    slOfDetOne a b c d h ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ha, hd, hc]

/-- `(1 k; 0 1) ∈ SL(2, ℤ)`. -/
def upperSL (k : ℤ) : SL(2, ℤ) := slOfDetOne 1 k 0 1 (by ring)

/-- `(1 0; M 1) ∈ SL(2, ℤ)`. -/
def lowerSL (M : ℕ) : SL(2, ℤ) := slOfDetOne 1 0 M 1 (by ring)

lemma upperSL_mem_Gamma1 (N : ℕ) (k : ℤ) : upperSL k ∈ Gamma1 N :=
  slOfDetOne_mem_Gamma1 _ (by simp) (by simp) (by simp)

lemma lowerSL_mem_Gamma1 (M : ℕ) : lowerSL M ∈ Gamma1 M :=
  slOfDetOne_mem_Gamma1 _ (by simp) (by simp) (by simp)

lemma mapGL_upperSL_one : mapGL ℝ (upperSL 1) = glUpperUnipotent 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSL, glUpperUnipotent]

/-- The diamond lift `σ = (m n; M p) ∈ Γ₀(M)`, for `m p - n M = 1`. -/
def diamondLift (M p : ℕ) (m n : ℤ) (h : m * p - n * M = 1) : SL(2, ℤ) :=
  slOfDetOne m n M p h

lemma diamondLift_mem_Gamma0 (M p : ℕ) (m n : ℤ) (h : m * p - n * M = 1) :
    diamondLift M p m n h ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [diamondLift]

/-- The upper-triangular `(a b; 0 d) ∈ GL(2, ℝ)`, `a d ≠ 0`. -/
noncomputable def glUpperTri (a b d : ℝ) (h : a * d ≠ 0) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by rwa [det_fin_two_of, mul_zero, sub_zero])

@[simp] lemma glUpperTri_val (a b d : ℝ) (h : a * d ≠ 0) :
    ((glUpperTri a b d h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] :=
  rfl

lemma coe_heckePoint (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((heckePoint a d b ha hd τ : ℍ) : ℂ) = (a * (τ : ℂ) + b) / d :=
  rfl

lemma natCast_mul_natCast_ne_zero {a d : ℕ} (ha : 0 < a) (hd : 0 < d) : (a : ℝ) * d ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne') (Nat.cast_ne_zero.mpr hd.ne')

lemma coe_glUpperTri_smul {a b d : ℝ} (h : a * d ≠ 0) (hpos : 0 < a * d) (τ : ℍ) :
    ((glUpperTri a b d h • τ : ℍ) : ℂ) = (a * τ + b) / d := by
  rw [coe_smul_of_det_pos (by
    rwa [GeneralLinearGroup.val_det_apply, glUpperTri_val, det_fin_two_of, mul_zero, sub_zero])]
  simp [num, denom]

lemma natCast_pos_ne_zero {p : ℕ} (hp : 0 < p) : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'

/-- The Hecke matrix `(1 j; 0 p)`, sending `τ` to `(τ + j) / p`. -/
noncomputable def heckeShiftGL (p j : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  glUpperTri 1 j p (by rw [one_mul]; exact natCast_pos_ne_zero hp)

/-- The Hecke matrix `(p 0; 0 1)`, sending `τ` to `p τ`. -/
noncomputable def heckeScaleGL (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  glUpperTri p 0 1 (by rw [mul_one]; exact natCast_pos_ne_zero hp)

@[simp] lemma heckeShiftGL_val (p j : ℕ) (hp : 0 < p) :
    ((heckeShiftGL p j hp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (j : ℝ); 0, p] :=
  rfl

@[simp] lemma heckeScaleGL_val (p : ℕ) (hp : 0 < p) :
    ((heckeScaleGL p hp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] :=
  rfl

/-- `(τ + j) / p = (1 j; 0 p) • τ`. -/
lemma heckePoint_shift_eq_smul {p : ℕ} (hp : 0 < p) (j : ℕ) (τ : ℍ) :
    heckePoint 1 p j one_pos hp τ = heckeShiftGL p j hp • τ := by
  ext1
  rw [coe_heckePoint, heckeShiftGL, coe_glUpperTri_smul _ (by
    rw [one_mul]; exact Nat.cast_pos.mpr hp)]
  push_cast
  ring

/-- `p τ = (p 0; 0 1) • τ`. -/
lemma heckePoint_scale_eq_smul {p : ℕ} (hp : 0 < p) (τ : ℍ) :
    heckePoint p 1 0 hp one_pos τ = heckeScaleGL p hp • τ := by
  ext1
  rw [coe_heckePoint, heckeScaleGL, coe_glUpperTri_smul _ (by
    rw [mul_one]; exact Nat.cast_pos.mpr hp)]
  push_cast
  ring

/-! ### `σ T σ⁻¹ ∈ Γ₁(M)` -/

/-- `σ T = γ σ` with `γ = (1 - m M, m²; -M², 1 + m M) ∈ Γ₁(M)`. -/
lemma diamondLift_mul_upperSL (M p : ℕ) (m n : ℤ) (h : m * p - n * M = 1) :
    diamondLift M p m n h * upperSL 1 =
      slOfDetOne (1 - m * M) (m ^ 2) (-((M : ℤ) ^ 2)) (1 + m * M) (by ring) *
        diamondLift M p m n h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [diamondLift, upperSL, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, coe_mul,
      slOfDetOne_coe, Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one, cons_val_zero,
      cons_val_one, Fin.sum_univ_two, mul_one, mul_zero, add_zero, neg_mul] <;>
    first
    | ring1
    | linear_combination m * h
    | linear_combination (-m) * h
    | linear_combination (M : ℤ) * h
    | linear_combination (-(M : ℤ)) * h

lemma conj_upperSL_mem_Gamma1 (M : ℕ) (m : ℤ) :
    slOfDetOne (1 - m * M) (m ^ 2) (-((M : ℤ) ^ 2)) (1 + m * M) (by ring) ∈ Gamma1 M :=
  slOfDetOne_mem_Gamma1 _ (by simp) (by simp) (by simp)

/-- A `Γ₁(M)`-invariant `f` composed with `σ` is `1`-periodic. -/
theorem diamond_periodic {f : ℍ → ℂ} {M p : ℕ} {m n : ℤ} (h : m * p - n * M = 1)
    (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ) (τ : ℍ) :
    f (mapGL ℝ (diamondLift M p m n h) • (glUpperUnipotent 1 • τ)) =
      f (mapGL ℝ (diamondLift M p m n h) • τ) := by
  rw [← mapGL_upperSL_one, ← mul_smul, ← map_mul, diamondLift_mul_upperSL, map_mul, mul_smul,
    hf _ (conj_upperSL_mem_Gamma1 M m)]

/-! ### Möbius arithmetic on `𝔽_p` -/

section MoebiusField

variable {K : Type*} [Field K] {u ν : K}

lemma one_add_mul_ne_zero_of_ne (h : ν * u = -1) {x : K} (hx : x ≠ ν) : 1 + x * u ≠ 0 := by
  intro h0
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  apply hx
  have : (x - ν) * u = 0 := by linear_combination h0 - h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hu)

lemma one_sub_mul_ne_zero_of_ne (h : ν * u = -1) {y : K} (hy : y ≠ -ν) : 1 - y * u ≠ 0 := by
  intro h0
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  apply hy
  have : (y + ν) * u = 0 := by linear_combination -h0 + h
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_right hu)

lemma moebius_ne_neg (h : ν * u = -1) {x : K} (hx : x ≠ ν) : x / (1 + x * u) ≠ -ν := by
  have h1 := one_add_mul_ne_zero_of_ne h hx
  intro he
  rw [div_eq_iff h1] at he
  have hν : ν = 0 := by linear_combination he - x * h
  rw [hν] at h
  simp at h

lemma moebiusInv_ne (h : ν * u = -1) {y : K} (hy : y ≠ -ν) : y / (1 - y * u) ≠ ν := by
  have h1 := one_sub_mul_ne_zero_of_ne h hy
  intro he
  rw [div_eq_iff h1] at he
  have hν : ν = 0 := by linear_combination -he + y * h
  rw [hν] at h
  simp at h

lemma moebiusInv_moebius (h : ν * u = -1) {x : K} (hx : x ≠ ν) :
    x / (1 + x * u) / (1 - x / (1 + x * u) * u) = x := by
  have h1 := one_add_mul_ne_zero_of_ne h hx
  have h2 : 1 - x / (1 + x * u) * u = 1 / (1 + x * u) := by
    field_simp
    ring
  rw [h2, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ h1]

lemma moebius_moebiusInv (h : ν * u = -1) {y : K} (hy : y ≠ -ν) :
    y / (1 - y * u) / (1 + y / (1 - y * u) * u) = y := by
  have h1 := one_sub_mul_ne_zero_of_ne h hy
  have h2 : 1 + y / (1 - y * u) * u = 1 / (1 - y * u) := by
    field_simp
    ring
  rw [h2, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ h1]

end MoebiusField

section IndexMaps

variable {p : ℕ} [Fact p.Prime] {M : ℕ}

/-- `j ↦ j′`, the representative in `[0, p)` of `j / (1 + j M) mod p`. -/
noncomputable def heckeIndexMap (p M : ℕ) [Fact p.Prime] (j : ℕ) : ℕ :=
  ((j : ZMod p) / (1 + (j : ZMod p) * (M : ZMod p))).val

/-- The inverse `j′ ↦ j′ / (1 - j′ M) mod p` of `heckeIndexMap`. -/
noncomputable def heckeIndexInv (p M : ℕ) [Fact p.Prime] (j : ℕ) : ℕ :=
  ((j : ZMod p) / (1 - (j : ZMod p) * (M : ZMod p))).val

lemma natCast_ne_of_mem_erase {j : ℕ} {ν : ZMod p} (hj : j ∈ (Finset.range p).erase ν.val) :
    (j : ZMod p) ≠ ν := by
  rw [Finset.mem_erase, Finset.mem_range] at hj
  intro h
  apply hj.1
  rw [← h, ZMod.val_natCast_of_lt hj.2]

omit [Fact p.Prime] in
lemma lt_of_mem_erase {j a : ℕ} (hj : j ∈ (Finset.range p).erase a) : j < p :=
  Finset.mem_range.mp (Finset.mem_of_mem_erase hj)

variable {ν : ZMod p} (hν : ν * (M : ZMod p) = -1)
include hν

lemma heckeIndexMap_mem {j : ℕ} (hj : j ∈ (Finset.range p).erase ν.val) :
    heckeIndexMap p M j ∈ (Finset.range p).erase (-ν).val := by
  have hx := natCast_ne_of_mem_erase hj
  rw [Finset.mem_erase, Finset.mem_range]
  exact ⟨fun he => moebius_ne_neg hν hx (ZMod.val_injective p he), ZMod.val_lt _⟩

lemma heckeIndexInv_mem {j : ℕ} (hj : j ∈ (Finset.range p).erase (-ν).val) :
    heckeIndexInv p M j ∈ (Finset.range p).erase ν.val := by
  have hy := natCast_ne_of_mem_erase hj
  rw [Finset.mem_erase, Finset.mem_range]
  exact ⟨fun he => moebiusInv_ne hν hy (ZMod.val_injective p he), ZMod.val_lt _⟩

lemma heckeIndexInv_map {j : ℕ} (hj : j ∈ (Finset.range p).erase ν.val) :
    heckeIndexInv p M (heckeIndexMap p M j) = j := by
  have hx := natCast_ne_of_mem_erase hj
  unfold heckeIndexInv heckeIndexMap
  rw [ZMod.natCast_zmod_val, moebiusInv_moebius hν hx, ZMod.val_natCast_of_lt (lt_of_mem_erase hj)]

lemma heckeIndexMap_inv {j : ℕ} (hj : j ∈ (Finset.range p).erase (-ν).val) :
    heckeIndexMap p M (heckeIndexInv p M j) = j := by
  have hy := natCast_ne_of_mem_erase hj
  unfold heckeIndexInv heckeIndexMap
  rw [ZMod.natCast_zmod_val, moebius_moebiusInv hν hy, ZMod.val_natCast_of_lt (lt_of_mem_erase hj)]

lemma heckeIndexMap_dvd {j : ℕ} (hj : j ∈ (Finset.range p).erase ν.val) :
    (p : ℤ) ∣ (j : ℤ) - (1 + (j : ℤ) * M) * (heckeIndexMap p M j : ℤ) := by
  have hx := natCast_ne_of_mem_erase hj
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  unfold heckeIndexMap
  rw [ZMod.natCast_zmod_val, mul_div_cancel₀ _ (one_add_mul_ne_zero_of_ne hν hx), sub_self]

end IndexMaps

/-! ### The three coset identities -/

section Cosets

variable {f : ℍ → ℂ} {M p : ℕ}

/-- **Generic coset.** `(1 j; 0 p) L_M = γ (1 j′; 0 p)` with
`γ = (1 + j M, e; p M, 1 - M j′) ∈ Γ₁(M)`, whenever `p e = j - (1 + j M) j′`. -/
lemma heckeShift_lowerSL (hp : 0 < p) (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ)
    {j j' : ℕ} {e : ℤ} (he : (p : ℤ) * e = j - (1 + j * M) * j') (τ : ℍ) :
    f (heckePoint 1 p j one_pos hp (mapGL ℝ (lowerSL M) • τ)) =
      f (heckePoint 1 p j' one_pos hp τ) := by
  have hdet : ((1 : ℤ) + j * M) * (1 - M * j') - e * (p * M) = 1 := by
    linear_combination (-(M : ℤ)) * he
  have hγ : slOfDetOne (1 + j * M) e (p * M) (1 - M * j') hdet ∈ Gamma1 M :=
    slOfDetOne_mem_Gamma1 _ (by simp) (by simp) (by simp)
  have heR : (p : ℝ) * e = j - (1 + j * M) * j' := by exact_mod_cast he
  have hmat : mapGL ℝ (slOfDetOne (1 + j * M) e (p * M) (1 - M * j') hdet) * heckeShiftGL p j' hp =
      heckeShiftGL p j hp * mapGL ℝ (lowerSL M) := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Units.val_mul,
        mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe, slOfDetOne_coe, RingHom.mapMatrix_apply,
        Int.coe_castRingHom, heckeShiftGL_val, Matrix.mul_apply, map_apply, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two, Int.cast_add, Int.cast_one,
        Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_zero, mul_one, mul_zero, add_zero,
        zero_add, lowerSL] <;>
      first
      | ring1
      | linear_combination heR
  rw [heckePoint_shift_eq_smul, heckePoint_shift_eq_smul, ← mul_smul, ← hmat, mul_smul, hf _ hγ]

/-- **Exceptional coset.** `(1 j₀; 0 p) L_M = T_k σ (p 0; 0 1)` when `j₀ = n + k p`. -/
lemma heckeShift_lowerSL_exceptional (hp : 0 < p) {m n : ℤ} (hmn : m * p - n * M = 1)
    (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ) {j₀ : ℕ} {k : ℤ}
    (hk : (j₀ : ℤ) = n + k * p) (τ : ℍ) :
    f (heckePoint 1 p j₀ one_pos hp (mapGL ℝ (lowerSL M) • τ)) =
      f (mapGL ℝ (diamondLift M p m n hmn) • heckePoint p 1 0 hp one_pos τ) := by
  have hkR : (j₀ : ℝ) = n + k * p := by exact_mod_cast hk
  have hmnR : (m : ℝ) * p - n * M = 1 := by exact_mod_cast hmn
  have hmat : heckeShiftGL p j₀ hp * mapGL ℝ (lowerSL M) =
      mapGL ℝ (upperSL k) * mapGL ℝ (diamondLift M p m n hmn) * heckeScaleGL p hp := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp only [lowerSL, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Units.val_mul,
        heckeShiftGL_val, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe, slOfDetOne_coe,
        RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.mul_apply, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_val_one, map_apply, Fin.sum_univ_two, Int.cast_one,
        Int.cast_zero, Int.cast_natCast, mul_one, mul_zero, zero_add, add_zero, zero_mul, one_mul,
        upperSL, diamondLift, heckeScaleGL_val] <;>
      first
      | ring1
      | linear_combination hkR
      | linear_combination -hkR
      | linear_combination (M : ℝ) * hkR - hmnR
  rw [heckePoint_shift_eq_smul, heckePoint_scale_eq_smul, ← mul_smul, hmat, mul_smul, mul_smul,
    hf _ (upperSL_mem_Gamma1 M k)]

/-- **Extra coset.** `σ (p 0; 0 1) L_M = γ* (1 j*; 0 p)` with
`γ* = (m p + n M, e; 2 M p, 1 - 2 M j*) ∈ Γ₁(M)`, whenever `p e = n - (m p + n M) j*`. -/
lemma diamondScale_lowerSL (hp : 0 < p) {m n : ℤ} (hmn : m * p - n * M = 1)
    (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ) {js : ℕ} {e : ℤ}
    (he : (p : ℤ) * e = n - (m * p + n * M) * js) (τ : ℍ) :
    f (mapGL ℝ (diamondLift M p m n hmn) • heckePoint p 1 0 hp one_pos (mapGL ℝ (lowerSL M) • τ)) =
      f (heckePoint 1 p js one_pos hp τ) := by
  have hdet : (m * p + n * M) * (1 - 2 * M * js) - e * (2 * M * p) = 1 := by
    linear_combination hmn - 2 * (M : ℤ) * he
  have hmM : (m : ZMod M) * p = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod M) hmn
    push_cast at this
    rwa [ZMod.natCast_self, mul_zero, sub_zero] at this
  have hγ : slOfDetOne (m * p + n * M) e (2 * M * p) (1 - 2 * M * js) hdet ∈ Gamma1 M :=
    slOfDetOne_mem_Gamma1 _ (by push_cast; rw [ZMod.natCast_self, mul_zero, add_zero, hmM])
      (by simp) (by simp)
  have heR : (p : ℝ) * e = n - (m * p + n * M) * js := by exact_mod_cast he
  have hmat : mapGL ℝ (diamondLift M p m n hmn) * heckeScaleGL p hp * mapGL ℝ (lowerSL M) =
      mapGL ℝ (slOfDetOne (m * p + n * M) e (2 * M * p) (1 - 2 * M * js) hdet) *
        heckeShiftGL p js hp := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp only [diamondLift, lowerSL, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
        Units.val_mul, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe, slOfDetOne_coe,
        RingHom.mapMatrix_apply, Int.coe_castRingHom, heckeScaleGL_val, Matrix.mul_apply, map_apply,
        of_apply, cons_val', cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two,
        mul_zero, add_zero, Int.cast_zero, Int.cast_one, mul_one, zero_add, Int.cast_natCast,
        heckeShiftGL_val, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sub] <;>
      first
      | ring1
      | linear_combination heR
      | linear_combination -heR
  rw [heckePoint_scale_eq_smul, heckePoint_shift_eq_smul, ← mul_smul, ← mul_smul, hmat, mul_smul,
    hf _ hγ]

end Cosets

/-! ### The level sum -/

/-- `S(τ) = Σ_{j<p} f((τ + j)/p) + f(σ(p τ))`. -/
noncomputable def heckeLevelSum (f : ℍ → ℂ) (σ : SL(2, ℤ)) (p : ℕ) (hp : 0 < p) (τ : ℍ) : ℂ :=
  ∑ j ∈ Finset.range p, f (heckePoint 1 p j one_pos hp τ) +
    f (mapGL ℝ σ • heckePoint p 1 0 hp one_pos τ)

/-- **Hecke coset matching.** For a `Γ₁(M)`-invariant `f`, a prime `p` and `m p - n M = 1`,
the level sum `S` is invariant under `L_M = (1 0; M 1)`. -/
theorem heckeLevelSum_lowerSL {f : ℍ → ℂ} {M p : ℕ} (hp : p.Prime) {m n : ℤ}
    (hmn : m * p - n * M = 1) (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ) (τ : ℍ) :
    heckeLevelSum f (diamondLift M p m n hmn) p hp.pos (mapGL ℝ (lowerSL M) • τ) =
      heckeLevelSum f (diamondLift M p m n hmn) p hp.pos τ := by
  haveI := Fact.mk hp
  have hν : (n : ZMod p) * (M : ZMod p) = -1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hmn
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, zero_sub] at this
    linear_combination -this
  have hj₀ : (n : ZMod p).val ∈ Finset.range p := Finset.mem_range.mpr (ZMod.val_lt _)
  have hjs : (-(n : ZMod p)).val ∈ Finset.range p := Finset.mem_range.mpr (ZMod.val_lt _)
  -- the exceptional index `j₀ ≡ n`
  have hk : (p : ℤ) ∣ ((n : ZMod p).val : ℤ) - n := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, sub_self]
  obtain ⟨k, hk⟩ := hk
  have hexc := heckeShift_lowerSL_exceptional (f := f) hp.pos hmn hf
    (j₀ := (n : ZMod p).val) (k := k) (by linear_combination hk) τ
  -- the extra index `j* ≡ -n`
  have he : (p : ℤ) ∣ n - (m * p + n * M) * ((-(n : ZMod p)).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, zero_add]
    linear_combination (n : ZMod p) * hν
  obtain ⟨e, he⟩ := he
  have hext := diamondScale_lowerSL (f := f) hp.pos hmn hf (js := (-(n : ZMod p)).val) (e := e)
    he.symm τ
  -- the bijection on the remaining indices
  have hbij : ∑ j ∈ (Finset.range p).erase (n : ZMod p).val,
      f (heckePoint 1 p j one_pos hp.pos (mapGL ℝ (lowerSL M) • τ)) =
      ∑ j ∈ (Finset.range p).erase (-(n : ZMod p)).val, f (heckePoint 1 p j one_pos hp.pos τ) := by
    refine Finset.sum_nbij' (heckeIndexMap p M) (heckeIndexInv p M)
      (fun j hj => heckeIndexMap_mem hν hj) (fun j hj => heckeIndexInv_mem hν hj)
      (fun j hj => heckeIndexInv_map hν hj) (fun j hj => heckeIndexMap_inv hν hj) ?_
    intro j hj
    obtain ⟨e', he'⟩ := heckeIndexMap_dvd hν hj
    exact heckeShift_lowerSL hp.pos hf (j := j) (j' := heckeIndexMap p M j) (e := e') he'.symm τ
  unfold heckeLevelSum
  rw [← Finset.add_sum_erase _ _ hj₀, ← Finset.add_sum_erase _ _ hjs, hexc, hext, hbij]
  ring

/-! ### The difference `f ∘ σ - f′` -/

/-- `p (L_M τ) = L_{M/p} (p τ)`. -/
lemma heckeScale_lowerSL {M p : ℕ} (hp : 0 < p) (τ : ℍ) :
    heckePoint p 1 0 hp one_pos (mapGL ℝ (lowerSL M) • τ) =
      glLowerUnipotent ((M : ℝ) / p) • heckePoint p 1 0 hp one_pos τ := by
  have hp' : (p : ℝ) ≠ 0 := natCast_pos_ne_zero hp
  have hmat : heckeScaleGL p hp * mapGL ℝ (lowerSL M) =
      glLowerUnipotent ((M : ℝ) / p) * heckeScaleGL p hp := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [lowerSL, glLowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [heckePoint_scale_eq_smul, heckePoint_scale_eq_smul, ← mul_smul, ← mul_smul, hmat]

lemma heckeScale_surjective {p : ℕ} (hp : 0 < p) (z : ℍ) :
    ∃ τ : ℍ, heckePoint p 1 0 hp one_pos τ = z := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨⟨(z : ℂ) / p, ?_⟩, ?_⟩
  · rw [Complex.div_natCast_im]
    exact div_pos z.im_pos hp'
  · ext1
    rw [coe_heckePoint]
    simp only [Nat.cast_one, Nat.cast_zero, add_zero, div_one]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp.ne')

/-- **`ψ = f ∘ σ - f′` is `L_{M/p}`-invariant**, given the replication formula at `p`
(with an arbitrary function `Φ` of `f` on the left). -/
theorem diamond_sub_replicate_lowerUnipotent {f f' : ℍ → ℂ} {Φ : ℂ → ℂ} {M p : ℕ}
    (hp : p.Prime) {m n : ℤ} (hmn : m * p - n * M = 1)
    (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ)
    (hrep : ∀ τ : ℍ, Φ (f τ) = ∑ j ∈ Finset.range p, f (heckePoint 1 p j one_pos hp.pos τ) +
      f' (heckePoint p 1 0 hp.pos one_pos τ)) (z : ℍ) :
    f (mapGL ℝ (diamondLift M p m n hmn) • (glLowerUnipotent ((M : ℝ) / p) • z)) -
        f' (glLowerUnipotent ((M : ℝ) / p) • z) =
      f (mapGL ℝ (diamondLift M p m n hmn) • z) - f' z := by
  obtain ⟨τ, rfl⟩ := heckeScale_surjective hp.pos z
  rw [← heckeScale_lowerSL hp.pos τ]
  have h1 := hrep (mapGL ℝ (lowerSL M) • τ)
  have h2 := hrep τ
  have h3 := heckeLevelSum_lowerSL hp hmn hf τ
  unfold heckeLevelSum at h3
  rw [hf _ (lowerSL_mem_Gamma1 M)] at h1
  linear_combination h3 + h1 - h2

/-- **The replicate differs from the diamond image by a constant** (`0 < M < p`, `p` prime):
`f (σ τ) = f′ τ + c`, given holomorphy, `Γ₁(M)`-invariance of `f`, `1`-periodicity of `f′`, and the
replication formula at `p`. -/
theorem diamond_eq_replicate_add_const {f f' : ℍ → ℂ} {Φ : ℂ → ℂ} {M p : ℕ} (hM : 0 < M)
    (hp : p.Prime) (hMp : M < p) {m n : ℤ} (hmn : m * p - n * M = 1)
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ)
    (hf'hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f')
    (hf'per : ∀ τ : ℍ, f' (glUpperUnipotent 1 • τ) = f' τ)
    (hrep : ∀ τ : ℍ, Φ (f τ) = ∑ j ∈ Finset.range p, f (heckePoint 1 p j one_pos hp.pos τ) +
      f' (heckePoint p 1 0 hp.pos one_pos τ)) :
    ∃ c : ℂ, ∀ τ : ℍ, f (mapGL ℝ (diamondLift M p m n hmn) • τ) = f' τ + c := by
  set σ := mapGL ℝ (diamondLift M p m n hmn)
  have hσ : 0 < σ.det.val := by simp [σ]
  have hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((f ∘ fun τ : ℍ => σ • τ) - f') :=
    MDifferentiable.sub (MDifferentiable.comp hfhol (mdifferentiable_smul hσ)) hf'hol
  have hy0 : (0 : ℝ) < (M : ℝ) / p := div_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hp.pos)
  have hy1 : (M : ℝ) / p < 1 := by
    rw [div_lt_one (Nat.cast_pos.mpr hp.pos)]
    exact_mod_cast hMp
  have hconst := eq_of_invariant_upper_lower_unipotent hψ hy0 hy1
    (fun τ => by
      simp only [Pi.sub_apply, Function.comp_apply]
      rw [diamond_periodic hmn hf, hf'per])
    (fun τ => by
      simp only [Pi.sub_apply, Function.comp_apply]
      exact diamond_sub_replicate_lowerUnipotent hp hmn hf hrep τ)
  refine ⟨f (σ • UpperHalfPlane.I) - f' UpperHalfPlane.I, fun τ => ?_⟩
  have := hconst τ UpperHalfPlane.I
  simp only [Pi.sub_apply, Function.comp_apply] at this
  linear_combination this

end VOA.Moonshine.ConwayNorton
