import VOA.Huang.DLNSmallPairing
import VOA.Huang.DLNSchur3Gauss

/-!
# Matrix facts for the layer `SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k)`

Throughout `k ≥ 1`, `R = ℤ/3^{k+1}`, `q = 3^k`, so `q² = 0` and `3q = 0`.

* kernels of reduction are `{1 + m • W}`;
* the layer `N = ker(R → ℤ/3^k)` has exponent 3 and commutes with `K₁ = ker(R → ℤ/3)`;
* generators of `N` and of `K₁`;
* the conjugation identities used by the pairing argument;
* the quaternion average kills `N`.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-! ## Kernels of reduction -/

theorem castHom_eq_zero_iff_exists {n m : ℕ} [NeZero n] (h : m ∣ n) (r : ZMod n) :
    ZMod.castHom h (ZMod m) r = 0 ↔ ∃ w : ZMod n, r = (m : ZMod n) * w := by
  constructor
  · intro hr
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hr
    obtain ⟨c, hc⟩ := hr
    refine ⟨(c : ZMod n), ?_⟩
    rw [← ZMod.natCast_zmod_val r, hc]
    push_cast; rfl
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem reductionMod_apply_entry {n m : ℕ} (h : m ∣ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) (i j : Fin 2) :
    (reductionMod n m h g : Matrix (Fin 2) (Fin 2) (ZMod m)) i j =
      ZMod.castHom h (ZMod m) (g i j) := rfl

/-- Elements of the kernel of reduction modulo `m` are exactly `1 + m • W`. -/
theorem mem_ker_reductionMod_iff {n m : ℕ} [NeZero n] (h : m ∣ n)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) :
    g ∈ (reductionMod n m h).ker ↔
      ∃ W : Matrix (Fin 2) (Fin 2) (ZMod n),
        (g : Matrix (Fin 2) (Fin 2) (ZMod n)) = 1 + (m : ZMod n) • W := by
  have h1 : ∀ i j, ZMod.castHom h (ZMod m) ((1 : Matrix (Fin 2) (Fin 2) (ZMod n)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod m)) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hent : ∀ i j, ∃ w : ZMod n,
        g i j - (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) i j = (m : ZMod n) * w := by
      intro i j
      apply (castHom_eq_zero_iff_exists h _).mp
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod m) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod m)) i j) hg
      simp only [reductionMod_apply_entry, Matrix.SpecialLinearGroup.coe_one] at this
      rw [map_sub, this, h1, sub_self]
    choose W hW using hent
    refine ⟨Matrix.of W, ?_⟩
    ext i j
    have := hW i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  · rintro ⟨W, hW⟩
    ext i j
    rw [reductionMod_apply_entry]
    change ZMod.castHom h (ZMod m) ((g : Matrix (Fin 2) (Fin 2) (ZMod n)) i j) = _
    rw [hW]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_natCast, ZMod.natCast_self, zero_mul, add_zero, Matrix.SpecialLinearGroup.coe_one]
    exact h1 i j

/-! ## Arithmetic in `ℤ/3^{k+1}` -/

theorem three_pow_succ_eq_zero (k : ℕ) : (3 : ZMod (3 ^ (k + 1))) ^ (k + 1) = 0 := by
  have : ((3 ^ (k + 1) : ℕ) : ZMod (3 ^ (k + 1))) = 0 := ZMod.natCast_self _
  exact_mod_cast this

theorem three_pow_mul_three (k : ℕ) : (3 : ZMod (3 ^ (k + 1))) ^ k * 3 = 0 := by
  rw [← pow_succ]; exact three_pow_succ_eq_zero k

theorem three_mul_three_pow (k : ℕ) : (3 : ZMod (3 ^ (k + 1))) * 3 ^ k = 0 := by
  rw [mul_comm]; exact three_pow_mul_three k

theorem three_pow_mul_self {k : ℕ} (hk : 1 ≤ k) :
    (3 : ZMod (3 ^ (k + 1))) ^ k * 3 ^ k = 0 := by
  have : (3 : ZMod (3 ^ (k + 1))) ^ k * 3 ^ k = 3 ^ (k + 1) * 3 ^ (k - 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [this, three_pow_succ_eq_zero, zero_mul]

/-! ## Matrices of the form `1 + q • W` -/

section OneAdd

variable {R : Type*} [CommRing R]

theorem one_add_smul_mul_one_add_smul (q q' : R) (W W' : Matrix (Fin 2) (Fin 2) R) :
    (1 + q • W) * (1 + q' • W') = 1 + q • W + q' • W' + (q * q') • (W * W') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  abel

theorem one_add_smul_pow_three (q : R) (hq2 : q * q = 0) (hq3 : 3 * q = 0)
    (W : Matrix (Fin 2) (Fin 2) R) : (1 + q • W) ^ 3 = 1 := by
  rw [pow_succ, pow_two, one_add_smul_mul_one_add_smul, hq2, zero_smul, add_zero,
    add_assoc, ← smul_add, one_add_smul_mul_one_add_smul, hq2, zero_smul, add_zero,
    add_assoc, ← smul_add]
  have : W + W + W = (3 : R) • W := by
    rw [show (3 : R) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [this, smul_smul, mul_comm, hq3, zero_smul, add_zero]

theorem inv_val_of_sq_zero (q : R) (hq : q * q = 0) (a : Rˣ) (ha : (a : R) = 1 + q) :
    ((a⁻¹ : Rˣ) : R) = 1 - q := by
  have h : ((a⁻¹ : Rˣ) : R) * (a : R) = 1 := by simp
  calc ((a⁻¹ : Rˣ) : R) = ((a⁻¹ : Rˣ) : R) * ((a : R) * (1 - q)) := by
        rw [ha]; ring_nf; rw [sq, hq]; ring
    _ = 1 - q := by rw [← mul_assoc, h, one_mul]

theorem layer_conj_upper_lower (q : R) (hq : q * q = 0) (a : Rˣ) (ha : (a : R) = 1 + q) :
    upperRoot 1 * lowerRoot q * (upperRoot 1)⁻¹ = (upperRoot q)⁻¹ * lowerRoot q * torus a := by
  have hai := inv_val_of_sq_zero q hq a ha
  have hq2 : q ^ 2 = 0 := by rw [sq]; exact hq
  have hq3 : q ^ 3 = 0 := by rw [pow_succ, hq2, zero_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, lowerRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha, hai] <;>
    ring_nf <;> simp [hq2, hq3]

theorem layer_conj_upper_torus (q : R) (hq : q * q = 0) (h3 : 3 * q = 0) (a : Rˣ)
    (ha : (a : R) = 1 + q) :
    upperRoot 1 * torus a * (upperRoot 1)⁻¹ = upperRoot q * torus a := by
  have hai := inv_val_of_sq_zero q hq a ha
  have hq2 : q ^ 2 = 0 := by rw [sq]; exact hq
  have hq3 : q ^ 3 = 0 := by rw [pow_succ, hq2, zero_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha, hai] <;>
    ring_nf <;> (try simp [hq2, hq3]) <;>
    (first | linear_combination h3 | linear_combination (-1) * h3 | linear_combination 2 * h3 |
      linear_combination (-2) * h3 | linear_combination 3 * h3 | linear_combination (-3) * h3)

theorem layer_conj_lower_upper (q : R) (hq : q * q = 0) (a : Rˣ) (ha : (a : R) = 1 + q) :
    lowerRoot 1 * upperRoot q * (lowerRoot 1)⁻¹ =
      upperRoot q * (lowerRoot q)⁻¹ * (torus a)⁻¹ := by
  have hai := inv_val_of_sq_zero q hq a ha
  have hq2 : q ^ 2 = 0 := by rw [sq]; exact hq
  have hq3 : q ^ 3 = 0 := by rw [pow_succ, hq2, zero_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, lowerRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha, hai] <;>
    ring_nf <;> simp [hq2, hq3]

theorem layer_conj_lower_torus (q : R) (hq : q * q = 0) (h3 : 3 * q = 0) (a : Rˣ)
    (ha : (a : R) = 1 + q) :
    lowerRoot 1 * torus a * (lowerRoot 1)⁻¹ = (lowerRoot q)⁻¹ * torus a := by
  have hai := inv_val_of_sq_zero q hq a ha
  have hq2 : q ^ 2 = 0 := by rw [sq]; exact hq
  have hq3 : q ^ 3 = 0 := by rw [pow_succ, hq2, zero_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha, hai] <;>
    ring_nf <;> (try simp [hq2, hq3]) <;>
    (first | linear_combination h3 | linear_combination (-1) * h3 | linear_combination 2 * h3 |
      linear_combination (-2) * h3 | linear_combination 3 * h3 | linear_combination (-3) * h3)

theorem conj_upper_one_torus (b : Rˣ) :
    upperRoot 1 * torus b * (upperRoot 1)⁻¹ =
      torus b * upperRoot (((b⁻¹ : Rˣ) : R) ^ 2 - 1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;> ring_nf <;>
    simp [pow_two, ← mul_assoc]

theorem conj_lower_one_torus (b : Rˣ) :
    lowerRoot 1 * torus b * (lowerRoot 1)⁻¹ = torus b * lowerRoot ((b : R) ^ 2 - 1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, torus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;> ring_nf <;>
    simp [pow_two, ← mul_assoc]

theorem upperRoot_conj_upperRoot (s t : R) :
    upperRoot s * upperRoot t * (upperRoot s)⁻¹ = upperRoot t := by
  rw [← upperRoot_neg, ← upperRoot_add, ← upperRoot_add]; congr 1; ring

theorem lowerRoot_conj_lowerRoot (s t : R) :
    lowerRoot s * lowerRoot t * (lowerRoot s)⁻¹ = lowerRoot t := by
  rw [← lowerRoot_neg, ← lowerRoot_add, ← lowerRoot_add]; congr 1; ring

/-- A torus element with `b = 1 + c d` is a product of four root elements. -/
theorem torus_eq_four_roots (b : Rˣ) (c d : R) (hb : (b : R) = 1 + c * d) :
    torus b = upperRoot c * lowerRoot d * upperRoot (-c * ((b⁻¹ : Rˣ) : R)) *
      lowerRoot (-d * (b : R)) := by
  have hbi : ((b⁻¹ : Rˣ) : R) * (b : R) = 1 := by simp
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upperRoot, lowerRoot, torus, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination hbi - ((b⁻¹ : Rˣ) : R) * hb
    | linear_combination c * (hbi - ((b⁻¹ : Rˣ) : R) * hb)
    | linear_combination d * hb - c * d ^ 2 * hbi
    | linear_combination (1 + (b : R) * c * d * ((b⁻¹ : Rˣ) : R)) * hb - (b : R) * c * d * hbi

end OneAdd

/-! ## Powers of four -/

/-- `4^(3^j) ≡ 1 + 3^(j+1) (mod 3^(j+2))`. -/
theorem four_pow_three_pow (j : ℕ) :
    ∃ w : ℤ, (4 : ℤ) ^ (3 ^ j) = 1 + 3 ^ (j + 1) + 3 ^ (j + 2) * w := by
  induction j with
  | zero => exact ⟨0, by norm_num⟩
  | succ j ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w + 3 ^ j * (1 + 3 * w) ^ 2 + 3 ^ (2 * j) * (1 + 3 * w) ^ 3, ?_⟩
    rw [pow_succ 3 j, pow_mul, hw]
    ring

theorem torus_pow {R : Type*} [CommRing R] (b : Rˣ) (m : ℕ) : torus b ^ m = torus (b ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, ← torus_mul, pow_succ]

/-! ## The layer and the level-one kernel -/

section Layer

variable (k : ℕ)

/-- `SL₂(ℤ/3^{k+1})`. -/
abbrev SLL := Matrix.SpecialLinearGroup (Fin 2) (ZMod (3 ^ (k + 1)))

/-- Reduction `SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k)`. -/
noncomputable abbrev rhoTop : SLL k →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (3 ^ k)) :=
  reductionMod (3 ^ (k + 1)) (3 ^ k) (pow_dvd_pow 3 (Nat.le_succ k))

/-- Reduction `SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3)`. -/
noncomputable abbrev rhoOne : SLL k →* SLThree :=
  reductionMod (3 ^ (k + 1)) 3 (dvd_pow_self 3 (Nat.succ_ne_zero k))

/-- The top layer `N = ker(SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k))`. -/
noncomputable abbrev layerN : Subgroup (SLL k) := (rhoTop k).ker

/-- The level-one congruence kernel `K₁ = ker(SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3))`. -/
noncomputable abbrev levelOne : Subgroup (SLL k) := (rhoOne k).ker

variable {k}

theorem mem_layerN_iff (n : SLL k) :
    n ∈ layerN k ↔ ∃ W : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1))),
      (n : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) = 1 + (3 : ZMod (3 ^ (k + 1))) ^ k • W := by
  rw [mem_ker_reductionMod_iff]
  push_cast
  rfl

theorem mem_levelOne_iff (g : SLL k) :
    g ∈ levelOne k ↔ ∃ V : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1))),
      (g : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) = 1 + (3 : ZMod (3 ^ (k + 1))) • V := by
  rw [mem_ker_reductionMod_iff]
  push_cast
  rfl

theorem layerN_le_levelOne (hk : 1 ≤ k) : layerN k ≤ levelOne k := by
  intro n hn
  obtain ⟨W, hW⟩ := (mem_layerN_iff n).mp hn
  refine (mem_levelOne_iff n).mpr ⟨(3 : ZMod (3 ^ (k + 1))) ^ (k - 1) • W, ?_⟩
  rw [hW, smul_smul, ← pow_succ']
  congr 3; omega

theorem layerN_pow_three (hk : 1 ≤ k) {n : SLL k} (hn : n ∈ layerN k) : n ^ 3 = 1 := by
  obtain ⟨W, hW⟩ := (mem_layerN_iff n).mp hn
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hW, Matrix.SpecialLinearGroup.coe_one]
  exact one_add_smul_pow_three _ (three_pow_mul_self hk) (three_mul_three_pow k) W

theorem levelOne_commute_layerN {g n : SLL k} (hg : g ∈ levelOne k) (hn : n ∈ layerN k) :
    Commute g n := by
  obtain ⟨V, hV⟩ := (mem_levelOne_iff g).mp hg
  obtain ⟨W, hW⟩ := (mem_layerN_iff n).mp hn
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) * n = n * g
  rw [hV, hW, one_add_smul_mul_one_add_smul, one_add_smul_mul_one_add_smul,
    three_mul_three_pow, three_pow_mul_three, zero_smul, zero_smul]
  abel

end Layer

end VOA.Huang.DLNSchur
