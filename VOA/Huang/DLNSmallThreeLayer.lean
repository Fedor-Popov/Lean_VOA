import VOA.Huang.DLNSmallThreeMatrices

/-!
# Named elements of the layer `SL₂(ℤ/3^{k+1}) → SL₂(ℤ/3^k)`

`x₃ = x(3)`, `y₃ = y(3)`, `t₄ = diag(4, 4⁻¹)` generate the level-one kernel `K₁`;
`n_e = x(3^k)`, `n_f = y(3^k)`, `n_h = t₄^{3^{k-1}} = diag(1+3^k, 1-3^k)` generate the layer `N`.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

section Elements

variable (k : ℕ)

/-- The unit `4` of `ℤ/3^{k+1}`. -/
noncomputable def fourU : (ZMod (3 ^ (k + 1)))ˣ :=
  ZMod.unitOfCoprime 4 (Nat.Coprime.pow_right _ (by norm_num))

/-- The unit `5` of `ℤ/3^{k+1}`. -/
noncomputable def fiveU : (ZMod (3 ^ (k + 1)))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))

/-- `x(3)`. -/
abbrev x3 : SLL k := upperRoot 3
/-- `y(3)`. -/
abbrev y3 : SLL k := lowerRoot 3
/-- `diag(4, 4⁻¹)`. -/
noncomputable abbrev t4 : SLL k := torus (fourU k)
/-- `x(3^k)`. -/
abbrev nE : SLL k := upperRoot ((3 : ZMod (3 ^ (k + 1))) ^ k)
/-- `y(3^k)`. -/
abbrev nF : SLL k := lowerRoot ((3 : ZMod (3 ^ (k + 1))) ^ k)
/-- `diag(4, 4⁻¹)^{3^{k-1}}`. -/
noncomputable abbrev nH : SLL k := torus (fourU k ^ (3 ^ (k - 1)))

variable {k}

@[simp] theorem fourU_val : ((fourU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) = 4 := by
  simp [fourU, ZMod.coe_unitOfCoprime]

@[simp] theorem fiveU_val : ((fiveU k : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) = 5 := by
  simp [fiveU, ZMod.coe_unitOfCoprime]

theorem fourU_pow_val (hk : 1 ≤ k) :
    (((fourU k ^ (3 ^ (k - 1)) : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1))) =
      1 + 3 ^ k := by
  rw [Units.val_pow_eq_pow_val, fourU_val]
  obtain ⟨w, hw⟩ := four_pow_three_pow (k - 1)
  have := congrArg (Int.cast : ℤ → ZMod (3 ^ (k + 1))) hw
  push_cast at this
  rw [this, show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega,
    three_pow_succ_eq_zero, zero_mul, add_zero]

theorem nH_eq_torus_val (hk : 1 ≤ k) :
    ((fourU k ^ (3 ^ (k - 1)) : (ZMod (3 ^ (k + 1)))ˣ) : ZMod (3 ^ (k + 1))) =
      1 + (3 : ZMod (3 ^ (k + 1))) ^ k := fourU_pow_val hk

theorem nH_eq_pow : nH k = t4 k ^ (3 ^ (k - 1)) := by
  rw [torus_pow]

/-! ### Membership -/

theorem upperRoot_three_mul_mem_levelOne (w : ZMod (3 ^ (k + 1))) :
    upperRoot (3 * w) ∈ levelOne k := by
  rw [mem_levelOne_iff]
  refine ⟨!![0, w; 0, 0], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperRoot]

theorem lowerRoot_three_mul_mem_levelOne (w : ZMod (3 ^ (k + 1))) :
    lowerRoot (3 * w) ∈ levelOne k := by
  rw [mem_levelOne_iff]
  refine ⟨!![0, 0; w, 0], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerRoot]

theorem x3_mem_levelOne : x3 k ∈ levelOne k := by
  simpa using upperRoot_three_mul_mem_levelOne (k := k) 1

theorem y3_mem_levelOne : y3 k ∈ levelOne k := by
  simpa using lowerRoot_three_mul_mem_levelOne (k := k) 1

theorem t4_mem_levelOne : t4 k ∈ levelOne k := by
  rw [mem_levelOne_iff]
  refine ⟨!![1, 0; 0, -((((fourU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1)))], ?_⟩
  have h : ((((fourU k)⁻¹ : (ZMod (3 ^ (k + 1)))ˣ)) : ZMod (3 ^ (k + 1))) * 4 = 1 := by
    rw [← fourU_val (k := k)]; simp
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus]
  · norm_num
  · linear_combination h

theorem upperRoot_pow_mul_mem_layerN (w : ZMod (3 ^ (k + 1))) :
    upperRoot ((3 : ZMod (3 ^ (k + 1))) ^ k * w) ∈ layerN k := by
  rw [mem_layerN_iff]
  refine ⟨!![0, w; 0, 0], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [upperRoot]

theorem lowerRoot_pow_mul_mem_layerN (w : ZMod (3 ^ (k + 1))) :
    lowerRoot ((3 : ZMod (3 ^ (k + 1))) ^ k * w) ∈ layerN k := by
  rw [mem_layerN_iff]
  refine ⟨!![0, 0; w, 0], ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerRoot]

theorem nE_mem_layerN : nE k ∈ layerN k := by
  simpa using upperRoot_pow_mul_mem_layerN (k := k) 1

theorem nF_mem_layerN : nF k ∈ layerN k := by
  simpa using lowerRoot_pow_mul_mem_layerN (k := k) 1

theorem nH_mem_layerN (hk : 1 ≤ k) : nH k ∈ layerN k := by
  rw [mem_layerN_iff]
  refine ⟨!![1, 0; 0, -1], ?_⟩
  have hv := nH_eq_torus_val hk
  have hiv := inv_val_of_sq_zero _ (three_pow_mul_self hk) _ hv
  ext i j; fin_cases i <;> fin_cases j <;> simp [torus, hv, hiv]
  ring

end Elements

end VOA.Huang.DLNSchur
