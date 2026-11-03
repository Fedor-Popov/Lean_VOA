/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Lattice.Defs
import VOA.LatticesAndCodes.Codes.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The lattice attached to a binary code

Ebeling §1.3 attaches to a binary code `C ⊆ 𝔽₂ⁿ` with `C ⊆ Cᗮ` the lattice
`Γ_C = (1/√2) ρ⁻¹(C) ⊆ ℝⁿ`, where `ρ : ℤⁿ → 𝔽₂ⁿ` is reduction mod `2`.

Following decision **D2** of `BLUEPRINT.md` the `1/√2` is put into the *form* rather than into
the vectors: the carrier is the honest integral module `ρ⁻¹(C) ⊆ ℤⁿ` and the form is
`⟪x, y⟫ = (∑ᵢ xᵢyᵢ)/2`, which takes integer values exactly because `C ⊆ Cᗮ`. The result is
isometric to Ebeling's `Γ_C` and never leaves `ℤ`.

## Main results

* `latticeOfCode` — the lattice `Γ_C`.
* `latticeOfCode_isPosDef` — `Γ_C` is positive definite.
* `latticeOfCode_rank` — `Γ_C` has rank `n`.
* `latticeOfCode_isEven` — **Ebeling, Prop. 1.3**: `Γ_C` is even iff `C` is doubly even.
* `latticeOfCode_det` — **Ebeling, Prop. 1.4**: `det Γ_C = 2 ^ (n - 2k)`.
* `latticeOfCode_isUnimodular` — **Ebeling, Prop. 1.4**: `Γ_C` is unimodular iff `C` is self-dual.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §1.3, Propositions 1.3 and 1.4.
-/

open scoped Matrix
open Module (Basis finrank finBasis)

/-! ### Reduction mod `q` -/

/-- Coordinatewise reduction `ℤⁿ → (ZMod q)ⁿ`, Ebeling's `ρ`. -/
def reduceMod (q n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod q) where
  toFun x := fun i => ((x i : ℤ) : ZMod q)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul]

@[simp] theorem reduceMod_apply (q n : ℕ) (x : Fin n → ℤ) (i : Fin n) :
    reduceMod q n x i = ((x i : ℤ) : ZMod q) := rfl

theorem reduceMod_surjective (q n : ℕ) [NeZero q] :
    Function.Surjective (reduceMod q n) := by
  intro y
  refine ⟨fun i => ((y i).val : ℤ), ?_⟩
  funext i
  simp [ZMod.natCast_val, ZMod.cast_id]

theorem intCast_dotProduct (q n : ℕ) (x y : Fin n → ℤ) :
    (((x ⬝ᵥ y : ℤ)) : ZMod q) = (reduceMod q n x) ⬝ᵥ (reduceMod q n y) := by
  simp only [dotProduct, reduceMod_apply, Int.cast_sum, Int.cast_mul]

/-! ### The integral preimage `ρ⁻¹(C)` -/

variable {n : ℕ}

/-- The preimage `ρ⁻¹(C) ⊆ ℤⁿ` of a code under reduction mod `q`. This is the carrier of
`latticeOfCode`. -/
def preimageOfCode {q : ℕ} (C : Code q n) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.comap (reduceMod q n) (C.restrictScalars ℤ)

@[simp] theorem mem_preimageOfCode {q : ℕ} {C : Code q n} {x : Fin n → ℤ} :
    x ∈ preimageOfCode C ↔ reduceMod q n x ∈ C := Iff.rfl

/-- Every codeword is the reduction of a lattice vector. -/
theorem exists_mem_preimageOfCode {q : ℕ} [NeZero q] (C : Code q n) {c : Fin n → ZMod q}
    (hc : c ∈ C) : ∃ x ∈ preimageOfCode C, reduceMod q n x = c := by
  obtain ⟨x, hx⟩ := reduceMod_surjective q n c
  exact ⟨x, by rw [mem_preimageOfCode, hx]; exact hc, hx⟩

theorem two_smul_mem_preimageOfCode (C : Code 2 n) (x : Fin n → ℤ) :
    (2 : ℤ) • x ∈ preimageOfCode C := by
  rw [mem_preimageOfCode, map_smul]
  have h2 : ((2 : ℤ) • (reduceMod 2 n x)) = 0 := by
    funext i
    simp only [Pi.smul_apply, zsmul_eq_mul, Pi.zero_apply]
    have : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [this, zero_mul]
  rw [h2]
  exact C.zero_mem

/-- Integrality of the halved form: this is exactly the hypothesis `C ⊆ Cᗮ`. -/
theorem two_dvd_dotProduct_of_mem {C : Code 2 n} (hC : C ≤ C.dual) {x y : Fin n → ℤ}
    (hx : x ∈ preimageOfCode C) (hy : y ∈ preimageOfCode C) : (2 : ℤ) ∣ x ⬝ᵥ y := by
  have h0 : ((x ⬝ᵥ y : ℤ) : ZMod 2) = 0 := by
    rw [intCast_dotProduct]
    exact Code.mem_dual'.mp (hC (mem_preimageOfCode.mp hx)) _ (mem_preimageOfCode.mp hy)
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ⬝ᵥ y) 2).mp h0
  simpa using this

/-! ### The lattice `Γ_C` -/

/-- **Ebeling's construction (§1.3), `BLUEPRINT.md` D2.** For a self-orthogonal binary code `C`,
`latticeOfCode C hC` is the lattice with carrier `ρ⁻¹(C) ⊆ ℤⁿ` and form `⟪x,y⟫ = (∑ᵢ xᵢyᵢ)/2`.
It is isometric to Ebeling's `Γ_C = (1/√2) ρ⁻¹(C)`. -/
noncomputable def latticeOfCode (C : Code 2 n) (hC : C ≤ C.dual) : IntegralLattice where
  carrier := ↥(preimageOfCode C)
  bilin := LinearMap.mk₂ ℤ
    (fun x y => ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / 2)
    (fun x₁ x₂ y => by
      simp only [Submodule.coe_add, add_dotProduct]
      exact Int.add_ediv_of_dvd_left (two_dvd_dotProduct_of_mem hC x₁.2 y.2))
    (fun c x y => by
      simp only [Submodule.coe_smul, smul_dotProduct, smul_eq_mul]
      rw [Int.mul_ediv_assoc _ (two_dvd_dotProduct_of_mem hC x.2 y.2)])
    (fun x y₁ y₂ => by
      simp only [Submodule.coe_add, dotProduct_add]
      exact Int.add_ediv_of_dvd_left (two_dvd_dotProduct_of_mem hC x.2 y₁.2))
    (fun c x y => by
      simp only [Submodule.coe_smul, dotProduct_smul, smul_eq_mul]
      rw [Int.mul_ediv_assoc _ (two_dvd_dotProduct_of_mem hC x.2 y.2)])
  bilin_symm x y := by
    show ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / 2 = ((y : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / 2
    rw [dotProduct_comm]

@[simp] theorem latticeOfCode_bilin (C : Code 2 n) (hC : C ≤ C.dual)
    (x y : preimageOfCode C) :
    (latticeOfCode C hC).bilin x y = ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / 2 := rfl

theorem two_mul_latticeOfCode_bilin (C : Code 2 n) (hC : C ≤ C.dual)
    (x y : preimageOfCode C) :
    2 * (latticeOfCode C hC).bilin x y = (x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ) := by
  rw [latticeOfCode_bilin]
  exact Int.mul_ediv_cancel' (two_dvd_dotProduct_of_mem hC x.2 y.2)

/-! ### Positive definiteness and rank -/

theorem dotProduct_self_pos {x : Fin n → ℤ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [Pi.zero_apply] at hi
  rw [dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem latticeOfCode_isPosDef (C : Code 2 n) (hC : C ≤ C.dual) :
    (latticeOfCode C hC).IsPosDef := by
  show ∀ x : preimageOfCode C, x ≠ 0 → 0 < ((x : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / 2
  intro x hx
  have hxne : (x : Fin n → ℤ) ≠ 0 := fun h => hx (Subtype.ext h)
  have hpos : 0 < (x : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ) := dotProduct_self_pos hxne
  obtain ⟨k, hk⟩ := two_dvd_dotProduct_of_mem hC x.2 x.2
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  omega

theorem finrank_preimageOfCode (C : Code 2 n) : finrank ℤ (preimageOfCode C) = n := by
  refine le_antisymm ?_ ?_
  · have h := Submodule.finrank_le (preimageOfCode C)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  · let g : (Fin n → ℤ) →ₗ[ℤ] preimageOfCode C :=
      { toFun := fun x => ⟨(2 : ℤ) • x, two_smul_mem_preimageOfCode C x⟩
        map_add' := fun x y => by ext i; simp; ring
        map_smul' := fun c x => by ext i; simp; ring }
    have hg : Function.Injective g := by
      intro x y hxy
      have : (2 : ℤ) • x = (2 : ℤ) • y := congrArg Subtype.val hxy
      exact smul_right_injective _ (by norm_num) this
    have h := LinearMap.finrank_le_finrank_of_injective (f := g) hg
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

@[simp] theorem latticeOfCode_rank (C : Code 2 n) (hC : C ≤ C.dual) :
    (latticeOfCode C hC).rank = n :=
  finrank_preimageOfCode C

/-! ### Ebeling, Proposition 1.3: `Γ_C` is even iff `C` is doubly even -/

/-- `a² ≡ 0 (mod 4)` when `a` is even and `a² ≡ 1 (mod 4)` when `a` is odd: the arithmetic
behind Proposition 1.3. -/
theorem four_dvd_mul_self_sub_parity (a : ℤ) :
    (4 : ℤ) ∣ a * a - (if (2 : ℤ) ∣ a then 0 else 1) := by
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    exact ⟨m * m, by rw [hm]; ring⟩
  · obtain ⟨m, hm⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
    exact ⟨m * m + m, by rw [hm]; ring⟩

theorem weight_reduceMod_eq_sum (x : Fin n → ℤ) :
    ((Code.weight (reduceMod 2 n x) : ℕ) : ℤ) = ∑ i, if (2 : ℤ) ∣ x i then (0 : ℤ) else 1 := by
  classical
  have hsupp : Code.support (reduceMod 2 n x)
      = Finset.univ.filter (fun i => ¬ (2 : ℤ) ∣ x i) := by
    ext i
    simp only [Code.mem_support, Finset.mem_filter, Finset.mem_univ, true_and, reduceMod_apply,
      ne_eq]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  rw [Code.weight_eq_card_support, hsupp, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul, mul_one]

theorem four_dvd_dotProduct_self_sub_weight (x : Fin n → ℤ) :
    (4 : ℤ) ∣ x ⬝ᵥ x - (Code.weight (reduceMod 2 n x) : ℤ) := by
  rw [dotProduct, weight_reduceMod_eq_sum, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => four_dvd_mul_self_sub_parity (x i)

/-- **Ebeling, Proposition 1.3.** `Γ_C` is an even lattice exactly when `C` is doubly even. -/
theorem latticeOfCode_isEven (C : Code 2 n) (hC : C ≤ C.dual) :
    (latticeOfCode C hC).IsEven ↔ C.IsDoublyEven := by
  have key : ∀ x : preimageOfCode C,
      ((2 : ℤ) ∣ ((x : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / 2
        ↔ 4 ∣ Code.weight (reduceMod 2 n (x : Fin n → ℤ))) := by
    intro x
    obtain ⟨k, hk⟩ := two_dvd_dotProduct_of_mem hC x.2 x.2
    obtain ⟨m, hm⟩ := four_dvd_dotProduct_self_sub_weight (x : Fin n → ℤ)
    have hdiv : ((x : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / 2 = k := by
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [hk] at hm
    rw [hdiv, ← Int.natCast_dvd_natCast (m := 4)]
    push_cast
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j - m, by omega⟩
    · rintro ⟨j, hj⟩
      exact ⟨j + m, by omega⟩
  constructor
  · intro h c hc
    obtain ⟨x, hx, hxc⟩ := exists_mem_preimageOfCode C hc
    have := (key ⟨x, hx⟩).mp (h ⟨x, hx⟩)
    rwa [hxc] at this
  · intro h
    show ∀ x : preimageOfCode C, (2 : ℤ) ∣ ((x : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / 2
    intro x
    exact (key x).mpr (h _ (mem_preimageOfCode.mp x.2))

/-! ### Ebeling, Proposition 1.4: the determinant -/

/-- A `ℤ`-basis of `ρ⁻¹(C)` indexed by `Fin n`. -/
noncomputable def preimageBasis (C : Code 2 n) : Basis (Fin n) ℤ (preimageOfCode C) :=
  (finBasis ℤ (preimageOfCode C)).reindex (finCongr (finrank_preimageOfCode C))

theorem card_quotient_preimageOfCode (C : Code 2 n) :
    Nat.card ((Fin n → ℤ) ⧸ preimageOfCode C) = 2 ^ (n - C.rank) := by
  classical
  let φ : (Fin n → ℤ) →ₗ[ℤ] ((Fin n → ZMod 2) ⧸ C) :=
    (AddMonoidHom.toIntLinearMap (Submodule.mkQ C).toAddMonoidHom).comp (reduceMod 2 n)
  have hker : LinearMap.ker φ = preimageOfCode C := by
    ext x
    show (Submodule.mkQ C) (reduceMod 2 n x) = 0 ↔ reduceMod 2 n x ∈ C
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective C y
    obtain ⟨x, rfl⟩ := reduceMod_surjective 2 n z
    exact ⟨x, rfl⟩
  rw [← hker, Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hsurj).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) C
  rw [Code.finrank_ambient] at h
  have hle : C.rank ≤ n := Code.rank_le C
  have hr : C.rank = finrank (ZMod 2) C := rfl
  show finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ C) = n - C.rank
  omega

/-- The matrix whose columns are the chosen `ℤ`-basis vectors of `ρ⁻¹(C)`, expressed in the
standard basis of `ℤⁿ`. -/
noncomputable def preimageBasisMatrix (C : Code 2 n) : Matrix (Fin n) (Fin n) ℤ :=
  (Pi.basisFun ℤ (Fin n)).toMatrix (fun i => ((preimageBasis C i : Fin n → ℤ)))

theorem preimageBasisMatrix_apply (C : Code 2 n) (i j : Fin n) :
    preimageBasisMatrix C i j = ((preimageBasis C j : Fin n → ℤ)) i := by
  rw [preimageBasisMatrix, Basis.toMatrix_apply]
  simp

theorem natAbs_det_preimageBasisMatrix (C : Code 2 n) :
    (preimageBasisMatrix C).det.natAbs = 2 ^ (n - C.rank) := by
  rw [preimageBasisMatrix, ← Basis.det_apply, ← card_quotient_preimageOfCode C]
  exact Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) (preimageOfCode C)
    (preimageBasis C)

/-- Doubling the Gram matrix of `Γ_C` recovers the Gram matrix of the *unscaled* dot product,
which is `Pᵀ P` for the basis matrix `P`. -/
theorem two_smul_gram_preimageBasis (C : Code 2 n) (hC : C ≤ C.dual) :
    (2 : ℤ) • (latticeOfCode C hC).gram (preimageBasis C)
      = (preimageBasisMatrix C)ᵀ * (preimageBasisMatrix C) := by
  ext i j
  have h2 := two_mul_latticeOfCode_bilin C hC (preimageBasis C i) (preimageBasis C j)
  -- `IntegralLattice.gram_apply` must be applied with explicit arguments: `rw` cannot match it
  -- here, because the `Module ℤ` instance on `(latticeOfCode C hC).carrier` is only
  -- *definitionally*, not syntactically, the one on `↥(preimageOfCode C)`.
  have hgram : (latticeOfCode C hC).gram (preimageBasis C) i j
      = (latticeOfCode C hC).bilin (preimageBasis C i) (preimageBasis C j) :=
    IntegralLattice.gram_apply (latticeOfCode C hC) (preimageBasis C) i j
  rw [Matrix.smul_apply, smul_eq_mul, hgram, h2, Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl fun l _ => by
    rw [Matrix.transpose_apply, preimageBasisMatrix_apply, preimageBasisMatrix_apply, mul_comm]

/-- **Ebeling, Proposition 1.4.** `det Γ_C = 2 ^ (n - 2k)` where `k = dim C`. -/
theorem latticeOfCode_det (C : Code 2 n) (hC : C ≤ C.dual) :
    (latticeOfCode C hC).det = 2 ^ (n - 2 * C.rank) := by
  classical
  have hk : 2 * C.rank ≤ n := Code.IsSelfOrthogonal.two_mul_rank_le hC
  have hle : C.rank ≤ n := Code.rank_le C
  have hdet : (2 : ℤ) ^ n * (latticeOfCode C hC).det
      = (preimageBasisMatrix C).det * (preimageBasisMatrix C).det := by
    have h1 := congrArg Matrix.det (two_smul_gram_preimageBasis C hC)
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin] at h1
    rwa [IntegralLattice.det_eq_gram_det (latticeOfCode C hC) (preimageBasis C)] at h1
  have hPP : (preimageBasisMatrix C).det * (preimageBasisMatrix C).det
      = 2 ^ (2 * (n - C.rank)) := by
    have h1 : (((preimageBasisMatrix C).det.natAbs : ℕ) : ℤ) = (2 : ℤ) ^ (n - C.rank) := by
      rw [natAbs_det_preimageBasisMatrix C]
      push_cast
      ring
    have h2 : (preimageBasisMatrix C).det * (preimageBasisMatrix C).det
        = (((preimageBasisMatrix C).det.natAbs : ℕ) : ℤ)
          * (((preimageBasisMatrix C).det.natAbs : ℕ) : ℤ) :=
      (Int.natAbs_mul_self' _).symm
    rw [h2, h1, ← pow_add]
    congr 1
    omega
  rw [hPP] at hdet
  have hpow : (2 : ℤ) ^ (2 * (n - C.rank)) = 2 ^ n * 2 ^ (n - 2 * C.rank) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hdet
  exact mul_left_cancel₀ (by positivity) hdet

/-- **Ebeling, Proposition 1.4.** `Γ_C` is unimodular exactly when `C` is self-dual. -/
theorem latticeOfCode_isUnimodular (C : Code 2 n) (hC : C ≤ C.dual) :
    (latticeOfCode C hC).IsUnimodular ↔ C.IsSelfDual := by
  have hk : 2 * C.rank ≤ n := Code.IsSelfOrthogonal.two_mul_rank_le hC
  rw [Code.isSelfDual_iff]
  constructor
  · intro h
    refine ⟨hC, ?_⟩
    rw [IntegralLattice.isUnimodular_iff, latticeOfCode_det] at h
    rcases h with h | h
    · have : n - 2 * C.rank = 0 := by
        by_contra hne
        have : (2 : ℤ) ^ (n - 2 * C.rank) ≠ 1 := by
          have h2 : 1 < (2 : ℤ) ^ (n - 2 * C.rank) :=
            one_lt_pow₀ (by norm_num) hne
          omega
        exact this h
      omega
    · have : (0 : ℤ) < 2 ^ (n - 2 * C.rank) := by positivity
      omega
  · rintro ⟨-, hr⟩
    rw [IntegralLattice.IsUnimodular, latticeOfCode_det]
    have : n - 2 * C.rank = 0 := by omega
    rw [this, pow_zero]
    exact isUnit_one
