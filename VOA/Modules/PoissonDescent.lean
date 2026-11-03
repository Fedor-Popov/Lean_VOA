/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.C2Cofinite

/-!
# The Poisson algebra `A₂(𝒱)` — the descended `CommRing` + `LieRing`  (Gannon §5.3.2)

The representative-level Poisson identities of `Modules.C2Cofinite` are here **descended** to
genuine algebra instances on the quotient `A₂(𝒱) = 𝒱 ⧸ O₂(𝒱)`:

* **`O₂` is a two-sided ideal** for both `₍₋₁₎` and `₍₀₎` (`poissonMul_mem_O₂_left/right`,
  `poissonBracket_mem_O₂_left/right`): the left-ideal property is the all-`ℤ` Borcherds iterate
  `mode_iterate` applied to a generator `a₍₋₂₎b` (every summand has outer mode `≤ −2`, hence in
  `O₂`); the right-ideal property is the left one plus commutativity/antisymmetry mod `O₂`
  (`C2Cofinite.poissonMul_sub_swap_mem_O₂` / `poissonBracket_add_swap_mem_O₂`).
* **The descent** `descendBilin` lifts a two-sided-ideal bilinear map to `A₂`, giving the
  product `A₂mul` (`[u]·[v] = [u₍₋₁₎v]`) and bracket `A₂bracket` (`[[u],[v]] = [u₍₀₎v]`).
* **`A₂CommRing`** — the commutative associative product (associativity mod `O₂` is
  `poissonMul_assoc_mem_O₂`, off `mode_iterate` at `ℓ = −1`), unit `[𝟙]`.
* **`A₂LieRing`** — the Lie bracket (antisymmetry, self-bracket `0`, Jacobi from
  `zeroMode_isDerivation`). Both instances reuse the quotient `AddCommGroup` (no diamond).

## Status
`sorry`-free, with no project axioms. The `O₂` two-sided-ideal lemmas, the descent,
`A₂CommRing`, and `A₂LieRing` are all `[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2, eqs. (5.3.11); Zhu [574]; Li (Poisson structure of `A₂`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Step 0: `u₍ₙ₎v ∈ O₂` for every `n ≤ -2`.

`O₂ = span{a₍₋₂₎b}`.  For `n ≤ -2` write `n = -(k+1)-1` with the helper `smul_Tpow`
specialised at the base index `-2`:
`(Tᵏu)₍₋₂₎v = (∏_{i<k} (2+i)) • u₍₋₂₋ₖ₎v`, and `(Tᵏu)₍₋₂₎v` is *literally* a generator of `O₂`.
-/

/-- `u₍₋₂₋ₖ₎v ∈ O₂` for all `k : ℕ`. -/
theorem smul_neg_two_sub_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    W.smul u (-2 - (k : ℤ)) v ∈ O₂ W := by
  -- `(Tᵏu)₍₋₂₎v = (∏_{i<k} (2+i)) • u₍₋₂₋ₖ₎v`, with the product a nonzero integer.
  have hkey : W.smul ((W.toPreVertexAlgebra.T ^ k) u) (-2) v
      = (∏ i ∈ Finset.range k, (-((-2 : ℤ) - (i : ℤ)))) • W.smul u (-2 - (k : ℤ)) v := by
    have h := smul_Tpow W u v k (-2)
    rwa [show (-2 : ℤ) - (k : ℤ) = -2 - (k : ℤ) from rfl] at h
  -- the product is `∏ (2+i) > 0`, hence nonzero
  set c : ℤ := ∏ i ∈ Finset.range k, (-((-2 : ℤ) - (i : ℤ))) with hc
  have hcpos : 0 < c := by
    rw [hc]
    apply Finset.prod_pos
    intro i _
    omega
  have hcne : (c : ℤ) ≠ 0 := ne_of_gt hcpos
  -- `(Tᵏu)₍₋₂₎v` is a generator of O₂
  have hgen : W.smul ((W.toPreVertexAlgebra.T ^ k) u) (-2) v ∈ O₂ W :=
    Submodule.subset_span ⟨(W.toPreVertexAlgebra.T ^ k) u, v, rfl⟩
  rw [hkey] at hgen
  -- divide out the scalar `c`
  have : W.smul u (-2 - (k : ℤ)) v = ((c : ℂ)⁻¹) • ((c : ℤ) • W.smul u (-2 - (k : ℤ)) v) := by
    rw [← Int.cast_smul_eq_zsmul ℂ c, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hcne), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ hgen

/-- `u₍ₙ₎v ∈ O₂` for every `n ≤ -2`. -/
theorem smul_le_neg_two_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) {n : ℤ} (hn : n ≤ -2) :
    W.smul u n v ∈ O₂ W := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -2 - (k : ℤ) := ⟨(-2 - n).toNat, by omega⟩
  exact smul_neg_two_sub_mem_O₂ W u v k

/-- **Finsum membership helper.**  A `finsum` of elements of a submodule `p` lies in `p`
(finite-support branch: a finset sum of members; infinite-support branch: the finsum is `0`). -/
theorem finsum_mem_submodule_pd {ι : Type*} (p : Submodule ℂ 𝒱) (F : ι → 𝒱)
    (hF : ∀ i, F i ∈ p) : (∑ᶠ i, F i) ∈ p := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
        (fun i hi => hfin.mem_toFinset.mpr hi)]
    exact Submodule.sum_mem _ (fun i _ => hF i)
  · rw [finsum_of_infinite_support (by rwa [Set.not_finite] at hfin)]
    exact p.zero_mem

/-! ## Step 1: `O₂` is a LEFT ideal under `₍₋₁₎` and `₍₀₎`.

By the all-`ℤ` Borcherds iterate `mode_iterate`, for a generator `a₍₋₂₎b` and any outer mode
`N`, `(a₍₋₂₎b)₍ₙ₎x = ∑ᵢ cᵢ • (a₍₋₂₋ᵢ₎(b₍ₙ₊ᵢ₎x) − (±)•b₍₋₃₊ₙ₋ᵢ₎(a₍ᵢ₎x))`.  For `N = -1` the
outer modes are `-2-i ≤ -2` and `-3-i ≤ -2`; for `N = 0` they are `-2-i ≤ -2` and `-2-i ≤ -2`.
Every summand is thus in `O₂` (Step 0), so the whole finsum is (`finsum_mem_submodule_pd`). -/

/-- `(a₍₋₂₎b)₍ₙ₎x ∈ O₂` for any outer mode `N ≤ 0` (every iterate summand has outer mode `≤ -2`). -/
theorem gen_smul_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (a b x : 𝒱) {N : ℤ} (hN : N ≤ 0) :
    W.smul (W.smul a (-2) b) N x ∈ O₂ W := by
  rw [show (-2 : ℤ) = -(1 : ℤ) - 1 from by ring]
  rw [mode_iterate W a b (-(1 : ℤ) - 1) N x]
  apply finsum_mem_submodule_pd
  intro i
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · -- A-term: outer mode `(-1-1) - i = -2 - i ≤ -2`
    exact smul_le_neg_two_mem_O₂ W a _ (by push_cast; omega)
  · -- B-term: outer mode `(-1-1) + N - i = -2 + N - i ≤ -2`
    apply Submodule.smul_mem
    exact smul_le_neg_two_mem_O₂ W b _ (by push_cast; omega)

/-- **`O₂` is a left ideal for `₍₋₁₎`**: `u ∈ O₂ → u₍₋₁₎v ∈ O₂`. -/
theorem poissonMul_mem_O₂_left (W : VertexOperatorAlgebra 𝒱) {u : 𝒱} (hu : u ∈ O₂ W) (v : 𝒱) :
    poissonMul W u v ∈ O₂ W := by
  simp only [poissonMul_def]
  -- `u ↦ u₍₋₁₎v` is a linear map; O₂ is generated by `a₍₋₂₎b`; check on generators.
  refine Submodule.span_induction (p := fun u _ => W.smul u (-1) v ∈ O₂ W) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨a, b, rfl⟩
    exact gen_smul_mem_O₂ W a b v (by norm_num)
  · simp only [PreVertexAlgebra.smul_zero_left]; exact (O₂ W).zero_mem
  · intro x y _ _ hx hy
    rw [PreVertexAlgebra.smul_add_left]; exact (O₂ W).add_mem hx hy
  · intro c x _ hx
    rw [PreVertexAlgebra.smul_smul_left]; exact (O₂ W).smul_mem c hx

/-- **`O₂` is a left ideal for `₍₀₎`**: `u ∈ O₂ → u₍₀₎v ∈ O₂`. -/
theorem poissonBracket_mem_O₂_left (W : VertexOperatorAlgebra 𝒱) {u : 𝒱} (hu : u ∈ O₂ W) (v : 𝒱) :
    poissonBracket W u v ∈ O₂ W := by
  simp only [poissonBracket_def]
  refine Submodule.span_induction (p := fun u _ => W.smul u 0 v ∈ O₂ W) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨a, b, rfl⟩
    exact gen_smul_mem_O₂ W a b v (le_refl 0)
  · simp only [PreVertexAlgebra.smul_zero_left]; exact (O₂ W).zero_mem
  · intro x y _ _ hx hy
    rw [PreVertexAlgebra.smul_add_left]; exact (O₂ W).add_mem hx hy
  · intro c x _ hx
    rw [PreVertexAlgebra.smul_smul_left]; exact (O₂ W).smul_mem c hx

/-! ## Step 2: `O₂` is a RIGHT ideal under `₍₋₁₎` and `₍₀₎` (via commutativity/antisymmetry mod O₂). -/

/-- **`O₂` is a right ideal for `₍₋₁₎`**: `u ∈ O₂ → v₍₋₁₎u ∈ O₂`.  From the left-ideal property and
the commutativity of the product mod `O₂` (`poissonMul_sub_swap_mem_O₂`). -/
theorem poissonMul_mem_O₂_right (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) {u : 𝒱} (hu : u ∈ O₂ W) :
    poissonMul W v u ∈ O₂ W := by
  have hswap : poissonMul W v u - poissonMul W u v ∈ O₂ W := poissonMul_sub_swap_mem_O₂ W v u
  have hleft : poissonMul W u v ∈ O₂ W := poissonMul_mem_O₂_left W hu v
  have : poissonMul W v u = (poissonMul W v u - poissonMul W u v) + poissonMul W u v := by
    abel
  rw [this]; exact (O₂ W).add_mem hswap hleft

/-- **`O₂` is a right ideal for `₍₀₎`**: `u ∈ O₂ → v₍₀₎u ∈ O₂`.  From the left-ideal property and
the antisymmetry of the bracket mod `O₂` (`poissonBracket_add_swap_mem_O₂`). -/
theorem poissonBracket_mem_O₂_right (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) {u : 𝒱} (hu : u ∈ O₂ W) :
    poissonBracket W v u ∈ O₂ W := by
  have hswap : poissonBracket W v u + poissonBracket W u v ∈ O₂ W :=
    poissonBracket_add_swap_mem_O₂ W v u
  have hleft : poissonBracket W u v ∈ O₂ W := poissonBracket_mem_O₂_left W hu v
  have : poissonBracket W v u = (poissonBracket W v u + poissonBracket W u v)
      - poissonBracket W u v := by abel
  rw [this]; exact (O₂ W).sub_mem hswap hleft

/-! ## Step 3: package the products as `ℂ`-bilinear maps `𝒱 →ₗ 𝒱 →ₗ 𝒱`. -/

/-- The Poisson product as a `ℂ`-bilinear map `𝒱 →ₗ 𝒱 →ₗ 𝒱`. -/
noncomputable def poissonMulₗ (W : VertexOperatorAlgebra 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u :=
    { toFun := fun v => poissonMul W u v
      map_add' := fun v₁ v₂ => by simp only [poissonMul_def, PreVertexAlgebra.smul_add_right]
      map_smul' := fun c v => by simp only [poissonMul_def, PreVertexAlgebra.smul_smul_right,
        RingHom.id_apply] }
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [poissonMul_def, PreVertexAlgebra.smul_add_left, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext fun v => ?_
    simp only [poissonMul_def, PreVertexAlgebra.smul_smul_left, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

/-- The Poisson bracket as a `ℂ`-bilinear map `𝒱 →ₗ 𝒱 →ₗ 𝒱`. -/
noncomputable def poissonBracketₗ (W : VertexOperatorAlgebra 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u :=
    { toFun := fun v => poissonBracket W u v
      map_add' := fun v₁ v₂ => by simp only [poissonBracket_def, PreVertexAlgebra.smul_add_right]
      map_smul' := fun c v => by simp only [poissonBracket_def, PreVertexAlgebra.smul_smul_right,
        RingHom.id_apply] }
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [poissonBracket_def, PreVertexAlgebra.smul_add_left, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext fun v => ?_
    simp only [poissonBracket_def, PreVertexAlgebra.smul_smul_left, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply]

@[simp] theorem poissonMulₗ_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonMulₗ W u v = poissonMul W u v := rfl

@[simp] theorem poissonBracketₗ_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    poissonBracketₗ W u v = poissonBracket W u v := rfl

/-! ## Step 4: descend a two-sided-ideal bilinear map to `A₂ W`. -/

/-- Right-lift of `B`: `O₂ ≤ ker (B.compr₂ mk₂).flip`. -/
theorem descend_right_ker (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O₂ W → B u v ∈ O₂ W) :
    O₂ W ≤ LinearMap.ker (B.compr₂ (mk₂ W)).flip := by
  intro v hv
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.zero_apply, mk₂]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hright u hv)

/-- Left-lift of `B`: `O₂ ≤ ker (((B.compr₂ mk₂).flip.liftQ).flip)`. -/
theorem descend_left_ker (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O₂ W → ∀ v, B u v ∈ O₂ W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O₂ W → B u v ∈ O₂ W) :
    O₂ W ≤ LinearMap.ker
      (((O₂ W).liftQ (B.compr₂ (mk₂ W)).flip (descend_right_ker W B hright)).flip) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun vb => ?_
  refine Submodule.Quotient.induction_on _ vb fun v => ?_
  simp only [LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.compr₂_apply,
    LinearMap.zero_apply, mk₂]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hleft hu v)

/-- **Generic descent** of a `ℂ`-bilinear map `B : 𝒱 →ₗ 𝒱 →ₗ 𝒱` to `A₂ W`, given that `O₂` is a
two-sided ideal for `B`.  Returns `A₂ W →ₗ A₂ W →ₗ A₂ W` with `descend B ū v̄ = mk₂ (B u v)`. -/
noncomputable def descendBilin (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O₂ W → ∀ v, B u v ∈ O₂ W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O₂ W → B u v ∈ O₂ W) :
    A₂ W →ₗ[ℂ] A₂ W →ₗ[ℂ] A₂ W :=
  (O₂ W).liftQ
    (((O₂ W).liftQ (B.compr₂ (mk₂ W)).flip (descend_right_ker W B hright)).flip)
    (descend_left_ker W B hleft hright)

theorem descendBilin_apply (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O₂ W → ∀ v, B u v ∈ O₂ W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O₂ W → B u v ∈ O₂ W) (u v : 𝒱) :
    descendBilin W B hleft hright (mk₂ W u) (mk₂ W v) = mk₂ W (B u v) := by
  simp only [descendBilin, mk₂, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.flip_apply,
    LinearMap.compr₂_apply]

/-! ## Step 5: the descended Poisson product and bracket on `A₂ W`. -/

/-- The **descended Poisson product** `A₂ W →ₗ A₂ W →ₗ A₂ W`, `[u]·[v] = [u₍₋₁₎v]`. -/
noncomputable def A₂mul (W : VertexOperatorAlgebra 𝒱) : A₂ W →ₗ[ℂ] A₂ W →ₗ[ℂ] A₂ W :=
  descendBilin W (poissonMulₗ W)
    (fun {u} hu v => poissonMul_mem_O₂_left W hu v)
    (fun u {v} hv => poissonMul_mem_O₂_right W u hv)

/-- The **descended Poisson bracket** `A₂ W →ₗ A₂ W →ₗ A₂ W`, `[[u],[v]] = [u₍₀₎v]`. -/
noncomputable def A₂bracket (W : VertexOperatorAlgebra 𝒱) : A₂ W →ₗ[ℂ] A₂ W →ₗ[ℂ] A₂ W :=
  descendBilin W (poissonBracketₗ W)
    (fun {u} hu v => poissonBracket_mem_O₂_left W hu v)
    (fun u {v} hv => poissonBracket_mem_O₂_right W u hv)

@[simp] theorem A₂mul_mk (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    A₂mul W (mk₂ W u) (mk₂ W v) = mk₂ W (poissonMul W u v) := by
  rw [A₂mul, descendBilin_apply]; rfl

@[simp] theorem A₂bracket_mk (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    A₂bracket W (mk₂ W u) (mk₂ W v) = mk₂ W (poissonBracket W u v) := by
  rw [A₂bracket, descendBilin_apply]; rfl

/-- `mk₂` is surjective. -/
theorem mk₂_surjective (W : VertexOperatorAlgebra 𝒱) : Function.Surjective (mk₂ W) :=
  Submodule.mkQ_surjective _

/-- `mk₂ W u = mk₂ W v ↔ u - v ∈ O₂`. -/
theorem mk₂_eq_iff (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱} :
    mk₂ W u = mk₂ W v ↔ u - v ∈ O₂ W := by
  rw [mk₂, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

theorem mk₂_eq_zero_iff (W : VertexOperatorAlgebra 𝒱) {u : 𝒱} :
    mk₂ W u = 0 ↔ u ∈ O₂ W := by
  rw [mk₂, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-! ## Step 6: the descended Poisson algebra laws on `A₂ W`. -/

/-- **Commutativity of the descended product**: `[u]·[v] = [v]·[u]`. -/
theorem A₂mul_comm (W : VertexOperatorAlgebra 𝒱) (p q : A₂ W) :
    A₂mul W p q = A₂mul W q p := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  rw [A₂mul_mk, A₂mul_mk, mk₂_eq_iff]
  exact poissonMul_sub_swap_mem_O₂ W u v

/-- **Antisymmetry of the descended bracket**: `[[u],[v]] = -[[v],[u]]`. -/
theorem A₂bracket_antisymm (W : VertexOperatorAlgebra 𝒱) (p q : A₂ W) :
    A₂bracket W p q = -(A₂bracket W q p) := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  rw [A₂bracket_mk, A₂bracket_mk, ← (mk₂ W).map_neg, mk₂_eq_iff]
  rw [show poissonBracket W u v - -poissonBracket W v u
      = poissonBracket W u v + poissonBracket W v u from by abel]
  exact poissonBracket_add_swap_mem_O₂ W u v

/-- **Self-bracket vanishes** `[[u],[u]] = 0` (from antisymmetry over `ℂ`). -/
theorem A₂bracket_self (W : VertexOperatorAlgebra 𝒱) (p : A₂ W) :
    A₂bracket W p p = 0 := by
  have h := A₂bracket_antisymm W p p
  -- `x = -x ⟹ 2x = 0 ⟹ x = 0` over `ℂ`
  have h2 : (2 : ℂ) • A₂bracket W p p = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; abel
  have := smul_eq_zero.mp h2
  rcases this with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

/-- **Leibniz / Poisson compatibility** on `A₂ W`:
`[[u], [v]·[w]] = [[u],[v]]·[w] + [v]·[[u],[w]]`.  Descends from the exact representative
identity `poissonBracket_leibniz`. -/
theorem A₂_leibniz (W : VertexOperatorAlgebra 𝒱) (p q r : A₂ W) :
    A₂bracket W p (A₂mul W q r)
      = A₂mul W (A₂bracket W p q) r + A₂mul W q (A₂bracket W p r) := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  obtain ⟨w, rfl⟩ := mk₂_surjective W r
  rw [A₂mul_mk, A₂bracket_mk, A₂bracket_mk, A₂bracket_mk, A₂mul_mk, A₂mul_mk,
    ← (mk₂ W).map_add]
  rw [mk₂_eq_iff]
  -- representative identity: `u₍₀₎(v₍₋₁₎w) = (u₍₀₎v)₍₋₁₎w + v₍₋₁₎(u₍₀₎w)`
  have h := poissonBracket_leibniz W u v w
  rw [show poissonBracket W u (poissonMul W v w)
      - (poissonMul W (poissonBracket W u v) w + poissonMul W v (poissonBracket W u w))
      = (poissonBracket W u (poissonMul W v w) - poissonMul W v (poissonBracket W u w))
        - poissonMul W (poissonBracket W u v) w from by abel]
  rw [h, sub_self]
  exact (O₂ W).zero_mem

/-! ## Step 7: associativity of the product mod `O₂` (part (b)).

By `mode_iterate` at `ℓ = -1`, `N = -1`:
`(u₍₋₁₎v)₍₋₁₎w = ∑ᵢ cᵢ•(u₍₋₁₋ᵢ₎(v₍₋₁₊ᵢ₎w) − (−1)⁻¹•v₍₋₂₋ᵢ₎(u₍ᵢ₎w))`.
The `i = 0` `u`-term is exactly `u₍₋₁₎(v₍₋₁₎w)` (coefficient `c₀ = (−1)⁰·gBinom(−1,0) = 1`); every
other summand has an outer mode `≤ −2` (`u₍₋₁₋ᵢ₎`, `i ≥ 1`; `v₍₋₂₋ᵢ₎`, `i ≥ 0`) and so lies in
`O₂` (Step 0).  Hence `(u₍₋₁₎v)₍₋₁₎w − u₍₋₁₎(v₍₋₁₎w) ∈ O₂`. -/

/-- The single iterate summand of `(u₍₋₁₎v)₍₋₁₎w` at index `i`. -/
private noncomputable def assocTerm (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) (i : ℕ) : 𝒱 :=
  ((-1 : ℂ) ^ i * gBinom (-1 : ℤ) i) •
    (W.smul u (-1 - (i : ℤ)) (W.smul v (-1 + (i : ℤ)) w)
      - ((-1 : ℂ) ^ (-1 : ℤ)) • W.smul v (-1 + -1 - (i : ℤ)) (W.smul u (i : ℤ) w))

/-- `(u₍₋₁₎v)₍₋₁₎w = ∑ᶠ i, assocTerm`. -/
private theorem assoc_mode_iterate (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    W.smul (W.smul u (-1) v) (-1) w = ∑ᶠ i : ℕ, assocTerm W u v w i :=
  mode_iterate W u v (-1) (-1) w

/-- Finiteness of the iterate finsum. -/
private theorem assocTerm_support_finite (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    (Function.support (assocTerm W u v w)).Finite := by
  obtain ⟨Na, hNa⟩ := W.regularity v w   -- `v₍ₙ₎w = 0` for `n ≥ Na`
  obtain ⟨Nb, hNb⟩ := W.regularity u w   -- `u₍ₙ₎w = 0` for `n ≥ Nb`
  apply Set.Finite.subset (Set.finite_Icc 0 (max (Na + 1) Nb).toNat)
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  rw [not_le] at hbig
  apply hi
  simp only [assocTerm]
  have hA : W.smul v (-1 + (i : ℤ)) w = 0 := hNa (-1 + (i : ℤ)) (by
    have h1 : Na + 1 ≤ max (Na + 1) Nb := le_max_left _ _
    omega)
  have hB : W.smul u (i : ℤ) w = 0 := hNb (i : ℤ) (by
    have h1 : Nb ≤ max (Na + 1) Nb := le_max_right _ _
    omega)
  rw [hA, hB, PreVertexAlgebra.smul_zero_right, PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero,
    smul_zero]

/-- Every iterate summand of index `i ≥ 1`, and the `v`-part of `i = 0`, lies in `O₂`;
the `i = 0` `u`-part is `u₍₋₁₎(v₍₋₁₎w)`.  We package: `assocTerm i − (i=0 ? RHS : 0) ∈ O₂`. -/
private theorem assocTerm_sub_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) (i : ℕ) :
    assocTerm W u v w i - (if i = 0 then W.smul u (-1) (W.smul v (-1) w) else 0) ∈ O₂ W := by
  simp only [assocTerm]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl]
    -- `c₀ = (-1)^0 * gBinom(-1,0) = 1*1 = 1`
    have hc0 : ((-1 : ℂ) ^ (0 : ℕ) * gBinom (-1 : ℤ) 0) = 1 := by
      simp [gBinom_negsucc 0 0]
    rw [hc0, one_smul]
    -- collapse the `i = 0` index casts
    simp only [Nat.cast_zero, sub_zero, add_zero]
    rw [show ((-1 : ℤ) + -1) = (-2 : ℤ) from by norm_num]
    -- term = u₍₋₁₎(v₍₋₁₎w) - (-1)⁻¹•v₍₋₂₎(u₍₀₎w); subtract RHS leaves the v-part ∈ O₂
    rw [show W.smul u (-1) (W.smul v (-1) w)
          - ((-1 : ℂ) ^ (-1 : ℤ)) • W.smul v (-2) (W.smul u (0 : ℤ) w)
          - W.smul u (-1) (W.smul v (-1) w)
        = -(((-1 : ℂ) ^ (-1 : ℤ)) • W.smul v (-2) (W.smul u (0 : ℤ) w)) from by abel]
    exact (O₂ W).neg_mem (Submodule.smul_mem _ _
      (smul_le_neg_two_mem_O₂ W v _ (le_refl (-2))))
  · rw [if_neg hi, sub_zero]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · -- u₍₋₁₋ᵢ₎(...) outer mode -1-i ≤ -2 (since i ≥ 1)
      exact smul_le_neg_two_mem_O₂ W u _ (by
        have : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
        push_cast; omega)
    · apply Submodule.smul_mem
      -- v₍₋₂₋ᵢ₎(...) outer mode -2-i ≤ -2
      exact smul_le_neg_two_mem_O₂ W v _ (by push_cast; omega)

/-- **Associativity of the Poisson product mod `O₂`** (part (b)):
`(u₍₋₁₎v)₍₋₁₎w − u₍₋₁₎(v₍₋₁₎w) ∈ O₂`. -/
theorem poissonMul_assoc_mem_O₂ (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    poissonMul W (poissonMul W u v) w - poissonMul W u (poissonMul W v w) ∈ O₂ W := by
  simp only [poissonMul_def]
  rw [assoc_mode_iterate W u v w]
  -- subtract `RHS` as the single-point finsum `∑ᶠ i, (if i=0 then RHS else 0)`
  have hRHS : W.smul u (-1) (W.smul v (-1) w)
      = ∑ᶠ i : ℕ, (if i = 0 then W.smul u (-1) (W.smul v (-1) w) else 0) := by
    rw [finsum_eq_single _ 0 (fun j hj => if_neg hj), if_pos rfl]
  rw [hRHS, ← finsum_sub_distrib (assocTerm_support_finite W u v w)
    (by
      apply Set.Finite.subset (Set.finite_singleton 0)
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Set.mem_singleton_iff] at hc
      exact hi (if_neg hc))]
  exact finsum_mem_submodule_pd (O₂ W) _ (fun i => assocTerm_sub_mem_O₂ W u v w i)

/-! ## Step 8: the descended ring laws (associativity, unit) and the `CommRing` instance. -/

/-- **Associativity of the descended product** on `A₂ W`. -/
theorem A₂mul_assoc (W : VertexOperatorAlgebra 𝒱) (p q r : A₂ W) :
    A₂mul W (A₂mul W p q) r = A₂mul W p (A₂mul W q r) := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  obtain ⟨w, rfl⟩ := mk₂_surjective W r
  rw [A₂mul_mk, A₂mul_mk, A₂mul_mk, A₂mul_mk, mk₂_eq_iff]
  exact poissonMul_assoc_mem_O₂ W u v w

/-- **Left unit** `[𝟙]·[v] = [v]` for the descended product. -/
theorem A₂mul_one_left (W : VertexOperatorAlgebra 𝒱) (p : A₂ W) :
    A₂mul W (mk₂ W W.vacuum) p = p := by
  obtain ⟨v, rfl⟩ := mk₂_surjective W p
  rw [A₂mul_mk, poissonMul_def]
  congr 1
  rw [show W.smul W.vacuum (-1) v = v from by
    rw [W.toPreVertexAlgebra.smul_vacuum_left]; simp]

/-- **Right unit** `[v]·[𝟙] = [v]` for the descended product. -/
theorem A₂mul_one_right (W : VertexOperatorAlgebra 𝒱) (p : A₂ W) :
    A₂mul W p (mk₂ W W.vacuum) = p := by
  obtain ⟨v, rfl⟩ := mk₂_surjective W p
  rw [A₂mul_mk, poissonMul_def, W.toPreVertexAlgebra.smul_vacuum_neg_one]

/-- The **commutative ring** `A₂(𝒱)` (the associative-commutative Poisson algebra of Gannon
§5.3.2), built on the existing quotient `AddCommGroup` (no additive diamond): the multiplication
is the descended normal product `[u]·[v] = [u₍₋₁₎v]`, the unit is `[𝟙]`. -/
noncomputable instance A₂CommRing (W : VertexOperatorAlgebra 𝒱) : CommRing (A₂ W) :=
  { (inferInstance : AddCommGroup (A₂ W)) with
    mul := fun p q => A₂mul W p q
    one := mk₂ W W.vacuum
    mul_assoc := A₂mul_assoc W
    mul_comm := A₂mul_comm W
    one_mul := A₂mul_one_left W
    mul_one := A₂mul_one_right W
    left_distrib := fun p q r => by
      show A₂mul W p (q + r) = A₂mul W p q + A₂mul W p r
      rw [map_add]
    right_distrib := fun p q r => by
      show A₂mul W (p + q) r = A₂mul W p r + A₂mul W q r
      rw [map_add]; rfl
    zero_mul := fun p => by
      show A₂mul W 0 p = 0
      rw [map_zero]; rfl
    mul_zero := fun p => by
      show A₂mul W p 0 = 0
      rw [map_zero] }

/-- The descended multiplication is the Poisson product on representatives:
`[u] * [v] = [u₍₋₁₎v]`. -/
theorem A₂_mul_mk (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    (mk₂ W u) * (mk₂ W v) = mk₂ W (poissonMul W u v) :=
  A₂mul_mk W u v

/-- The ring unit is `[𝟙]`. -/
theorem A₂_one_eq (W : VertexOperatorAlgebra 𝒱) :
    (1 : A₂ W) = mk₂ W W.vacuum := rfl

/-! ## Step 9: the Lie bracket on `A₂ W`.

The descended bracket `A₂bracket` is `ℂ`-bilinear, antisymmetric (`A₂bracket_antisymm`), and
self-annihilating (`A₂bracket_self`).  Assembled as the bracket of a `ℂ`-`LieRing`/`LieAlgebra`
structure would additionally need the Jacobi identity; the antisymmetry + bilinearity +
Leibniz (`A₂_leibniz`) compatibility with the commutative product are the Poisson-algebra data
recorded here. -/

/-- The descended Lie bracket on representatives: `⁅[u], [v]⁆ = [u₍₀₎v]`. -/
theorem A₂bracket_repr (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    A₂bracket W (mk₂ W u) (mk₂ W v) = mk₂ W (W.smul u 0 v) :=
  A₂bracket_mk W u v

/-- **Leibniz/Jacobi for the descended bracket** (the `n = 0` zero-mode derivation, EXACT on
representatives, hence exact on `A₂ W`):
`⁅[u], ⁅[v],[w]⁆⁆ = ⁅⁅[u],[v]⁆, [w]⁆ + ⁅[v], ⁅[u],[w]⁆⁆`. -/
theorem A₂bracket_leibniz (W : VertexOperatorAlgebra 𝒱) (p q r : A₂ W) :
    A₂bracket W p (A₂bracket W q r)
      = A₂bracket W (A₂bracket W p q) r + A₂bracket W q (A₂bracket W p r) := by
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  obtain ⟨v, rfl⟩ := mk₂_surjective W q
  obtain ⟨w, rfl⟩ := mk₂_surjective W r
  rw [A₂bracket_mk, A₂bracket_mk, A₂bracket_mk, A₂bracket_mk, A₂bracket_mk, A₂bracket_mk,
    ← (mk₂ W).map_add]
  congr 1
  -- `u₍₀₎(v₍₀₎w) = (u₍₀₎v)₍₀₎w + v₍₀₎(u₍₀₎w)` is `zeroMode_isDerivation` at `n = 0`, rearranged
  have h := W.zeroMode_isDerivation u v w 0
  simp only [poissonBracket_def]
  rw [← h]; abel

/-- The **Lie-ring bracket** on `A₂ W` (Poisson bracket), `⁅[u],[v]⁆ = [u₍₀₎v]`. -/
noncomputable instance A₂Bracket (W : VertexOperatorAlgebra 𝒱) : Bracket (A₂ W) (A₂ W) :=
  ⟨fun p q => A₂bracket W p q⟩

@[simp] theorem A₂_lie_def (W : VertexOperatorAlgebra 𝒱) (p q : A₂ W) :
    ⁅p, q⁆ = A₂bracket W p q := rfl

/-- The **Lie ring** `A₂(𝒱)` under the Poisson bracket `⁅[u],[v]⁆ = [u₍₀₎v]` (Gannon §5.3.2):
bilinear (from `A₂bracket`), `⁅x,x⁆ = 0` (`A₂bracket_self`), Leibniz/Jacobi
(`A₂bracket_leibniz`, the exact zero-mode derivation).  Built on the existing quotient
`AddCommGroup` (no additive diamond). -/
noncomputable instance A₂LieRing (W : VertexOperatorAlgebra 𝒱) : LieRing (A₂ W) :=
  { (inferInstance : AddCommGroup (A₂ W)), (A₂Bracket W) with
    add_lie := fun x y z => by
      show A₂bracket W (x + y) z = A₂bracket W x z + A₂bracket W y z
      rw [map_add]; rfl
    lie_add := fun x y z => by
      show A₂bracket W x (y + z) = A₂bracket W x y + A₂bracket W x z
      rw [map_add]
    lie_self := fun x => A₂bracket_self W x
    leibniz_lie := fun x y z => A₂bracket_leibniz W x y z }

end VOA
