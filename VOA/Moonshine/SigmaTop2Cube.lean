/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Xi

/-!
# The spinor cube: `Θ` on the codeword states `e^{1_D}` of `V_N`

For a codeword `D` (`4 ∣ |D|`) and `β = 1_D ∈ N` (`gv β = ind D`) the states `e^{β − δ_S}`,
`S ⊆ D`, span a `2^{|D|}`-dimensional "spinor cube" on which the root exponentials `G_i`
(`i ∈ D`) act through the `i`-th tensor factor.  In the normalised basis
`b_S = ν(S) e^{β − δ_S}`, `ν(S) = ε(δ_S, δ_S + β) ξ(1_S) i^{−|S|}` (`nuC`, with the recursion
`nuC_insert : ν(S ∪ i) = ν(S) ε_i ε(α_i, β − δ_S)`), `E_i, F_i` act by the standard doublet
matrices, so `G = ∏_j G_j`, `χ`, `χ z₀` act on product vectors `⊗_i φ_i` (`vecP`) factorwise.

## Main results
* `Qa_bp_mem`, `Qm_bp_not`, … — the screening operators on the cube basis.
* `G1_bp_not`, `G1_bp_mem`, `G1_bp_out`, `golayG_vecP`, `golayG_inv_vecP`.
* `golayChi_vecP`, `golayChiMod_vecP` (`χ z₀` contributes the global sign `cD D`).
* `golaySigma_vecP`, `golayTheta_vecP` — `σ`, `Θ` on the cube are tensor powers of explicit
  `2 × 2` matrices; `theta_local : Θ₁ (1,0) = (0,1)` (the `√2`-algebra closed exactly).
* `golayTheta_codeword : Θ e^{β} = ξ(1_D) e^{−β}` — the `Θ`-scalar of a codeword state.

## Status
`sorry`-free; `#print axioms golayTheta_codeword`: `[propext, Classical.choice, Quot.sound]`.
Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN VOA.LatGen.Screen

/-! ## §1  Indicators and the cube basis -/

/-- The indicator vector of `S`. -/
def ind (S : Finset (Fin 24)) : Fin 24 → ℤ := fun i => if i ∈ S then 1 else 0

/-- `δ_S = Σ_{i ∈ S} α_i`. -/
noncomputable def dl (S : Finset (Fin 24)) : golayN.carrier := phiR (ind S)

theorem ind_insert {S : Finset (Fin 24)} {i : Fin 24} (hi : i ∉ S) :
    ind (insert i S) = ind S + Pi.single i 1 := by
  funext l
  simp only [ind, Finset.mem_insert, Pi.add_apply, Pi.single_apply]
  by_cases h : l = i
  · subst h; simp [hi]
  · simp [h]

theorem dl_insert {S : Finset (Fin 24)} {i : Fin 24} (hi : i ∉ S) :
    dl (insert i S) = dl S + golayRoot i := by
  rw [dl, ind_insert hi, map_add, phiR_single]; rfl

theorem ind_empty : ind ∅ = 0 := by funext l; simp [ind]

theorem dl_empty : dl ∅ = 0 := by rw [dl, ind_empty, map_zero]

theorem form_root_left (i : Fin 24) (x : golayN.carrier) : golayN.form (golayRoot i) x = gv x i := by
  rw [golayN_form, golayRoot_coe, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
  omega

variable (β : golayN.carrier)

/-- The normalisation `ν(S) = ε(δ_S, δ_S + β) ξ(1_S) i^{-|S|}` of the cube basis. -/
noncomputable def nuC (S : Finset (Fin 24)) : ℂ :=
  εN (dl S) (dl S + β) * xi (ind S) * (Complex.I ^ S.card)⁻¹

/-- The cube basis `b_S = ν(S) e^{β − δ_S}`. -/
noncomputable def bp (S : Finset (Fin 24)) : LatModuleGen golayN :=
  nuC β S • latChargeGen golayN (β - dl S)

theorem nuC_empty : nuC β ∅ = 1 := by
  rw [nuC, dl_empty, ind_empty, xi_zero, Finset.card_empty, pow_zero, inv_one, mul_one, mul_one]
  exact latticeCocycle_zero_left _ _

theorem bp_empty : bp β ∅ = latChargeGen golayN β := by
  rw [bp, nuC_empty, one_smul, dl_empty, sub_zero]

/-- The cube recursion `ν(S ∪ i) = ν(S) ε_i ε(α_i, β − δ_S)`. -/
theorem nuC_insert {S : Finset (Fin 24)} {i : Fin 24} (hi : i ∉ S) :
    nuC β (insert i S) = nuC β S * golayEps i * εN (golayRoot i) (β - dl S) := by
  have hx := xi_mul (ind S) (Pi.single i 1)
  rw [xi_single, phiR_single, ← ind_insert hi] at hx
  change xi (ind S) * Complex.I = εN (dl S) (golayRoot i) * xi (ind (insert i S)) at hx
  rw [nuC, nuC, dl_insert hi, Finset.card_insert_of_notMem hi, pow_succ, mul_inv]
  have hs := εN_sq (dl S) (golayRoot i)
  have hx' : xi (ind (insert i S)) = εN (dl S) (golayRoot i) * xi (ind S) * Complex.I := by
    linear_combination (-(εN (dl S) (golayRoot i))) * hx - xi (ind (insert i S)) * hs
  rw [hx', ← εN_root_self i]
  simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right, sub_eq_add_neg,
    latticeCocycle_neg_right]
  have hI : Complex.I * Complex.I⁻¹ = 1 := mul_inv_cancel₀ Complex.I_ne_zero
  have h2 : latticeCocycle golayN (dl S) (golayRoot i) * latticeCocycle golayN (dl S) (golayRoot i) = 1 := hs
  have h3 : latticeCocycle golayN (golayRoot i) (dl S) * latticeCocycle golayN (dl S) (golayRoot i) = 1 := by
    rw [latticeCocycle_comm golayN golayN_even, form_root_left, dl, gv_phiR, Pi.smul_apply,
      smul_eq_mul, zpow_mul]
    norm_num
  set A := latticeCocycle golayN (dl S) (dl S) * latticeCocycle golayN (golayRoot i) (dl S) *
    latticeCocycle golayN (golayRoot i) (golayRoot i) * latticeCocycle golayN (dl S) β *
    latticeCocycle golayN (golayRoot i) β * xi (ind S) * Complex.I⁻¹ ^ S.card
  linear_combination A * (latticeCocycle golayN (dl S) (golayRoot i) * latticeCocycle golayN (dl S) (golayRoot i)) * hI + A * h2

/-! ## §2  The root operators on the cube -/

theorem Qscr_of_form_neg_one {γ x : golayN.carrier} (h : golayN.form γ x = -1) :
    Qscr golayN γ (latChargeGen golayN x) = εN γ x • latChargeGen golayN (γ + x) := by
  rw [Qscr_latChargeGen, EEVec_vacuum, h, if_pos (by norm_num)]
  rw [show (-1 - (-1 : ℤ)).toNat = 0 from rfl, vSchur_zero]
  rfl

variable {D : Finset (Fin 24)}

theorem gv_sub_dl (hβ : gv β = ind D) (S : Finset (Fin 24)) (l : Fin 24) :
    gv (β - dl S) l = ind D l - 2 * ind S l := by
  change gv β l - gv (dl S) l = _
  rw [hβ, dl, gv_phiR, Pi.smul_apply, smul_eq_mul]

theorem form_root_sub (hβ : gv β = ind D) (S : Finset (Fin 24)) (l : Fin 24) :
    golayN.form (golayRoot l) (β - dl S) = ind D l - 2 * ind S l := by
  rw [form_root_left, gv_sub_dl β hβ]

theorem form_negroot_sub (hβ : gv β = ind D) (S : Finset (Fin 24)) (l : Fin 24) :
    golayN.form (-golayRoot l) (β - dl S) = -(ind D l - 2 * ind S l) := by
  rw [map_neg, LinearMap.neg_apply, form_root_sub β hβ]

theorem dl_erase {S : Finset (Fin 24)} {i : Fin 24} (hi : i ∈ S) :
    dl S = dl (S.erase i) + golayRoot i := by
  rw [← dl_insert (Finset.notMem_erase i S), Finset.insert_erase hi]

/-- `Q_{α_i} b_S = b_{S∖i}` for `i ∈ S ⊆ D`. -/
theorem Qa_bp_mem (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {i : Fin 24} (hi : i ∈ S) :
    Qscr golayN (golayRoot i) (bp β S) = bp β (S.erase i) := by
  have hf : golayN.form (golayRoot i) (β - dl S) = -1 := by
    rw [form_root_sub β hβ]; simp [ind, hi, hS hi]
  rw [bp, map_smul, Qscr_of_form_neg_one hf, smul_smul, bp]
  have e1 : golayRoot i + (β - dl S) = β - dl (S.erase i) := by rw [dl_erase hi]; abel
  rw [e1]
  congr 1
  have hn := nuC_insert β (Finset.notMem_erase i S)
  rw [Finset.insert_erase hi] at hn
  rw [hn]
  have e2 : β - dl S = (β - dl (S.erase i)) + -golayRoot i := by rw [dl_erase hi]; abel
  rw [e2]
  simp only [εN, latticeCocycle_add_right, latticeCocycle_neg_right]
  have h3 := εN_root_self i
  have h1 := golayEps_mul_self i
  have h2 := εN_sq (golayRoot i) (β - dl (S.erase i))
  simp only [εN] at h3 h2 ⊢
  linear_combination (nuC β (S.erase i)) * golayEps i *
    (latticeCocycle golayN (golayRoot i) (β - dl (S.erase i)))^2 * h3
    + (nuC β (S.erase i)) * (latticeCocycle golayN (golayRoot i) (β - dl (S.erase i)))^2 * h1
    + (nuC β (S.erase i)) * h2

theorem Qa_bp_not (hβ : gv β = ind D) {S : Finset (Fin 24)} {i : Fin 24} (hiD : i ∈ D) (hi : i ∉ S) :
    Qscr golayN (golayRoot i) (bp β S) = 0 := by
  rw [bp, map_smul, Qscr_latChargeGen_of_nonneg, smul_zero]
  rw [form_root_sub β hβ]; simp [ind, hi, hiD]

/-- `ε_i Q_{−α_i} b_S = b_{S ∪ i}` for `i ∈ D ∖ S`. -/
theorem Qm_bp_not (hβ : gv β = ind D) {S : Finset (Fin 24)} {i : Fin 24} (hiD : i ∈ D) (hi : i ∉ S) :
    golayEps i • Qscr golayN (-golayRoot i) (bp β S) = bp β (insert i S) := by
  have hf : golayN.form (-golayRoot i) (β - dl S) = -1 := by
    rw [form_negroot_sub β hβ]; simp [ind, hi, hiD]
  rw [bp, map_smul, Qscr_of_form_neg_one hf, smul_smul, smul_smul, bp, nuC_insert β hi]
  have e1 : -golayRoot i + (β - dl S) = β - dl (insert i S) := by rw [dl_insert hi]; abel
  rw [e1]
  simp only [εN, latticeCocycle_neg_left]
  congr 1; ring

theorem Qm_bp_mem (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {i : Fin 24} (hi : i ∈ S) :
    Qscr golayN (-golayRoot i) (bp β S) = 0 := by
  rw [bp, map_smul, Qscr_latChargeGen_of_nonneg, smul_zero]
  rw [form_negroot_sub β hβ]; simp [ind, hi, hS hi]

theorem Qa_bp_out (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {k : Fin 24} (hk : k ∉ D) :
    Qscr golayN (golayRoot k) (bp β S) = 0 := by
  rw [bp, map_smul, Qscr_latChargeGen_of_nonneg, smul_zero]
  have hkS : k ∉ S := fun h => hk (hS h)
  rw [form_root_sub β hβ]; simp [ind, hk, hkS]

theorem Qm_bp_out (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {k : Fin 24} (hk : k ∉ D) :
    Qscr golayN (-golayRoot k) (bp β S) = 0 := by
  rw [bp, map_smul, Qscr_latChargeGen_of_nonneg, smul_zero]
  have hkS : k ∉ S := fun h => hk (hS h)
  rw [form_negroot_sub β hβ]; simp [ind, hk, hkS]

/-! ## §3  The root exponentials `G_i` on the cube -/

theorem aut_add {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (g : Aut W) (x y : 𝒱) : g (x + y) = g x + g y := g.toLinearEquiv.map_add x y

theorem aut_smul {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (g : Aut W) (c : ℂ) (x : 𝒱) : g (c • x) = c • g x := g.toLinearEquiv.map_smul c x

theorem aut_sum {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (g : Aut W) {ι : Type*} (s : Finset ι) (f : ι → 𝒱) : g (∑ i ∈ s, f i) = ∑ i ∈ s, g (f i) :=
  map_sum g.toLinearEquiv f s

theorem rootExp_sq {α : golayN.carrier} (hα : golayN.form α α = 2) (c : ℂ) {v : LatModuleGen golayN}
    (h : Qscr golayN α (Qscr golayN α v) = 0) :
    rootExp golayN golayN_even golayN_posDef hα c v = v + c • Qscr golayN α v := by
  rw [rootExp_apply_of_cube golayN golayN_posDef golayN_even hα c (by rw [h, map_zero]), h,
    smul_zero, add_zero]

/-- The constants of `g_j = exp(a E_j) exp(b F_j)`. -/
noncomputable abbrev aG : ℂ := ((1 - Real.sqrt 2 : ℝ) : ℂ)
noncomputable abbrev bG : ℂ := ((Real.sqrt 2 / 4 : ℝ) : ℂ)

theorem Qm_bp_not' (hβ : gv β = ind D) {S : Finset (Fin 24)} {i : Fin 24} (hiD : i ∈ D) (hi : i ∉ S) :
    Qscr golayN (-golayRoot i) (bp β S) = golayEps i • bp β (insert i S) := by
  rw [← Qm_bp_not β hβ hiD hi, smul_smul, golayEps_mul_self, one_smul]

/-- `G_i b_S = (1+ab) b_S + b b_{S∪i}` for `i ∈ D ∖ S`. -/
theorem G1_bp_not (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {i : Fin 24} (hiD : i ∈ D)
    (hi : i ∉ S) :
    golayG1 i (bp β S) = (1 + aG * bG) • bp β S + bG • bp β (insert i S) := by
  have hins : insert i S ⊆ D := Finset.insert_subset hiD hS
  have hin : i ∈ insert i S := Finset.mem_insert_self i S
  rw [golayG1, Aut.mul_apply]
  rw [rootExp_sq (golayRoot_neg_norm i) _ (by
      rw [Qm_bp_not' β hβ hiD hi, map_smul, Qm_bp_mem β hβ hins hin, smul_zero])]
  rw [Qm_bp_not' β hβ hiD hi, smul_smul, mul_assoc, golayEps_mul_self, mul_one, aut_add, aut_smul,
    rootExp_apply_of_Qscr_eq_zero golayN golayN_even golayN_posDef _ _ (Qa_bp_not β hβ hiD hi)]
  rw [rootExp_sq (golayRoot_norm i) _ (by
      rw [Qa_bp_mem β hβ hins hin, Finset.erase_insert hi, Qa_bp_not β hβ hiD hi])]
  rw [Qa_bp_mem β hβ hins hin, Finset.erase_insert hi]
  module

/-- `G_i b_S = b_S + a b_{S∖i}` for `i ∈ S`. -/
theorem G1_bp_mem (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {i : Fin 24} (hi : i ∈ S) :
    golayG1 i (bp β S) = bp β S + aG • bp β (S.erase i) := by
  rw [golayG1, Aut.mul_apply,
    rootExp_apply_of_Qscr_eq_zero golayN golayN_even golayN_posDef _ _ (Qm_bp_mem β hβ hS hi)]
  rw [rootExp_sq (golayRoot_norm i) _ (by
      rw [Qa_bp_mem β hβ hS hi, Qa_bp_not β hβ (hS hi) (Finset.notMem_erase i S)])]
  rw [Qa_bp_mem β hβ hS hi]

/-- `G_k` fixes the cube for `k ∉ D`. -/
theorem G1_bp_out (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) {k : Fin 24} (hk : k ∉ D) :
    golayG1 k (bp β S) = bp β S := by
  rw [golayG1, Aut.mul_apply,
    rootExp_apply_of_Qscr_eq_zero golayN golayN_even golayN_posDef _ _ (Qm_bp_out β hβ hS hk),
    rootExp_apply_of_Qscr_eq_zero golayN golayN_even golayN_posDef _ _ (Qa_bp_out β hβ hS hk)]

/-! ## §4  Product vectors on the cube -/

variable (D) in
/-- The coefficient of `b_S` in the product vector `⊗_i φ_i`. -/
def prodC (φ : Fin 24 → Fin 2 → ℂ) (S : Finset (Fin 24)) : ℂ :=
  ∏ i ∈ D, φ i (if i ∈ S then 1 else 0)

variable (D) in
/-- The product vector `⊗_{i ∈ D} φ_i = Σ_{S ⊆ D} (∏ φ_i(i ∈ S)) b_S`. -/
noncomputable def vecP (φ : Fin 24 → Fin 2 → ℂ) : LatModuleGen golayN :=
  ∑ S ∈ D.powerset, prodC D φ S • bp β S

theorem vecP_congr {φ ψ : Fin 24 → Fin 2 → ℂ} (h : ∀ i ∈ D, φ i = ψ i) : vecP β D φ = vecP β D ψ := by
  unfold vecP prodC
  exact Finset.sum_congr rfl fun S _ => by rw [Finset.prod_congr rfl fun i hi => by rw [h i hi]]

/-- The coefficient over `D ∖ i`. -/
def prodR (D : Finset (Fin 24)) (i : Fin 24) (φ : Fin 24 → Fin 2 → ℂ) (S : Finset (Fin 24)) : ℂ :=
  ∏ l ∈ D.erase i, φ l (if l ∈ S then 1 else 0)

theorem prodC_split {i : Fin 24} (hi : i ∈ D) (φ : Fin 24 → Fin 2 → ℂ) {S : Finset (Fin 24)}
    (hS : i ∉ S) :
    prodC D φ S = φ i 0 * prodR D i φ S ∧ prodC D φ (insert i S) = φ i 1 * prodR D i φ S := by
  constructor
  · rw [prodC, ← Finset.mul_prod_erase D _ hi, if_neg hS]; rfl
  · rw [prodC, ← Finset.mul_prod_erase D _ hi, if_pos (Finset.mem_insert_self i S)]
    congr 1
    exact Finset.prod_congr rfl fun l hl => by
      simp only [Finset.mem_insert, Finset.ne_of_mem_erase hl, false_or]

/-- Splitting the cube along the coordinate `i`. -/
theorem vecP_split {i : Fin 24} (hi : i ∈ D) (φ : Fin 24 → Fin 2 → ℂ) :
    vecP β D φ = ∑ S ∈ (D.erase i).powerset,
      prodR D i φ S • (φ i 0 • bp β S + φ i 1 • bp β (insert i S)) := by
  have hD : D = insert i (D.erase i) := (Finset.insert_erase hi).symm
  have hni : i ∉ D.erase i := Finset.notMem_erase i D
  unfold vecP
  conv_lhs => rw [hD, Finset.powerset_insert]
  rw [Finset.sum_union, Finset.sum_image, ← Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hiS : i ∉ S := fun h => hni (Finset.mem_powerset.mp hS h)
    rw [← hD]
    obtain ⟨h1, h2⟩ := prodC_split hi φ hiS
    rw [h1, h2, smul_add, smul_smul, smul_smul, mul_comm (φ i 0), mul_comm (φ i 1)]
  · intro S hS T hT h
    have hiS : i ∉ S := fun h' => hni (Finset.mem_powerset.mp hS h')
    have hiT : i ∉ T := fun h' => hni (Finset.mem_powerset.mp hT h')
    rw [← Finset.erase_insert hiS, ← Finset.erase_insert hiT, h]
  · rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS'
    exact hni (Finset.mem_powerset.mp hS (Finset.mem_insert_self i T))

theorem prodR_update {i : Fin 24} (φ : Fin 24 → Fin 2 → ℂ) (v : Fin 2 → ℂ) (S : Finset (Fin 24)) :
    prodR D i (Function.update φ i v) S = prodR D i φ S := by
  unfold prodR
  exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- The local matrix of `g = exp(aE) exp(bF)` on `(up, down)`. -/
noncomputable def gvec (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![(1 + aG * bG) * v 0 + aG * v 1, bG * v 0 + v 1]

/-- The inverse matrix. -/
noncomputable def ginv (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![v 0 - aG * v 1, -bG * v 0 + (1 + aG * bG) * v 1]

/-- The local sign `diag(1, −1)`. -/
def chivec (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![v 0, -v 1]

theorem gvec_ginv (v : Fin 2 → ℂ) : gvec (ginv v) = v := by
  funext l; fin_cases l <;> simp [gvec, ginv] <;> ring

/-- `G_i` acts on product vectors through the `i`-th factor. -/
theorem G1_vecP (hβ : gv β = ind D) {i : Fin 24} (hi : i ∈ D) (φ : Fin 24 → Fin 2 → ℂ) :
    golayG1 i (vecP β D φ) = vecP β D (Function.update φ i (gvec (φ i))) := by
  rw [vecP_split β hi, vecP_split β hi, aut_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSD : S ⊆ D.erase i := Finset.mem_powerset.mp hS
  have hiS : i ∉ S := fun h => Finset.notMem_erase i D (hSD h)
  have hS' : S ⊆ D := hSD.trans (Finset.erase_subset i D)
  have hins : insert i S ⊆ D := Finset.insert_subset hi hS'
  rw [prodR_update, Function.update_self, aut_smul, aut_add, aut_smul, aut_smul,
    G1_bp_not β hβ hS' hi hiS, G1_bp_mem β hβ hins (Finset.mem_insert_self i S),
    Finset.erase_insert hiS]
  simp only [gvec, Matrix.cons_val_zero, Matrix.cons_val_one]
  module

theorem G1_vecP_out (hβ : gv β = ind D) {k : Fin 24} (hk : k ∉ D) (φ : Fin 24 → Fin 2 → ℂ) :
    golayG1 k (vecP β D φ) = vecP β D φ := by
  unfold vecP
  rw [aut_sum]
  exact Finset.sum_congr rfl fun S hS => by
    rw [aut_smul, G1_bp_out β hβ (Finset.mem_powerset.mp hS) hk]

theorem listG_vecP (hβ : gv β = ind D) :
    ∀ (l : List (Fin 24)), l.Nodup → ∀ φ : Fin 24 → Fin 2 → ℂ,
      (l.map golayG1).prod (vecP β D φ)
        = vecP β D (fun m => if m ∈ l ∧ m ∈ D then gvec (φ m) else φ m)
  | [], _, φ => by simp
  | j :: l, hl, φ => by
      obtain ⟨hjl, hl'⟩ := List.nodup_cons.mp hl
      rw [List.map_cons, List.prod_cons, Aut.mul_apply, listG_vecP hβ l hl' φ]
      by_cases hj : j ∈ D
      · rw [G1_vecP β hβ hj]
        congr 1
        funext m
        by_cases hm : m = j
        · subst hm; simp [hj, hjl]
        · rw [Function.update_of_ne hm]; simp [hm]
      · rw [G1_vecP_out β hβ hj]
        congr 1
        funext m
        by_cases hm : m = j
        · subst hm; simp [hj]
        · simp [hm]

/-- `G = ∏_j G_j` acts on product vectors factorwise. -/
theorem golayG_vecP (hβ : gv β = ind D) (φ : Fin 24 → Fin 2 → ℂ) :
    golayG (vecP β D φ) = vecP β D (fun m => gvec (φ m)) := by
  rw [golayG, List.ofFn_eq_map, listG_vecP β hβ _ (List.nodup_finRange 24)]
  exact vecP_congr β fun i hi => by simp [hi]

theorem golayG_inv_vecP (hβ : gv β = ind D) (φ : Fin 24 → Fin 2 → ℂ) :
    golayG⁻¹ (vecP β D φ) = vecP β D (fun m => ginv (φ m)) := by
  have h := golayG_vecP β hβ (fun m => ginv (φ m))
  simp only [gvec_ginv] at h
  rw [← h, Aut.inv_apply_apply]

/-! ## §5  The momentum signs `χ`, `χ z₀` and `Θ = σχσ` on the cube -/

theorem sum_gv_sub (hβ : gv β = ind D) {S : Finset (Fin 24)} (_hS : S ⊆ D) :
    ∑ l, gv (β - dl S) l = (D.card : ℤ) - 2 * S.card := by
  simp only [gv_sub_dl β hβ, Finset.sum_sub_distrib, ← Finset.mul_sum, ind, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem chiSign_parity_cube (hβ : gv β = ind D) (h4 : 4 ∣ D.card) {S : Finset (Fin 24)} (hS : S ⊆ D) :
    chiSign golayN golayParity (β - dl S) = (-1 : ℂ) ^ S.card := by
  have hsum := sum_gv_sub β hβ hS
  obtain ⟨m, hm⟩ := h4
  rcases Nat.even_or_odd S.card with he | ho
  · rw [he.neg_one_pow]
    apply chiSign_of_eq_zero
    rw [golayParity_eq_zero_iff]
    change (4 : ℤ) ∣ ∑ l, gv (β - dl S) l
    rw [hsum, hm]
    obtain ⟨r, hr⟩ := he
    rw [hr]; push_cast; exact ⟨m - r, by ring⟩
  · rw [ho.neg_one_pow]
    apply chiSign_of_ne_zero
    rw [Ne, golayParity_eq_zero_iff]
    change ¬ (4 : ℤ) ∣ ∑ l, gv (β - dl S) l
    rw [hsum, hm]
    obtain ⟨r, hr⟩ := ho
    rw [hr]; push_cast; omega

theorem chiSign_coord_cube (hβ : gv β = ind D) {S : Finset (Fin 24)} (hS : S ⊆ D) :
    chiSign golayN (golayCoord 0) (β - dl S) = if (0 : Fin 24) ∈ D then -1 else 1 := by
  have h := gv_sub_dl β hβ S 0
  split_ifs with h0
  · apply chiSign_of_ne_zero
    change (((gv (β - dl S) 0 : ℤ)) : ZMod 2) ≠ 0
    rw [h]
    by_cases h0S : (0 : Fin 24) ∈ S
    · simp [ind, h0, h0S]
    · simp [ind, h0, h0S]
  · apply chiSign_of_eq_zero
    change (((gv (β - dl S) 0 : ℤ)) : ZMod 2) = 0
    rw [h]
    have h0S : (0 : Fin 24) ∉ S := fun h' => h0 (hS h')
    simp [ind, h0, h0S]

theorem golayChi_bp (hβ : gv β = ind D) (h4 : 4 ∣ D.card) {S : Finset (Fin 24)} (hS : S ⊆ D) :
    golayChi (bp β S) = (-1 : ℂ) ^ S.card • bp β S := by
  rw [bp, aut_smul, smul_comm]
  congr 1
  show chiLat golayN golayParity (latStateGen golayN _ _) = _
  rw [chiLat_latStateGen, chiSign_parity_cube β hβ h4 hS]; rfl

/-- The global sign of `χ z₀` on the cube. -/
def cD (D : Finset (Fin 24)) : ℂ := if (0 : Fin 24) ∈ D then -1 else 1

theorem cD_mul_self (D : Finset (Fin 24)) : cD D * cD D = 1 := by
  unfold cD; split_ifs <;> norm_num

theorem golayChiMod_bp (hβ : gv β = ind D) (h4 : 4 ∣ D.card) {S : Finset (Fin 24)} (hS : S ⊆ D) :
    golayChiMod (bp β S) = (cD D * (-1 : ℂ) ^ S.card) • bp β S := by
  rw [bp, aut_smul, smul_comm]
  congr 1
  show chiLat golayN _ (latStateGen golayN _ _) = _
  rw [chiLat_latStateGen]
  congr 1
  rw [chiSign, AddMonoidHom.add_apply, Extraspecial.sgn_add, ← chiSign, ← chiSign,
    chiSign_parity_cube β hβ h4 hS, chiSign_coord_cube β hβ hS, cD, mul_comm]

theorem prodC_chivec {φ : Fin 24 → Fin 2 → ℂ} {S : Finset (Fin 24)} (hS : S ⊆ D) :
    prodC D (fun m => chivec (φ m)) S = (-1 : ℂ) ^ S.card * prodC D φ S := by
  unfold prodC
  have h : ∀ i ∈ D, chivec (φ i) (if i ∈ S then 1 else 0)
      = (if i ∈ S then (-1 : ℂ) else 1) * φ i (if i ∈ S then 1 else 0) := by
    intro i _; by_cases hi : i ∈ S <;> simp [chivec, hi]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

theorem golayChi_vecP (hβ : gv β = ind D) (h4 : 4 ∣ D.card) (φ : Fin 24 → Fin 2 → ℂ) :
    golayChi (vecP β D φ) = vecP β D (fun m => chivec (φ m)) := by
  unfold vecP
  rw [aut_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS' := Finset.mem_powerset.mp hS
  rw [aut_smul, golayChi_bp β hβ h4 hS', smul_smul, prodC_chivec hS', mul_comm]

theorem golayChiMod_vecP (hβ : gv β = ind D) (h4 : 4 ∣ D.card) (φ : Fin 24 → Fin 2 → ℂ) :
    golayChiMod (vecP β D φ) = cD D • vecP β D (fun m => chivec (φ m)) := by
  unfold vecP
  rw [aut_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hS' := Finset.mem_powerset.mp hS
  rw [aut_smul, golayChiMod_bp β hβ h4 hS', smul_smul, smul_smul, prodC_chivec hS']
  congr 1; ring

theorem golaySigma_vecP (hβ : gv β = ind D) (h4 : 4 ∣ D.card) (φ : Fin 24 → Fin 2 → ℂ) :
    golaySigma (vecP β D φ) = cD D • vecP β D (fun m => gvec (chivec (ginv (φ m)))) := by
  rw [golaySigma, Aut.mul_apply, Aut.mul_apply, golayG_inv_vecP β hβ, golayChiMod_vecP β hβ h4,
    aut_smul, golayG_vecP β hβ]

/-- **`Θ = σχσ` on the cube is the tensor power of a `2 × 2` matrix.** -/
theorem golayTheta_vecP (hβ : gv β = ind D) (h4 : 4 ∣ D.card) (φ : Fin 24 → Fin 2 → ℂ) :
    golayTheta (vecP β D φ) = vecP β D (fun m =>
      gvec (chivec (ginv (chivec (gvec (chivec (ginv (φ m)))))))) := by
  rw [golayTheta, Aut.mul_apply, Aut.mul_apply, golaySigma_vecP β hβ h4, aut_smul,
    golayChi_vecP β hβ h4, aut_smul, golaySigma_vecP β hβ h4, smul_smul, cD_mul_self, one_smul]

/-! ## §6  `Θ e^β = ξ(1_D) e^{−β}` -/

theorem vecP_up : vecP β D (fun _ => ![1, 0]) = latChargeGen golayN β := by
  unfold vecP
  rw [Finset.sum_eq_single ∅, ← bp_empty β]
  · unfold prodC; simp
  · intro S hS hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [prodC, Finset.prod_eq_zero (Finset.mem_powerset.mp hS hi) (by simp [hi]), zero_smul]
  · intro h; exact absurd (Finset.empty_mem_powerset D) h

theorem vecP_down : vecP β D (fun _ => ![0, 1]) = bp β D := by
  unfold vecP
  rw [Finset.sum_eq_single D]
  · unfold prodC
    rw [Finset.prod_congr rfl fun i hi => by rw [if_pos hi]]
    simp
  · intro S hS hne
    have hss : S ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hS, hne⟩
    obtain ⟨i, hiD, hiS⟩ := Finset.exists_of_ssubset hss
    rw [prodC, Finset.prod_eq_zero hiD (by simp [hiS]), zero_smul]
  · intro h; exact absurd (Finset.mem_powerset_self D) h

theorem sqrt2_mul_self' : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The `2 × 2` computation: `Θ₁ (1,0) = (0,1)`. -/
theorem theta_local :
    gvec (chivec (ginv (chivec (gvec (chivec (ginv ![1, 0])))))) = ![0, 1] := by
  have hs := sqrt2_mul_self'
  set r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr
  funext l
  fin_cases l
  · simp [gvec, ginv, chivec, aG, bG]
    push_cast
    rw [← hr]
    linear_combination ((1 / 2 : ℂ) * r ^ 2 - r - 1 / 2) * hs
  · simp [gvec, ginv, chivec, aG, bG]
    push_cast
    rw [← hr]
    linear_combination ((1 / 2 : ℂ) - (1 / 2 : ℂ) * r) * hs

theorem dl_full (hβ : gv β = ind D) : dl D = β + β := by
  apply Subtype.ext
  change gv (dl D) = gv β + gv β
  rw [dl, gv_phiR, hβ, two_smul]

/-- **`Θ` on a codeword state**: `Θ e^β = ξ(1_D) e^{−β}` for `β = 1_D` (`4 ∣ |D|`). -/
theorem golayTheta_codeword (hβ : gv β = ind D) (h4 : 4 ∣ D.card) :
    golayTheta (latChargeGen golayN β) = xi (ind D) • latChargeGen golayN (-β) := by
  rw [← vecP_up β, golayTheta_vecP β hβ h4]
  simp only [theta_local]
  rw [vecP_down, bp, nuC, dl_full β hβ, show β - (β + β) = -β by abel]
  congr 1
  obtain ⟨m, hm⟩ := h4
  rw [hm, pow_mul, Complex.I_pow_four, one_pow, inv_one, mul_one]
  have h := εN_sq β β
  simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right] at h ⊢
  linear_combination (xi (ind D)) * (latticeCocycle golayN β β ^ 4 + latticeCocycle golayN β β ^ 2 + 1) * h

end VOA.Moonshine.SigmaTop
