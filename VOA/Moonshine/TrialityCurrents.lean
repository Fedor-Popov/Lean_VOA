/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TrialityGolay
import VOA.Moonshine.TrialitySl2

/-!
# The triality `σ` on the `su(2)²⁴` currents, and `σ₀ ≠ 1`  (Moonshine step M8g)

This file evaluates `golaySigma = G (χ z₀) G⁻¹` (`TrialityGolay.lean`) on the weight-one
currents of `V_{N(A₁²⁴)}`.  In coordinate `j`, with `e = e^{α_j}`, `h = α_j(−1)𝟙`,
`f = e^{−α_j}` and `ε_j = ε(α_j,−α_j)`:

  `σ h = e + ε_j f`     (`golaySigma_hSt`),      `σ (e + ε_j f) = h`,

i.e. `σ` exchanges the Heisenberg (Cartan) current with the `e+f` current — DGM (7.7),
`J^{j1} ↔ J^{j2}`.  The proof is the `SL₂` computation of `TrialityGolay`'s docstring made
exact: with `y = (2−2√2) e + (√2/2) h − ε(1+√2)/4 f` and
`y' = (2√2−2) e + (√2/2) h + ε(1+√2)/4 f` one has `G y = h`, `G y' = e + εf` and
`χ z₀ y = y'` (all coefficient identities are certified modulo `(√2)² = 2`, `ε² = 1`).

Consequences:
* `golayTheta_hSt : Θ h = −h` — `Θ = σχσ` acts as `−1` on the Cartan currents (the first half of
  "`Θ` is a lift of `−1`");
* `golaySigma0_ne_one : golaySigma0 ≠ 1` — the state `x = h₀₍₋₁₎h₁ ∈ V_N^{⟨χ,Θ⟩}` is moved:
  `σx = (e₀+ε₀f₀)₍₋₁₎(e₁+ε₁f₁)` has charge-`(α₀+α₁)` component `ε(α₀,α₁) e^{α₀+α₁} ≠ 0`.

## Status
`sorry`-free, no new axioms.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.Triality

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN VOA.LatGen.Screen

/-! ## §1  Products of automorphisms over `Fin n` acting on a set fixed by all but one factor -/

section ListProd

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem ofFn_prod_apply_of_fix {n : ℕ} (f : Fin n → Aut W) (S : Set 𝒱)
    (hfix : ∀ k, ∀ x ∈ S, f k x = x) : ∀ x ∈ S, (List.ofFn f).prod x = x := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [List.ofFn_succ, List.prod_cons, Aut.mul_apply,
      ih (fun i => f i.succ) (fun k => hfix k.succ) x hx, hfix 0 x hx]

theorem ofFn_prod_apply_single {n : ℕ} (f : Fin n → Aut W) (S : Set 𝒱) (j : Fin n)
    (hfix : ∀ k, k ≠ j → ∀ x ∈ S, f k x = x) (hpres : ∀ x ∈ S, f j x ∈ S) :
    ∀ x ∈ S, (List.ofFn f).prod x = f j x := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    intro x hx
    rw [List.ofFn_succ, List.prod_cons, Aut.mul_apply]
    induction j using Fin.cases with
    | zero =>
      rw [ofFn_prod_apply_of_fix (fun i => f i.succ) S
        (fun k y hy => hfix k.succ (Fin.succ_ne_zero k) y hy) x hx]
    | succ j' =>
      rw [ih (fun i => f i.succ) j' (fun k hk y hy => hfix k.succ (by simpa using hk) y hy)
        hpres x hx]
      exact hfix 0 (Fin.succ_ne_zero j').symm _ (hpres x hx)

end ListProd

/-! ## §2  `G` on the `j`-th triple -/

theorem golayRoot_orth {j k : Fin 24} (h : j ≠ k) : golayN.form (golayRoot j) (golayRoot k) = 0 := by
  rw [golayRoot_form, if_neg h]

theorem golayRoot_orth_neg {j k : Fin 24} (h : j ≠ k) :
    golayN.form (golayRoot j) (-golayRoot k) = 0 := by
  rw [map_neg, golayRoot_orth h, neg_zero]

/-- The `j`-th current triple `x₁ e^{α_j} + x₂ α_j(−1)𝟙 + x₃ e^{−α_j}`. -/
noncomputable abbrev tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) : LatModuleGen golayN :=
  vec3 golayN (golayRoot j) x₁ x₂ x₃

/-- The set of `j`-th triples. -/
def triSet (j : Fin 24) : Set (LatModuleGen golayN) := {v | ∃ x₁ x₂ x₃, v = tri j x₁ x₂ x₃}

theorem golayG1_tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    golayG1 j (tri j x₁ x₂ x₃) =
      let c := ((Real.sqrt 2 / 4 : ℝ) : ℂ) * golayEps j
      let a := ((1 - Real.sqrt 2 : ℝ) : ℂ)
      let e := golayEps j
      let N₁ := x₁
      let N₂ := x₂ - c * e * x₁
      let N₃ := x₃ + 2 * c * x₂ - c ^ 2 * e * x₁
      tri j (N₁ - 2 * a * N₂ - a ^ 2 * e * N₃) (N₂ + a * e * N₃) N₃ := by
  simp only [golayG1, Aut.mul_apply, tri]
  rw [rootExp_vec3_neg golayN golayN_posDef golayN_even (golayRoot_norm j) (golayRoot_neg_norm j),
    rootExp_vec3_pos golayN golayN_posDef golayN_even (golayRoot_norm j)]
  rfl

theorem golayG1_tri_orth {j k : Fin 24} (h : k ≠ j) (x₁ x₂ x₃ : ℂ) :
    golayG1 k (tri j x₁ x₂ x₃) = tri j x₁ x₂ x₃ := by
  simp only [golayG1, Aut.mul_apply, tri]
  rw [rootExp_vec3_orth golayN golayN_posDef golayN_even (golayRoot_neg_norm k)
      (golayRoot_orth_neg h.symm),
    rootExp_vec3_orth golayN golayN_posDef golayN_even (golayRoot_norm k) (golayRoot_orth h.symm)]

theorem golayG_tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    golayG (tri j x₁ x₂ x₃) = golayG1 j (tri j x₁ x₂ x₃) := by
  refine ofFn_prod_apply_single golayG1 (triSet j) j ?_ ?_ _ ⟨x₁, x₂, x₃, rfl⟩
  · rintro k hk _ ⟨y₁, y₂, y₃, rfl⟩
    exact golayG1_tri_orth hk y₁ y₂ y₃
  · rintro _ ⟨y₁, y₂, y₃, rfl⟩
    rw [golayG1_tri]
    exact ⟨_, _, _, rfl⟩

/-! ## §3  The explicit preimages and `σ h = e + εf` -/

theorem golayEps_sq (j : Fin 24) : golayEps j ^ 2 = 1 := by
  rw [pow_two]; exact latticeCocycle_sq _ _ _

theorem sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `y = (2−2√2) e + (√2/2) h − ε(1+√2)/4 f`, with `G y = h`. -/
noncomputable def yPre (j : Fin 24) : LatModuleGen golayN :=
  tri j (2 - 2 * (Real.sqrt 2 : ℂ)) ((Real.sqrt 2 : ℂ) / 2)
    (-(golayEps j) * (1 + (Real.sqrt 2 : ℂ)) / 4)

/-- `y' = (2√2−2) e + (√2/2) h + ε(1+√2)/4 f`, with `G y' = e + εf`. -/
noncomputable def yPre' (j : Fin 24) : LatModuleGen golayN :=
  tri j (2 * (Real.sqrt 2 : ℂ) - 2) ((Real.sqrt 2 : ℂ) / 2)
    (golayEps j * (1 + (Real.sqrt 2 : ℂ)) / 4)

theorem golayG_yPre (j : Fin 24) : golayG (yPre j) = tri j 0 1 0 := by
  rw [yPre, golayG_tri, golayG1_tri]
  have hs := sqrt2_sq
  have he := golayEps_sq j
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hsdef
  set e := golayEps j with hedef
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [← hsdef]
  apply vec3_congr
  · linear_combination (-(e^4*s^3 - 3*e^4*s^2 + 5*e^4*s - 7*e^4 + 2*e^2*s^2 - 14*e^2*s + 24*e^2 - 8)/8) * hs + (-(5*e^2*s - 7*e^2 - 12*s + 16)/4) * he
  · linear_combination (-e^2*(e^2*s^2 - 2*e^2*s + 3*e^2 + 2*s - 8)/8) * hs + ((2*e^2*s - 3*e^2 - 2*s + 4)/4) * he
  · linear_combination (e*(e^2*s - e^2 + 2)/8) * hs + (e*(s - 1)/4) * he

theorem golayG_yPre' (j : Fin 24) : golayG (yPre' j) = tri j 1 0 (golayEps j) := by
  rw [yPre', golayG_tri, golayG1_tri]
  have hs := sqrt2_sq
  have he := golayEps_sq j
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hsdef
  set e := golayEps j with hedef
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [← hsdef]
  apply vec3_congr
  · linear_combination ((e^4*s^3 - 3*e^4*s^2 + 5*e^4*s - 7*e^4 - 2*e^2*s^2 - 6*e^2*s + 12*e^2 + 8)/8) * hs + ((5*e^2*s - 7*e^2 - 4*s + 4)/4) * he
  · linear_combination (e^2*(e^2*s^2 - 2*e^2*s + 3*e^2 - 2*s - 4)/8) * hs + (-(2*e^2*s - 3*e^2 + 2*s)/4) * he
  · linear_combination (-e*(e^2*s - e^2 - 2)/8) * hs + (-e*(s - 1)/4) * he

theorem chiSign_mod_root (j : Fin 24) :
    chiSign golayN (golayParity + golayCoord 0) (golayRoot j) = -1 := by
  apply chiSign_of_ne_zero
  rw [AddMonoidHom.add_apply, golayParity_root, golayCoord_root, add_zero]; exact one_ne_zero

theorem chiSign_parity_root (j : Fin 24) : chiSign golayN golayParity (golayRoot j) = -1 := by
  apply chiSign_of_ne_zero
  rw [golayParity_root]; exact one_ne_zero

theorem golayChiMod_tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    golayChiMod (tri j x₁ x₂ x₃) = tri j (-x₁) x₂ (-x₃) := by
  show chiLat golayN _ (vec3 golayN _ _ _ _) = _
  rw [chiLat_vec3, chiSign_mod_root]; simp [tri]

theorem golayChi_tri (j : Fin 24) (x₁ x₂ x₃ : ℂ) :
    golayChi (tri j x₁ x₂ x₃) = tri j (-x₁) x₂ (-x₃) := by
  show chiLat golayN _ (vec3 golayN _ _ _ _) = _
  rw [chiLat_vec3, chiSign_parity_root]; simp [tri]

theorem golayChiMod_yPre (j : Fin 24) : golayChiMod (yPre j) = yPre' j := by
  rw [yPre, golayChiMod_tri, yPre']
  apply vec3_congr <;> ring

theorem hSt_eq_tri (j : Fin 24) : hSt golayN (golayRoot j) = tri j 0 1 0 := by
  simp [tri, vec3]

theorem Aut.inv_apply_apply {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (g : Aut W) (x : 𝒱) : g⁻¹ (g x) = x := by
  rw [Aut.inv_apply]; exact g.toLinearEquiv.symm_apply_apply x

/-- **DGM (7.7) on the Cartan current**: `σ (α_j(−1)𝟙) = e^{α_j} + ε_j e^{−α_j}`. -/
theorem golaySigma_hSt (j : Fin 24) :
    golaySigma (hSt golayN (golayRoot j)) = tri j 1 0 (golayEps j) := by
  rw [hSt_eq_tri, ← golayG_yPre, golaySigma, Aut.mul_apply, Aut.mul_apply, Aut.inv_apply_apply,
    golayChiMod_yPre, golayG_yPre']

/-- `σ (e^{α_j} + ε_j e^{−α_j}) = α_j(−1)𝟙`. -/
theorem golaySigma_tri_ef (j : Fin 24) :
    golaySigma (tri j 1 0 (golayEps j)) = hSt golayN (golayRoot j) := by
  rw [← golaySigma_hSt, ← Aut.mul_apply, golaySigma_sq, Aut.one_apply]

/-- `Θ = σχσ` acts by `−1` on the Cartan currents. -/
theorem golayTheta_hSt (j : Fin 24) :
    golayTheta (hSt golayN (golayRoot j)) = -hSt golayN (golayRoot j) := by
  rw [golayTheta, Aut.mul_apply, Aut.mul_apply, golaySigma_hSt, golayChi_tri]
  have h : tri j (-1) 0 (-golayEps j) = -tri j 1 0 (golayEps j) := by
    rw [tri, tri, vec3_neg]; simp
  rw [h]
  show golaySigma.toLinearEquiv (-_) = _
  rw [map_neg, Aut.coe_toLinearEquiv, golaySigma_tri_ef]

/-! ## §4  `σ₀ ≠ 1` -/

/-- The witness `x = α₀(−1)𝟙 ₍₋₁₎ α₁(−1)𝟙`. -/
noncomputable def xWit : LatModuleGen golayN :=
  golayVOA.smul (hSt golayN (golayRoot 0)) (-1) (hSt golayN (golayRoot 1))

theorem hSt_mem_chargeSec (α : golayN.carrier) : hSt golayN α ∈ chargeSec golayN 0 :=
  mem_chargeSec golayN 0 _

theorem xWit_mem_chargeSec : xWit ∈ chargeSec golayN 0 :=
  chargeSec_zero_smul_mem golayN golayN_even golayN_posDef (hSt_mem_chargeSec _) (-1)
    (hSt_mem_chargeSec _)

theorem golayChi_fix_chargeSec_zero {x : LatModuleGen golayN} (hx : x ∈ chargeSec golayN 0) :
    golayChi x = x := by
  obtain ⟨p, rfl⟩ := hx
  show chiLat golayN golayParity (mkEα golayN 0 p) = mkEα golayN 0 p
  rw [chiLat_mkEα, chiSign_zero, one_smul]

theorem golayTheta_xWit : golayTheta xWit = xWit := by
  rw [xWit, Aut.map_smul, golayTheta_hSt, golayTheta_hSt,
    ← neg_one_smul ℂ (hSt golayN (golayRoot 0)), ← neg_one_smul ℂ (hSt golayN (golayRoot 1)),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right, smul_smul]
  norm_num

theorem xWit_mem_golayV0 : xWit ∈ (orbifold golayK).carrier := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => g xWit = xWit) ?_ ?_ ?_ ?_ hg
  · rintro g (rfl | rfl)
    · exact golayChi_fix_chargeSec_zero xWit_mem_chargeSec
    · exact golayTheta_xWit
  · rfl
  · intro a b _ _ ha hb
    rw [Aut.mul_apply, hb, ha]
  · intro a _ ha
    calc a⁻¹ xWit = a⁻¹ (a xWit) := by rw [ha]
      _ = xWit := Aut.inv_apply_apply a xWit

theorem coordEα_of_mem_chargeSec {μ ν : golayN.carrier} (h : μ ≠ ν) {x : LatModuleGen golayN}
    (hx : x ∈ chargeSec golayN ν) : coordEα golayN μ x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  rw [mkEα_apply, coordEα_apply, if_neg h]

theorem smul_mem_chargeSec {α β : golayN.carrier} {u v : LatModuleGen golayN}
    (hu : u ∈ chargeSec golayN α) (hv : v ∈ chargeSec golayN β) (n : ℤ) :
    golayVOA.smul u n v ∈ chargeSec golayN (α + β) :=
  YfullGen_shiftsCharge golayN golayN_even golayN_posDef α hu β (-n - 1) v hv

theorem gv_golayRoot_apply (j i : Fin 24) : gv (golayRoot j) i = if i = j then 2 else 0 := by
  rw [golayRoot_coe, Pi.smul_apply, Pi.single_apply]; split_ifs <;> simp

theorem ne_of_gv {a b : golayN.carrier} (i : Fin 24) (h : gv a i ≠ gv b i) : a ≠ b :=
  fun hab => h (by rw [hab])

theorem charge_ne1 : golayRoot 0 + golayRoot 1 ≠ golayRoot 0 + -golayRoot 1 :=
  ne_of_gv 1 (by simp only [gv_add, gv_neg, Pi.add_apply, Pi.neg_apply, gv_golayRoot_apply]; decide)

theorem charge_ne2 : golayRoot 0 + golayRoot 1 ≠ -golayRoot 0 + golayRoot 1 :=
  ne_of_gv 0 (by simp only [gv_add, gv_neg, Pi.add_apply, Pi.neg_apply, gv_golayRoot_apply]; decide)

theorem charge_ne3 : golayRoot 0 + golayRoot 1 ≠ -golayRoot 0 + -golayRoot 1 :=
  ne_of_gv 0 (by simp only [gv_add, gv_neg, Pi.add_apply, Pi.neg_apply, gv_golayRoot_apply]; decide)

theorem charge_ne0 : golayRoot 0 + golayRoot 1 ≠ 0 :=
  ne_of_gv 0 (by simp only [gv_add, Pi.add_apply, gv_golayRoot_apply]; decide)

theorem latStateGen_one_ne_zero (γ : golayN.carrier) : latChargeGen golayN γ ≠ 0 :=
  latChargeGen_ne_zero' γ

/-- The charge-`(α₀+α₁)` component of `σ x`. -/
theorem coordEα_sigma_xWit :
    coordEα golayN (golayRoot 0 + golayRoot 1) (golaySigma xWit)
      = latticeCocycle golayN (golayRoot 0) (golayRoot 1) • (1 : FockN (rank golayN)) := by
  rw [xWit, Aut.map_smul, golaySigma_hSt, golaySigma_hSt]
  simp only [tri, vec3, zero_smul, add_zero, one_smul, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    map_add, map_smul]
  have hP : ∀ γ : golayN.carrier, latChargeGen golayN γ ∈ chargeSec golayN γ :=
    fun γ => mem_chargeSec golayN γ _
  have z1 := coordEα_of_mem_chargeSec charge_ne1
    (smul_mem_chargeSec (hP (golayRoot 0)) (hP (-golayRoot 1)) (-1))
  have z2 := coordEα_of_mem_chargeSec charge_ne2
    (smul_mem_chargeSec (hP (-golayRoot 0)) (hP (golayRoot 1)) (-1))
  have z3 := coordEα_of_mem_chargeSec charge_ne3
    (smul_mem_chargeSec (hP (-golayRoot 0)) (hP (-golayRoot 1)) (-1))
  rw [z1, z2, z3]
  -- the main term `e^{α₀}₍₋₁₎ e^{α₁}`
  have hmain : golayVOA.smul (latChargeGen golayN (golayRoot 0)) (-1) (latChargeGen golayN (golayRoot 1))
      = latticeCocycle golayN (golayRoot 0) (golayRoot 1) •
          latChargeGen golayN (golayRoot 0 + golayRoot 1) := by
    have h := Qscr_eq_mode_YfullGen golayN golayN_even golayN_posDef (golayRoot 0)
    have hY : YfullGen golayN golayN_even golayN_posDef (latChargeGen golayN (golayRoot 0))
        = Yeαvec golayN (golayRoot 0) := by
      have hw := YfullGen_word golayN golayN_even golayN_posDef [] (golayRoot 0)
      rwa [wordStateLatGen_nil, YwordLatGen_nil] at hw
    show mode (YfullGen golayN golayN_even golayN_posDef _) (-1) _ = _
    rw [hY, mode_apply, show (-(-1 : ℤ) - 1) = 0 by norm_num, latChargeGen, Yeαvec_tmul,
      golayRoot_orth (by decide : (0 : Fin 24) ≠ 1), sub_zero, EEVec_vacuum, if_pos le_rfl,
      show (0 : ℤ).toNat = 0 from rfl, vSchur_zero]
    rfl
  rw [hmain, map_smul, latChargeGen, latStateGen, coordEα_apply, if_pos rfl]
  simp [vacuumN]

theorem golaySigma_xWit_ne : golaySigma xWit ≠ xWit := by
  intro h
  have h1 := coordEα_sigma_xWit
  rw [h, coordEα_of_mem_chargeSec (ν := 0) charge_ne0 xWit_mem_chargeSec] at h1
  have hε : latticeCocycle golayN (golayRoot 0) (golayRoot 1) ≠ 0 := by
    intro h0; have := latticeCocycle_sq golayN (golayRoot 0) (golayRoot 1); rw [h0] at this; simp at this
  have h2 := h1.symm
  rw [smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hε h2
  · exact one_ne_zero h2

/-- **`σ₀ ≠ 1`**: the triality is a nontrivial involution of `V_N^{⟨χ,Θ⟩}`. -/
theorem golaySigma0_ne_one : golaySigma0 ≠ 1 := by
  intro h
  apply golaySigma_xWit_ne
  have := congrArg (fun g : Aut golayV0 => ((g ⟨xWit, xWit_mem_golayV0⟩ :
    (orbifold golayK).carrier) : LatModuleGen golayN)) h
  simpa [golaySigma0_coe] using this

end VOA.Moonshine.Triality
