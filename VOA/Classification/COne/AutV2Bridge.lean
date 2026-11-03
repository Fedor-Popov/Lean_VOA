/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.V2PlusV8
import VOA.Classification.COne.FiniteRotationGroups
import VOA.Classification.COne.Inputs

/-!
# The bridge `Aut V₂ → SO(3, ℂ)` and the finite orbifolds of `V₂`

Every finite orbifold `V₂^G` is in the list of Gannon–Rayhaun Theorem 3.1 (the `m = 1` half of
the enumeration input, GR Prop. C.4). With the `m ≥ 2` half (`AutV2m.lean`) this proves
`IEnumeration` (`Inputs.lean`) outright.

## Main results
* `V2_grading_one`: `(V₂)₁ = span(e^α, h, e^{−α})`; `br_xyz`: in the orthonormal coordinates
  `X = e + εf`, `Y = i(e − εf)`, `Z = h` the bracket `u₍₀₎v` is `−2i` times the cross product.
* `rho : Aut V₂ →* M₃(ℂ)`, the action on `(V₂)₁`; `rho_transpose_mul`, `rho_det` (image in
  `SO(3, ℂ)`: a matrix preserving the cross product, `orth_of_cross`), `rho_injective`
  (rigidity `aut_eq_one_of_fix`).
* `exists_aut_xyzL_eq_h` (transitivity): every unit vector of `(V₂)₁` is moved to `h` by a
  product of root exponentials and `θ`. Hence `exists_conj_charU`: every finite-order
  automorphism is conjugate to a torus element `g_u` (its axis is anisotropic,
  `exists_fixed_unit`), and automorphisms sending `h ↦ ±h` normalize the torus.
* `inNormalizer_conj_of_isCyclic`, `inNormalizer_conj_of_dihedral`, `inNormalizer_conj_of_axis`:
  cyclic, dihedral (`n ≥ 2`) and axis-preserving finite subgroups are conjugate into the torus
  normalizer, whose orbifolds are in the list (`inCOneList_orbifold_V2_normalizer_all`, C7c).
* `SO3C.so3c_dichotomy` (unitary trick): a finite group of complex-orthogonal determinant-one
  `3 × 3` matrices either preserves an anisotropic axis up to sign, or embeds in `SO(3, ℝ)`.
  Proof: average a Hermitian form `H`; `A = H̄H` commutes with the group. If `A` is not scalar,
  an eigenspace gives an invariant line `ℂv`; if `v` is isotropic, `conj(Hv)` spans a second
  invariant isotropic line and `v × conj(Hv)` an anisotropic one. If `A = μ` (then `μ > 0`),
  `J x = conj(μ^{-1/2} H x)` is an invariant antilinear involution, and an orthonormal frame of
  its fixed vectors conjugates the group into `SO(3, ℝ)`.
* `enumeration_m1`: for every finite `G ≤ Aut V₂`, `InCOneList (V₂^G)`: either the axis case,
  or `FiniteRotation.classification` makes `G` cyclic, dihedral (conjugate into the normalizer)
  or `A₄`, `S₄`, `A₅` (then `V₂^G` is literally the corresponding list entry, with `G` itself).
* `iEnumeration : IEnumeration`.

No conjugacy of isomorphic subgroups of `SO(3, ℝ)` is needed: the exceptional clauses of
`InCOneList` are existential in the subgroup.

## Status
`sorry`-free, no new axioms. Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN MvPolynomial Complex

/-! ## The weight-one space of `V₂` -/

section WeightOne

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- A Fock state of weight `0` is a constant. -/
theorem fock_weight_zero {r : ℕ} {p : FockN r} (hp : p ∈ gradingWN r 0) :
    p = (coeff 0 p) • vacuumN r := by
  ext d
  rw [vacuumN, coeff_smul, coeff_one, smul_eq_mul]
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg (Ne.symm hd), mul_zero]
    by_contra hc
    have hw : Finsupp.weight weightFnN d = 0 := hp hc
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd
    have := Finsupp.le_weight_of_ne_zero' weightFnN (show d i ≠ 0 from hi)
    rw [hw, weightFnN_apply] at this
    omega

theorem halfNorm_latP1 (v : (latP 1).carrier) :
    VOA.LatGen.halfNorm (latP 1) v = ci 1 v * ci 1 v := by
  rw [VOA.LatGen.halfNorm, latP_form]
  change 2 * ((1 : ℕ) : ℤ) * ci 1 v * ci 1 v / 2 = ci 1 v * ci 1 v
  rw [show 2 * ((1 : ℕ) : ℤ) * ci 1 v * ci 1 v = 2 * (ci 1 v * ci 1 v) by push_cast; ring]
  omega

/-- The span of `e^α, h, e^{−α}`, as the set of `vec3` vectors. -/
def v3Sub : Submodule ℂ (LatModuleGen (latP 1)) where
  carrier := {y | ∃ x₁ x₂ x₃ : ℂ, y = vec3 (latP 1) (a1 1) x₁ x₂ x₃}
  add_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', vec3_add (latP 1) (a1 1) a b c a' b' c'⟩
  zero_mem' := ⟨0, 0, 0, (vec3_zero _ _).symm⟩
  smul_mem' := by
    rintro t _ ⟨a, b, c, rfl⟩
    exact ⟨t * a, t * b, t * c, vec3_smul (latP 1) (a1 1) t a b c⟩

theorem mem_v3Sub {y : LatModuleGen (latP 1)} :
    y ∈ v3Sub ↔ ∃ x₁ x₂ x₃ : ℂ, y = vec3 (latP 1) (a1 1) x₁ x₂ x₃ := Iff.rfl

/-- **The weight-one space of `V₂`** is spanned by `e^α`, `h = α(−1)𝟙`, `e^{−α}`. -/
theorem V2_grading_one {x : LatModuleGen (latP 1)} (hx : x ∈ (V1).grading 1) :
    ∃ x₁ x₂ x₃ : ℂ, x = vec3 (latP 1) (a1 1) x₁ x₂ x₃ := by
  set S := v3Sub
  have hx' : x ∈ gradingLatGen (latP 1) 1 := hx
  suffices hle : gradingLatGen (latP 1) 1 ≤ S from mem_v3Sub.mp (hle hx')
  refine iSup_le (fun α => ?_)
  have hn := halfNorm_latP1 α
  by_cases h0 : ci 1 α = 0
  · have hα : α = 0 := h0
    subst hα
    rw [halfNorm_zero (latP 1), sub_zero]
    rintro _ ⟨q, hq, rfl⟩
    rw [gradingZN_of_nonneg (by norm_num)] at hq
    have hq' := fock_weight_one_mem_span hq
    have hspan : (Submodule.span ℂ (Set.range fun a : Fin (rank (latP 1)) => (X ((0 : ℕ), a) :
        FockN (rank (latP 1))))).map (mkEα (latP 1) 0) ≤ S := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      rw [← heisSt_eq_mkEα]
      have h1 := heisSt_mem_span_hSt (latP 1) (latP_posDef 1 le_rfl) a
      have h2 : Submodule.span ℂ (Set.range (hSt (latP 1))) ≤ S := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        rw [hSt_int 1 k]
        exact mem_v3Sub.mpr ⟨0, (ci 1 k : ℂ), 0, by simp [vec3]⟩
      exact h2 h1
    exact hspan ⟨q, hq', rfl⟩
  · by_cases h1 : ci 1 α = 1 ∨ ci 1 α = -1
    · have hh : VOA.LatGen.halfNorm (latP 1) α = 1 := by
        rw [hn]; rcases h1 with h | h <;> rw [h] <;> norm_num
      rw [hh, sub_self]
      rintro _ ⟨q, hq, rfl⟩
      rw [gradingZN_of_nonneg (le_refl _)] at hq
      have hq0 := fock_weight_zero (show q ∈ gradingWN _ 0 from hq)
      rw [hq0, map_smul, ← latStateGen_eq_mkEα, ← latChargeGen]
      rcases h1 with h | h
      · have : α = a1 1 := h
        subst this
        exact mem_v3Sub.mpr ⟨coeff 0 q, 0, 0, by simp [vec3]⟩
      · have : α = -a1 1 := h
        subst this
        exact mem_v3Sub.mpr ⟨0, 0, coeff 0 q, by simp [vec3]⟩
    · have hgt : 1 < VOA.LatGen.halfNorm (latP 1) α := by
        rw [hn]
        push Not at h1
        have : ci 1 α ≤ -2 ∨ 2 ≤ ci 1 α := by omega
        rcases this with h | h <;> nlinarith
      rw [bigradα_eq_bot_of_neg (latP 1) α (by omega)]
      exact bot_le

/-! ### The bracket `u₍₀₎v` on the triple -/

theorem smul_e_zero (w : LatModuleGen (latP 1)) :
    (V1).smul (latChargeGen (latP 1) (a1 1)) 0 w = Screen.Qscr (latP 1) (a1 1) w := by
  rw [← zeroMode_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (a1 1),
    VertexOperatorAlgebra.zeroMode_apply]; rfl

theorem smul_f_zero (w : LatModuleGen (latP 1)) :
    (V1).smul (latChargeGen (latP 1) (-a1 1)) 0 w = Screen.Qscr (latP 1) (-a1 1) w := by
  rw [← zeroMode_latChargeGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (-a1 1),
    VertexOperatorAlgebra.zeroMode_apply]; rfl

theorem smul_h_vec3 (y₁ y₂ y₃ : ℂ) :
    (V1).smul (hSt (latP 1) (a1 1)) 0 (vec3 (latP 1) (a1 1) y₁ y₂ y₃)
      = vec3 (latP 1) (a1 1) (2 * y₁) 0 (-2 * y₃) := by
  have h1 : (V1).smul (hSt (latP 1) (a1 1)) 0 (latChargeGen (latP 1) (a1 1))
      = (2 : ℂ) • latChargeGen (latP 1) (a1 1) := by
    rw [latChargeGen, smul_hSt_zero_latStateGen, latP_form]; norm_num [a1]
  have h2 : (V1).smul (hSt (latP 1) (a1 1)) 0 (hSt (latP 1) (a1 1)) = 0 := by
    change (V1).smul (hSt (latP 1) (a1 1)) 0 (latStateGen (latP 1) (vSchur (latP 1) (a1 1) 1) 0) = 0
    rw [smul_hSt_zero_latStateGen]; simp
  have h3 : (V1).smul (hSt (latP 1) (a1 1)) 0 (latChargeGen (latP 1) (-a1 1))
      = (-2 : ℂ) • latChargeGen (latP 1) (-a1 1) := by
    rw [latChargeGen, smul_hSt_zero_latStateGen, latP_form]
    congr 1
    change (((2 * ((1 : ℕ) : ℤ) * 1 * (-1) : ℤ)) : ℂ) = -2
    push_cast; ring
  simp only [vec3, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right, h1, h2, h3,
    smul_smul, smul_zero, zero_smul]
  module

/-- The bracket `u₍₀₎v` of two weight-one states, in `vec3` coordinates. -/
theorem br_vec3 (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) :
    (V1).smul (vec3 (latP 1) (a1 1) x₁ x₂ x₃) 0 (vec3 (latP 1) (a1 1) y₁ y₂ y₃)
      = vec3 (latP 1) (a1 1) (2 * x₂ * y₁ - 2 * x₁ * y₂) (eps1 * (x₁ * y₃ - x₃ * y₁))
          (2 * x₃ * y₂ - 2 * x₂ * y₃) := by
  conv_lhs => rw [vec3]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_smul_left, smul_e_zero, smul_f_zero,
    smul_h_vec3]
  rw [Qscr_vec3_pos _ (latP_posDef 1 le_rfl) latP1_root,
    Qscr_vec3_neg _ (latP_posDef 1 le_rfl) latP1_root, cocycle_eq_eps1,
    vec3_smul, vec3_smul, vec3_smul, vec3_add, vec3_add]
  apply vec3_congr <;> ring

/-- In the orthonormal coordinates `xyz`, the bracket is `−2i` times the cross product. -/
theorem br_xyz (a b c a' b' c' : ℂ) :
    (V1).smul (xyz a b c) 0 (xyz a' b' c')
      = xyz (-2 * I * (b * c' - c * b')) (-2 * I * (c * a' - a * c')) (-2 * I * (a * b' - b * a')) := by
  rw [xyz, xyz, br_vec3, xyz]
  rcases eps1_cases with h | h <;> rw [h] <;> apply vec3_congr <;>
    (ring_nf; try simp only [I_sq]; try ring_nf)

end WeightOne

/-! ## A cross-product-preserving `3 × 3` matrix lies in `SO(3)` -/

section CrossMatrix

open Matrix

variable {K : Type*} [Field K]

theorem cross_mulVec_adj' (A : Matrix (Fin 3) (Fin 3) K) (u w : Fin 3 → K) :
    (A *ᵥ u) ⨯₃ (A *ᵥ w) = (adjugate A)ᵀ *ᵥ (u ⨯₃ w) := by
  ext i
  fin_cases i <;>
  simp [cross_apply, adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem exists_cross_eq_single (k : Fin 3) : ∃ x y : Fin 3 → K, x ⨯₃ y = Pi.single k 1 := by
  fin_cases k
  · exact ⟨Pi.single 1 1, Pi.single 2 1, by ext i; fin_cases i <;> simp [cross_apply]⟩
  · exact ⟨Pi.single 2 1, Pi.single 0 1, by ext i; fin_cases i <;> simp [cross_apply]⟩
  · exact ⟨Pi.single 0 1, Pi.single 1 1, by ext i; fin_cases i <;> simp [cross_apply]⟩

/-- A matrix preserving the cross product with nonzero determinant is in `SO(3, K)`. -/
theorem orth_of_cross {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ x y, M *ᵥ (x ⨯₃ y) = (M *ᵥ x) ⨯₃ (M *ᵥ y)) (hdet : M.det ≠ 0) :
    Mᵀ * M = 1 ∧ M.det = 1 := by
  have hadj : (adjugate M)ᵀ = M := by
    ext i k
    obtain ⟨x, y, hxy⟩ := exists_cross_eq_single (K := K) k
    have h := congrFun ((cross_mulVec_adj' M x y).symm.trans (hM x y).symm) i
    rw [hxy] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hadj' : adjugate M = Mᵀ := by
    have := congrArg transpose hadj; rwa [transpose_transpose] at this
  have hMM : M * Mᵀ = M.det • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hadj', mul_adjugate]
  have hd : M.det = 1 := by
    have h := congrArg Matrix.det hMM
    rw [det_mul, det_transpose, det_smul, det_one, Fintype.card_fin, mul_one] at h
    have : M.det * M.det * (M.det - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (mul_self_eq_zero.mp h1) hdet
    · exact sub_eq_zero.mp h1
  refine ⟨?_, hd⟩
  rw [hd, one_smul] at hMM
  exact mul_eq_one_comm.mp hMM

end CrossMatrix

/-! ## The representation `ρ : Aut V₂ → SO(3, ℂ)` on the weight-one space -/

section Rep

open Matrix

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- The weight-one state with orthonormal coordinates `v`: `v₀ X + v₁ Y + v₂ Z`. -/
noncomputable def xyzL : (Fin 3 → ℂ) →ₗ[ℂ] LatModuleGen (latP 1) where
  toFun v := xyz (v 0) (v 1) (v 2)
  map_add' _ _ := (xyz_add _ _ _ _ _ _).symm
  map_smul' _ _ := (xyz_smul _ _ _ _).symm

theorem xyzL_apply (v : Fin 3 → ℂ) : xyzL v = xyz (v 0) (v 1) (v 2) := rfl

theorem vec3_coord_three {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ}
    (h : vec3 (latP 1) (a1 1) x₁ x₂ x₃ = vec3 (latP 1) (a1 1) y₁ y₂ y₃) : x₃ = y₃ := by
  have hq := congrArg (Screen.Qscr (latP 1) (a1 1)) h
  rw [Qscr_vec3_pos _ (latP_posDef 1 le_rfl) latP1_root,
    Qscr_vec3_pos _ (latP_posDef 1 le_rfl) latP1_root, cocycle_eq_eps1] at hq
  have h2 := vec3_coord_two hq
  have := congrArg (eps1 * ·) h2
  simp only [← mul_assoc, eps1_sq, one_mul] at this
  exact this

theorem xyz_inj {a b c a' b' c' : ℂ} (h : xyz a b c = xyz a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  rw [xyz, xyz] at h
  have h1 := vec3_coord_one h
  have h2 := vec3_coord_two h
  have h3 := vec3_coord_three h
  have h3' : a - I * b = a' - I * b' := by
    have := congrArg (eps1 * ·) h3
    simp only at this
    linear_combination this - (a - I * b - (a' - I * b')) * eps1_sq
  refine ⟨by linear_combination (h1 + h3') / 2, ?_, h2⟩
  have hb : I * (2 * (b - b')) = 0 := by linear_combination h1 - h3'
  have := (mul_eq_zero.mp hb).resolve_left I_ne_zero
  linear_combination this / 2

theorem xyzL_injective : Function.Injective xyzL := by
  intro v w h
  obtain ⟨h0, h1, h2⟩ := xyz_inj h
  ext i; fin_cases i <;> assumption

theorem xyzL_mem_grading (v : Fin 3 → ℂ) : xyzL v ∈ (V1).grading 1 := by
  rw [xyzL_apply, xyz, vec3]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
  · exact latChargeGen_mem_grading_one _ _ _ latP1_root
  · exact hSt_mem_grading_one 1 le_rfl
  · exact latChargeGen_mem_grading_one _ _ _ latP1_root'

theorem vec3_eq_xyzL (x₁ x₂ x₃ : ℂ) : vec3 (latP 1) (a1 1) x₁ x₂ x₃
    = xyzL ![(x₁ + eps1 * x₃) / 2, -I * (x₁ - eps1 * x₃) / 2, x₂] := by
  rw [xyzL_apply, xyz]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rcases eps1_cases with h | h <;> rw [h] <;> apply vec3_congr <;>
    (ring_nf; try simp only [I_sq]; try ring_nf)

theorem grading_one_eq_xyzL {x : LatModuleGen (latP 1)} (hx : x ∈ (V1).grading 1) :
    ∃ v, x = xyzL v := by
  obtain ⟨x₁, x₂, x₃, rfl⟩ := V2_grading_one hx
  exact ⟨_, vec3_eq_xyzL x₁ x₂ x₃⟩

theorem aut_xyzL_mem_range (g : Aut V1) (v : Fin 3 → ℂ) : g (xyzL v) ∈ LinearMap.range xyzL := by
  obtain ⟨w, hw⟩ := grading_one_eq_xyzL (Aut.map_grading g (xyzL_mem_grading v))
  exact ⟨w, hw.symm⟩

/-- The action of `g` on the weight-one space, in orthonormal coordinates. -/
noncomputable def autL (g : Aut V1) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  (LinearEquiv.ofInjective xyzL xyzL_injective).symm.toLinearMap ∘ₗ
    (g.toLinearEquiv.toLinearMap ∘ₗ xyzL).codRestrict (LinearMap.range xyzL)
      (fun v => aut_xyzL_mem_range g v)

theorem xyzL_autL (g : Aut V1) (v : Fin 3 → ℂ) : xyzL (autL g v) = g (xyzL v) := by
  set e := LinearEquiv.ofInjective xyzL xyzL_injective
  have h := LinearEquiv.ofInjective_apply xyzL (h := xyzL_injective)
  change xyzL (e.symm _) = _
  rw [← h, e.apply_symm_apply]
  rfl

theorem autL_mul (g h : Aut V1) : autL (g * h) = autL g ∘ₗ autL h := by
  refine LinearMap.ext fun v => ?_
  apply xyzL_injective
  rw [LinearMap.comp_apply, xyzL_autL, xyzL_autL, xyzL_autL, Aut.mul_apply]

theorem autL_one : autL 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  apply xyzL_injective
  rw [xyzL_autL]; rfl

/-- **The representation `ρ : Aut V₂ →* M₃(ℂ)`** on `(V₂)₁ ≅ sl₂`, in the orthonormal basis
`X = e + εf`, `Y = i(e − εf)`, `Z = h`. -/
noncomputable def rho : Aut V1 →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun g := LinearMap.toMatrix' (autL g)
  map_one' := by rw [autL_one, LinearMap.toMatrix'_id]
  map_mul' g h := by rw [autL_mul, LinearMap.toMatrix'_comp]

theorem rho_mulVec (g : Aut V1) (v : Fin 3 → ℂ) : rho g *ᵥ v = autL g v :=
  LinearMap.toMatrix'_mulVec _ _

/-- `g (v·(X,Y,Z)) = (ρ(g) v)·(X,Y,Z)`. -/
theorem aut_xyzL (g : Aut V1) (v : Fin 3 → ℂ) : g (xyzL v) = xyzL (rho g *ᵥ v) := by
  rw [rho_mulVec, xyzL_autL]

theorem br_xyzL (x y : Fin 3 → ℂ) :
    (V1).smul (xyzL x) 0 (xyzL y) = xyzL ((-2 * I) • (x ⨯₃ y)) := by
  rw [xyzL_apply, xyzL_apply, br_xyz, xyzL_apply]
  simp [cross_apply]

theorem rho_cross (g : Aut V1) (x y : Fin 3 → ℂ) :
    rho g *ᵥ (x ⨯₃ y) = (rho g *ᵥ x) ⨯₃ (rho g *ᵥ y) := by
  have h := Aut.map_smul g (xyzL x) 0 (xyzL y)
  rw [aut_xyzL, aut_xyzL, br_xyzL, br_xyzL, aut_xyzL] at h
  have h2 := xyzL_injective h
  rw [Matrix.mulVec_smul] at h2
  have hI : (-2 * I) ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  exact smul_right_injective _ hI h2

theorem rho_det_ne_zero (g : Aut V1) : (rho g).det ≠ 0 := by
  have h : rho g * rho g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have := congrArg Matrix.det h
  rw [det_mul, det_one] at this
  exact left_ne_zero_of_mul_eq_one this

/-- `ρ(g)` is complex-orthogonal: `ρ(g)ᵀ ρ(g) = 1`. -/
theorem rho_transpose_mul (g : Aut V1) : (rho g)ᵀ * rho g = 1 :=
  (orth_of_cross (rho_cross g) (rho_det_ne_zero g)).1

/-- `det ρ(g) = 1`. -/
theorem rho_det (g : Aut V1) : (rho g).det = 1 :=
  (orth_of_cross (rho_cross g) (rho_det_ne_zero g)).2

theorem rho_mul_transpose (g : Aut V1) : rho g * (rho g)ᵀ = 1 :=
  mul_eq_one_comm.mp (rho_transpose_mul g)

theorem hSt_eq_xyzL : hSt (latP 1) (a1 1) = xyzL ![0, 0, 1] := by
  rw [hSt_eq_xyz]; rfl

theorem latChargeGen_eq_xyzL : latChargeGen (latP 1) (a1 1) = xyzL ![1 / 2, -I / 2, 0] := by
  rw [latChargeGen_eq_xyz]; rfl

/-- **`ρ` is injective** (rigidity: `(V₂)₁` contains `h` and `e^α`). -/
theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply aut_eq_one_of_fix 1 le_rfl g
  · rw [hSt_eq_xyzL, aut_xyzL, hg, one_mulVec]
  · rw [latChargeGen_eq_xyzL, aut_xyzL, hg, one_mulVec]

/-! ### Transitivity on the unit sphere: every axis is conjugate to `h` -/

theorem expE_vec3 (c x₁ x₂ x₃ : ℂ) : expE c (vec3 (latP 1) (a1 1) x₁ x₂ x₃)
    = vec3 (latP 1) (a1 1) (x₁ - 2 * c * x₂ - c ^ 2 * eps1 * x₃) (x₂ + c * eps1 * x₃) x₃ := by
  rw [rootExp_vec3_pos _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root, cocycle_eq_eps1]

theorem expF_vec3 (c x₁ x₂ x₃ : ℂ) : expF c (vec3 (latP 1) (a1 1) x₁ x₂ x₃)
    = vec3 (latP 1) (a1 1) x₁ (x₂ - c * eps1 * x₁) (x₃ + 2 * c * x₂ - c ^ 2 * eps1 * x₁) := by
  rw [rootExp_vec3_neg _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root latP1_root',
    cocycle_eq_eps1]

theorem hSt_eq_vec3 : hSt (latP 1) (a1 1) = vec3 (latP 1) (a1 1) 0 1 0 := by simp [vec3]

theorem exists_aut_vec3_of_x3_zero (x₁ x₂ : ℂ) (h : x₂ ^ 2 = 1) :
    ∃ φ : Aut V1, φ (vec3 (latP 1) (a1 1) x₁ x₂ 0) = hSt (latP 1) (a1 1) := by
  have hx2 : x₂ ≠ 0 := by rintro rfl; norm_num at h
  have h1 : expE (x₁ / (2 * x₂)) (vec3 (latP 1) (a1 1) x₁ x₂ 0) = vec3 (latP 1) (a1 1) 0 x₂ 0 := by
    rw [expE_vec3]; apply vec3_congr <;> field_simp <;> ring
  have h2 : x₂ = 1 ∨ x₂ = -1 := by
    have : (x₂ - 1) * (x₂ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases h2 with rfl | rfl
  · exact ⟨_, h1.trans hSt_eq_vec3.symm⟩
  · refine ⟨thetaM 1 le_rfl * expE (x₁ / (2 * -1)), ?_⟩
    rw [Aut.mul_apply, h1, show vec3 (latP 1) (a1 1) 0 (-1) 0 = -hSt (latP 1) (a1 1) by
      rw [hSt_eq_vec3, vec3_neg]; simp, map_neg, thetaAut_apply, thetaLat_hSt', neg_neg]

theorem exists_aut_vec3 (x₁ x₂ x₃ : ℂ) (h : x₂ ^ 2 + eps1 * x₁ * x₃ = 1) :
    ∃ φ : Aut V1, φ (vec3 (latP 1) (a1 1) x₁ x₂ x₃) = hSt (latP 1) (a1 1) := by
  by_cases hx1 : x₁ = 0
  · subst hx1
    have h' : x₂ ^ 2 = 1 := by simpa using h
    have hx2 : x₂ ≠ 0 := by rintro rfl; norm_num at h'
    obtain ⟨φ, hφ⟩ := exists_aut_vec3_of_x3_zero 0 x₂ h'
    refine ⟨φ * expF (-x₃ / (2 * x₂)), ?_⟩
    rw [Aut.mul_apply, expF_vec3, ← hφ]
    congr 1; apply vec3_congr <;> field_simp <;> ring
  · have ha : -eps1 * x₁ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (by
      rcases eps1_cases with h | h <;> rw [h] <;> norm_num)) hx1
    obtain ⟨c, hc⟩ := exists_quadratic_eq_zero (b := 2 * x₂) (c := x₃) ha (IsAlgClosed.exists_eq_mul_self _)
    have hroot : x₃ + 2 * c * x₂ - c ^ 2 * eps1 * x₁ = 0 := by linear_combination hc
    have hq : (x₂ - c * eps1 * x₁) ^ 2 = 1 := by
      linear_combination h - (eps1 * x₁) * hroot
    obtain ⟨φ, hφ⟩ := exists_aut_vec3_of_x3_zero x₁ _ hq
    refine ⟨φ * expF c, ?_⟩
    rw [Aut.mul_apply, expF_vec3, hroot, hφ]

theorem xyzL_eq_vec3 (v : Fin 3 → ℂ) :
    xyzL v = vec3 (latP 1) (a1 1) (v 0 + I * v 1) (v 2) (eps1 * v 0 - I * eps1 * v 1) := rfl

/-- **Transitivity.** Every unit vector `v` (`v ⬝ v = 1`) of `(V₂)₁` is moved to `h` by an
automorphism of `V₂` (a product of root exponentials and `θ`). -/
theorem exists_aut_xyzL_eq_h (v : Fin 3 → ℂ) (hv : v ⬝ᵥ v = 1) :
    ∃ φ : Aut V1, φ (xyzL v) = hSt (latP 1) (a1 1) := by
  rw [xyzL_eq_vec3]
  apply exists_aut_vec3
  simp only [dotProduct, Fin.sum_univ_three] at hv
  linear_combination hv + (v 0 ^ 2 + v 1 ^ 2) * eps1_sq - eps1 ^ 2 * v 1 ^ 2 * I_sq

/-! ### Finite-order automorphisms have an anisotropic axis -/

theorem rho_dot (g : Aut V1) (x y : Fin 3 → ℂ) : (rho g *ᵥ x) ⬝ᵥ (rho g *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, rho_transpose_mul, one_mulVec]

theorem det_sub_one_eq_zero (g : Aut V1) : (rho g - 1).det = 0 := by
  set A := rho g
  have hfac : A - 1 = A * (1 - Aᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, rho_mul_transpose]
  have h1 : (A - 1).det = (1 - A).det := by
    rw [hfac, Matrix.det_mul, rho_det, one_mul, ← Matrix.det_transpose,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
  have h2 : (1 - A).det = - (A - 1).det := by
    rw [← neg_sub, Matrix.det_neg]; norm_num
  have : (2 : ℂ) * (A - 1).det = 0 := by linear_combination h1 + h2
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

theorem exists_fixed_ne_zero (g : Aut V1) : ∃ w : Fin 3 → ℂ, w ≠ 0 ∧ rho g *ᵥ w = w := by
  obtain ⟨w, hw, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (det_sub_one_eq_zero g)
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

theorem vecMul_rho_of_fixed {g : Aut V1} {w : Fin 3 → ℂ} (hw : rho g *ᵥ w = w) :
    w ᵥ* rho g = w := by
  rw [← mulVec_transpose]
  conv_lhs => rw [← hw]
  rw [mulVec_mulVec, rho_transpose_mul, one_mulVec]

/-- A finite-order automorphism of `V₂` fixes a unit vector of `(V₂)₁`. -/
theorem exists_fixed_unit (g : Aut V1) (hg : IsOfFinOrder g) :
    ∃ v : Fin 3 → ℂ, v ⬝ᵥ v = 1 ∧ rho g *ᵥ v = v := by
  obtain ⟨w, hw0, hw⟩ := exists_fixed_ne_zero g
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  set N := orderOf g
  have hN : 0 < N := hg.orderOf_pos
  set p : Fin 3 → ℂ := ∑ k ∈ Finset.range N, rho (g ^ k) *ᵥ Pi.single i 1
  have hp : rho g *ᵥ p = p := by
    rw [Matrix.mulVec_sum]
    simp only [mulVec_mulVec, ← map_mul, ← pow_succ']
    have h1 := Finset.sum_range_succ' (fun k => rho (g ^ k) *ᵥ Pi.single i (1 : ℂ)) N
    have h2 := Finset.sum_range_succ (fun k => rho (g ^ k) *ᵥ Pi.single i (1 : ℂ)) N
    rw [pow_orderOf_eq_one] at h2
    rw [pow_zero] at h1
    exact add_right_cancel (h1.symm.trans h2)
  have hwp : w ⬝ᵥ p = N * w i := by
    rw [dotProduct_sum]
    have : ∀ k, w ⬝ᵥ (rho (g ^ k) *ᵥ Pi.single i 1) = w i := by
      intro k
      rw [dotProduct_mulVec, map_pow]
      have : w ᵥ* rho g ^ k = w := by
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, vecMul_rho_of_fixed hw]
      rw [this, dotProduct_single, mul_one]
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hwp0 : w ⬝ᵥ p ≠ 0 := by
    rw [hwp]; exact mul_ne_zero (by exact_mod_cast hN.ne') hi
  obtain ⟨q, hq0, hq⟩ : ∃ q : Fin 3 → ℂ, q ⬝ᵥ q ≠ 0 ∧ rho g *ᵥ q = q := by
    by_cases h1 : w ⬝ᵥ w = 0
    · by_cases h2 : p ⬝ᵥ p = 0
      · refine ⟨w + p, ?_, by rw [mulVec_add, hw, hp]⟩
        rw [add_dotProduct, dotProduct_add, dotProduct_add, h1, h2, dotProduct_comm p w]
        intro h; apply hwp0; linear_combination h / 2
      · exact ⟨p, h2, hp⟩
    · exact ⟨w, h1, hw⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (q ⬝ᵥ q)⁻¹
  refine ⟨s • q, ?_, by rw [mulVec_smul, hq]⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hs,
    inv_mul_cancel₀ hq0]

/-! ### Automorphisms fixing `h` are torus elements -/

theorem eq_charU_of_fix_h (ψ : Aut V1) (hψ : ψ (hSt (latP 1) (a1 1)) = hSt (latP 1) (a1 1)) :
    ∃ u : ℂˣ, ψ = charU 1 le_rfl u := by
  obtain ⟨d, hd⟩ := exists_char_of_fix_h 1 le_rfl ψ hψ
  refine ⟨Additive.toMul (d (a1 1)), Aut.ext (LinearEquiv.ext fun x => ?_)⟩
  have hdu : d = unitChar 1 (Additive.toMul (d (a1 1))) := by
    apply AddMonoidHom.ext_int
    change d (a1 1) = (1 : ℤ) • Additive.ofMul (Additive.toMul (d (a1 1)))
    simp
  rw [Aut.coe_toLinearEquiv, hd x]
  conv_lhs => rw [hdu]
  rfl

/-- **Every finite-order automorphism of `V₂` is conjugate to a torus element** `g_u`. -/
theorem exists_conj_charU (g : Aut V1) (hg : IsOfFinOrder g) :
    ∃ φ : Aut V1, ∃ u : ℂˣ, φ * g * φ⁻¹ = charU 1 le_rfl u := by
  obtain ⟨v, hv, hfix⟩ := exists_fixed_unit g hg
  obtain ⟨φ, hφ⟩ := exists_aut_xyzL_eq_h v hv
  obtain ⟨u, hu⟩ := eq_charU_of_fix_h (φ * g * φ⁻¹) (by
    have h1 : φ⁻¹ (hSt (latP 1) (a1 1)) = xyzL v := by
      rw [← hφ, Aut.inv_apply]; exact φ.toLinearEquiv.symm_apply_apply _
    rw [Aut.mul_apply, Aut.mul_apply, h1, aut_xyzL, hfix, hφ])
  exact ⟨φ, u, hu⟩

end Rep

/-! ## Cyclic and dihedral subgroups are conjugate into the torus normalizer -/

section Normalizer

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

theorem eq_one_or_neg_one_of_sq {x : ℂ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- If a nontrivial torus element `g_w` fixes `y h`, then `y` lies in the torus normalizer
(`y h = ±h`, by orthogonality of `ρ(y)`). -/
theorem normalizer_of_fix {y : Aut V1} {w : ℂˣ} (hw : w ≠ 1)
    (h : charU 1 le_rfl w (y (hSt (latP 1) (a1 1))) = y (hSt (latP 1) (a1 1))) :
    (∃ u, y = charU 1 le_rfl u) ∨ (∃ u, y = thetaM 1 le_rfl * charU 1 le_rfl u) := by
  obtain ⟨x₁, x₂, x₃, hx⟩ := V2_grading_one (Aut.map_grading y (hSt_mem_grading_one 1 le_rfl))
  rw [hx, charU_vec3] at h
  have h1 := vec3_coord_one h
  have h3 := vec3_coord_three h
  have hw' : (w : ℂ) ≠ 1 := fun e => hw (Units.ext e)
  have hx1 : x₁ = 0 := by
    have : ((w : ℂ) - 1) * x₁ = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hw')
  have hx3 : x₃ = 0 := by
    have hwi : (w : ℂ)⁻¹ ≠ 1 := by
      intro e; apply hw'; rw [← inv_inv (w : ℂ), e, inv_one]
    have : ((w : ℂ)⁻¹ - 1) * x₃ = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hwi)
  subst hx1 hx3
  have hyh : y (hSt (latP 1) (a1 1)) = x₂ • hSt (latP 1) (a1 1) := by
    rw [hx, hSt_eq_vec3, vec3_smul]; simp
  have hsq : x₂ ^ 2 = 1 := by
    have e := hyh
    rw [hSt_eq_xyzL, aut_xyzL, ← map_smul] at e
    have e2 := xyzL_injective e
    have := rho_dot y ![0, 0, 1] ![0, 0, 1]
    rw [e2] at this
    simpa [dotProduct, Fin.sum_univ_three, sq] using this
  rcases eq_one_or_neg_one_of_sq hsq with rfl | rfl
  · left
    exact eq_charU_of_fix_h y (by rw [hyh, one_smul])
  · right
    obtain ⟨u, hu⟩ := eq_charU_of_fix_h (thetaM 1 le_rfl * y) (by
      rw [Aut.mul_apply, hyh, neg_one_smul, map_neg, thetaAut_apply, thetaLat_hSt', neg_neg])
    refine ⟨u, ?_⟩
    rw [← hu, ← mul_assoc, thetaM_mul_self, one_mul]

/-- A finite cyclic subgroup of `Aut V₂` is conjugate into the torus. -/
theorem inNormalizer_conj_of_isCyclic (G : Subgroup (Aut V1)) [Finite G] [IsCyclic G] :
    ∃ φ : Aut V1, InNormalizer 1 le_rfl (G.map (MulAut.conj φ).toMonoidHom) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hfin : IsOfFinOrder (g : Aut V1) := G.subtype.isOfFinOrder (isOfFinOrder_of_finite g)
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU _ hfin
  refine ⟨φ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  left
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  have hxk : x = (g : Aut V1) ^ k := by
    have := congrArg Subtype.val hk; simpa using this.symm
  refine ⟨u ^ k, ?_⟩
  rw [hxk, map_zpow]
  change (MulAut.conj φ) (g : Aut V1) ^ k = _
  rw [MulAut.conj_apply, hφ, map_zpow]

theorem dihedral_conj_r {n : ℕ} (d : DihedralGroup n) :
    d * DihedralGroup.r 1 * d⁻¹ = DihedralGroup.r 1 ∨
      d * DihedralGroup.r 1 * d⁻¹ = (DihedralGroup.r 1)⁻¹ := by
  rcases d with i | i
  · left
    simp only [DihedralGroup.r_mul_r, DihedralGroup.inv_r]
    congr 1; ring
  · right
    simp only [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    congr 1; ring

/-- A finite dihedral subgroup `D_n ≤ Aut V₂` (`n ≥ 2`) is conjugate into the torus
normalizer: conjugate the rotation `r` into the torus; every element then fixes or reverses the
axis `h` of `r`. -/
theorem inNormalizer_conj_of_dihedral (G : Subgroup (Aut V1)) [Finite G] {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* DihedralGroup n) :
    ∃ φ : Aut V1, InNormalizer 1 le_rfl (G.map (MulAut.conj φ).toMonoidHom) := by
  set r : G := e.symm (DihedralGroup.r 1)
  have hr1 : (r : Aut V1) ≠ 1 := by
    intro h
    have h' : r = 1 := Subtype.ext h
    have h2 : (DihedralGroup.r 1 : DihedralGroup n) = DihedralGroup.r 0 := by
      have : e r = e 1 := by rw [h']
      rwa [map_one, show e r = DihedralGroup.r 1 from e.apply_symm_apply _,
        DihedralGroup.one_def] at this
    have := ZMod.one_eq_zero_iff.mp (DihedralGroup.r.inj h2)
    omega
  have hfin : IsOfFinOrder (r : Aut V1) := G.subtype.isOfFinOrder (isOfFinOrder_of_finite r)
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU _ hfin
  have hu : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hφ
    apply hr1
    have : (r : Aut V1) = φ⁻¹ * (φ * r * φ⁻¹) * φ := by group
    rw [this, hφ, mul_one, inv_mul_cancel]
  refine ⟨φ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  set y : Aut V1 := φ * x * φ⁻¹
  have hc : ∃ w : ℂˣ, w ≠ 1 ∧ y * charU 1 le_rfl u * y⁻¹ = charU 1 le_rfl w := by
    have hxr := dihedral_conj_r (e ⟨x, hx⟩)
    rw [show (DihedralGroup.r 1 : DihedralGroup n) = e r from (e.apply_symm_apply _).symm] at hxr
    simp only [← map_mul, ← map_inv] at hxr
    have hyt : y * charU 1 le_rfl u * y⁻¹
        = φ * (((⟨x, hx⟩ : G) * r * (⟨x, hx⟩ : G)⁻¹ : G) : Aut V1) * φ⁻¹ := by
      rw [← hφ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      simp only [y]
      group
    rcases hxr with h | h
    · refine ⟨u, hu, ?_⟩
      rw [hyt, e.injective h, hφ]
    · refine ⟨u⁻¹, inv_ne_one.mpr hu, ?_⟩
      rw [hyt, e.injective h, Subgroup.coe_inv, map_inv, ← hφ]
      group
  obtain ⟨w, hw, hyw⟩ := hc
  have hyx : (MulAut.conj φ).toMonoidHom x = y := rfl
  have hinv : y⁻¹ (y (hSt (latP 1) (a1 1))) = hSt (latP 1) (a1 1) :=
    y.toLinearEquiv.symm_apply_apply _
  rw [hyx]
  exact normalizer_of_fix hw (by rw [← hyw, Aut.mul_apply, Aut.mul_apply, hinv, charU_hSt])

end Normalizer

end VOA.Classification.COne

/-! ## Finite subgroups of `SO(3, ℂ)`: the unitary trick -/

open Matrix
open scoped ComplexOrder

namespace VOA.Classification.COne.SO3C

local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ
local notation "V3" => Fin 3 → ℂ

/-! ### Generic facts on `SO(3, ℂ)` -/

theorem cross_of_orth {A : M3} (hO : Aᵀ * A = 1) (hD : A.det = 1) (u w : V3) :
    A *ᵥ (u ⨯₃ w) = (A *ᵥ u) ⨯₃ (A *ᵥ w) := by
  have h1 : A * adjugate A = 1 := by rw [mul_adjugate, hD, one_smul]
  have h2 : adjugate A = Aᵀ := by
    calc adjugate A = (Aᵀ * A) * adjugate A := by rw [hO, Matrix.one_mul]
      _ = Aᵀ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [cross_mulVec_adj', h2, transpose_transpose]

theorem dot_mulVec_orth {A : M3} (hO : Aᵀ * A = 1) (x y : V3) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hO, one_mulVec]

theorem star_mulVec' (A : M3) (x : V3) : star (A *ᵥ x) = A.map star *ᵥ star x := by
  ext i; simp [mulVec, dotProduct, star_sum]

theorem map_star_mul (A B : M3) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [mul_apply]

theorem map_star_map_star (A : M3) : (A.map star).map star = A := by
  ext i j; simp

theorem star_cross (x y : V3) : star (x ⨯₃ y) = star x ⨯₃ star y := by
  ext i; fin_cases i <;> simp [cross_apply]

theorem smul_cross_smul (a b : ℂ) (x y : V3) : (a • x) ⨯₃ (b • y) = (a * b) • (x ⨯₃ y) := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

/-- An anisotropic line on which `M` acts, with `M` orthogonal, is acted on by `±1`. -/
theorem pm_of_smul {A : M3} (hO : Aᵀ * A = 1) {u : V3} (hu : u ⬝ᵥ u ≠ 0) {c : ℂ}
    (hc : A *ᵥ u = c • u) : A *ᵥ u = u ∨ A *ᵥ u = -u := by
  have h := dot_mulVec_orth hO u u
  rw [hc, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
  have h2 : (c * c - 1) * (u ⬝ᵥ u) = 0 := by linear_combination h
  have h3 := (mul_eq_zero.mp h2).resolve_right hu
  have : (c - 1) * (c + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h4 | h4
  · left; rw [hc, sub_eq_zero.mp h4, one_smul]
  · right; rw [hc, eq_neg_of_add_eq_zero_left h4, neg_one_smul]

section Avg

variable {Γ : Type*} [Group Γ] [Fintype Γ] (ρ : Γ →* M3)

/-- The averaged Hermitian form `H = Σ ρ(g)ᴴ ρ(g)`. -/
noncomputable def avgH : M3 := ∑ g, (ρ g)ᴴ * ρ g

variable {ρ}
variable (hO : ∀ g, (ρ g)ᵀ * ρ g = 1)
include hO

omit [Fintype Γ] in
theorem mulVec_injective (g : Γ) : Function.Injective (ρ g).mulVec := by
  intro x y h
  have := congrArg ((ρ g)ᵀ *ᵥ ·) h
  simpa [mulVec_mulVec, hO g] using this

theorem avgH_posDef : (avgH ρ).PosDef :=
  posDef_sum Finset.univ_nonempty fun g _ => PosDef.conjTranspose_mul_self _ (mulVec_injective hO g)

omit hO in
theorem avgH_inv (g : Γ) : (ρ g)ᴴ * avgH ρ * ρ g = avgH ρ := by
  rw [avgH, Matrix.mul_sum, Matrix.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => ?_)
  simp only [Equiv.coe_mulRight, map_mul, conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype Γ] in
theorem map_star_mul_conjTranspose (g : Γ) : (ρ g).map star * (ρ g)ᴴ = 1 := by
  have h := mul_eq_one_comm.mp (hO g)
  have := congrArg (fun M : M3 => M.map star) h
  simpa [conjTranspose, Matrix.map_mul, transpose_map] using this

/-- `H ρ(g) = conj(ρ(g)) H`. -/
theorem avgH_mul (g : Γ) : avgH ρ * ρ g = (ρ g).map star * avgH ρ := by
  calc avgH ρ * ρ g = ((ρ g).map star * (ρ g)ᴴ) * (avgH ρ * ρ g) := by
        rw [map_star_mul_conjTranspose hO, Matrix.one_mul]
    _ = (ρ g).map star * avgH ρ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ρ g)ᴴ, avgH_inv]


theorem avgH_herm : (avgH ρ)ᴴ = avgH ρ := (avgH_posDef hO).1

theorem avgH_transpose : (avgH ρ)ᵀ = (avgH ρ).map star := by
  ext i j
  have := congrFun (congrFun (avgH_herm hO) j) i
  simp only [conjTranspose_apply] at this
  simp [transpose_apply, ← this]

/-- `A = Hᵀ H = H̄ H` commutes with `ρ`. -/
theorem avgA_comm (g : Γ) : ((avgH ρ)ᵀ * avgH ρ) * ρ g = ρ g * ((avgH ρ)ᵀ * avgH ρ) := by
  have h1 := congrArg (fun M : M3 => M.map star) (avgH_mul hO g)
  simp only [map_star_mul, map_star_map_star] at h1
  rw [← avgH_transpose hO] at h1
  rw [Matrix.mul_assoc, avgH_mul hO, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]

omit hO [Fintype Γ] in
theorem line_of_submodule (W : Submodule ℂ V3) (hW : Module.finrank ℂ W = 1)
    (hinv : ∀ g, ∀ x ∈ W, ρ g *ᵥ x ∈ W) :
    ∃ v : V3, v ≠ 0 ∧ ∀ g, ∃ c : ℂ, ρ g *ᵥ v = c • v := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hW
  refine ⟨v, fun h => hv0 (Subtype.ext h), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨ρ g *ᵥ v, hinv g v v.2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Either `A` is scalar, or `ρ` has an invariant line. -/
theorem scalar_or_line :
    (∃ μ : ℂ, (avgH ρ)ᵀ * avgH ρ = μ • 1) ∨ ∃ v : V3, v ≠ 0 ∧ ∀ g, ∃ c : ℂ, ρ g *ᵥ v = c • v := by
  set A := (avgH ρ)ᵀ * avgH ρ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  set f : V3 →ₗ[ℂ] V3 := Matrix.toLin' (A - μ • 1)
  have hcomm : ∀ g x, f (ρ g *ᵥ x) = ρ g *ᵥ f x := by
    intro g x
    simp only [f, Matrix.toLin'_apply, mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [show A * ρ g = ρ g * A from avgA_comm hO g]
  have hker : LinearMap.ker f = Module.End.eigenspace (Matrix.toLin' A) μ := by
    rw [Module.End.eigenspace_def]
    congr 1
    simp [f, map_sub, map_smul, Matrix.toLin'_one]
    rfl
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) := by
    rw [hker]
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv.1⟩, fun h => hv.2 (congrArg Subtype.val h)⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  by_cases h3 : Module.finrank ℂ (LinearMap.ker f) = 3
  · left
    refine ⟨μ, ?_⟩
    have hf : f = 0 := by
      have htop : LinearMap.ker f = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
      exact LinearMap.ker_eq_top.mp htop
    have := congrArg LinearMap.toMatrix' hf
    simp only [f, LinearMap.toMatrix'_toLin', map_zero] at this
    exact sub_eq_zero.mp this
  · right
    by_cases h1 : Module.finrank ℂ (LinearMap.ker f) = 1
    · refine line_of_submodule _ h1 fun g x hx => ?_
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hcomm, hx, mulVec_zero]
    · refine line_of_submodule (LinearMap.range f) (by omega) fun g x hx => ?_
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ g *ᵥ y, hcomm g y⟩


/-- `J x = conj(H x)` commutes with `ρ`. -/
theorem J_comm (g : Γ) (x : V3) :
    ρ g *ᵥ star (avgH ρ *ᵥ x) = star (avgH ρ *ᵥ (ρ g *ᵥ x)) := by
  rw [mulVec_mulVec, avgH_mul hO, star_mulVec', star_mulVec', map_star_mul, map_star_map_star,
    ← mulVec_mulVec]

theorem dot_star_avgH_ne_zero {v : V3} (hv : v ≠ 0) : v ⬝ᵥ star (avgH ρ *ᵥ v) ≠ 0 := by
  have hp := (avgH_posDef hO).dotProduct_mulVec_pos hv
  intro h
  have : star v ⬝ᵥ (avgH ρ *ᵥ v) = 0 := by
    have h' := congrArg star h
    rw [star_zero] at h'
    rw [← h', dotProduct_comm, ← star_dotProduct_star, star_star]
  rw [this] at hp
  exact lt_irrefl _ hp

/-- **An invariant line gives an invariant anisotropic unit vector**, on which `ρ` acts by `±1`. -/
theorem pm_of_line (hD : ∀ g, (ρ g).det = 1) {v : V3} (hv : v ≠ 0)
    (hinv : ∀ g, ∃ c : ℂ, ρ g *ᵥ v = c • v) :
    ∃ u : V3, u ⬝ᵥ u = 1 ∧ ∀ g, ρ g *ᵥ u = u ∨ ρ g *ᵥ u = -u := by
  obtain ⟨u, hu, huinv⟩ : ∃ u : V3, u ⬝ᵥ u ≠ 0 ∧ ∀ g, ∃ c : ℂ, ρ g *ᵥ u = c • u := by
    by_cases hvv : v ⬝ᵥ v = 0
    · set w := star (avgH ρ *ᵥ v)
      have hvw := dot_star_avgH_ne_zero hO hv
      refine ⟨v ⨯₃ w, ?_, fun g => ?_⟩
      · rw [cross_dot_cross, hvv, zero_mul, zero_sub, dotProduct_comm w v]
        exact neg_ne_zero.mpr (mul_ne_zero hvw hvw)
      · obtain ⟨c, hc⟩ := hinv g
        refine ⟨c * star c, ?_⟩
        rw [cross_of_orth (hO g) (hD g), hc, J_comm hO, hc, mulVec_smul, star_smul,
          smul_cross_smul]
    · exact ⟨v, hvv, hinv⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (u ⬝ᵥ u)⁻¹
  refine ⟨s • u, ?_, fun g => ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hs,
      inv_mul_cancel₀ hu]
  · obtain ⟨c, hc⟩ := huinv g
    have hsu : (s • u) ⬝ᵥ (s • u) ≠ 0 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← hs,
        inv_mul_cancel₀ hu]; exact one_ne_zero
    exact pm_of_smul (hO g) hsu (c := c) (by rw [mulVec_smul, hc, smul_comm])


/-! ### The scalar case: a `ρ`-invariant real structure -/

omit hO in
/-- A real positive complex number is `(√t)²` with `t > 0`. -/
theorem exists_real_of_pos {z : ℂ} (hz : 0 < z) : ∃ r : ℝ, 0 < r ∧ z = ((r : ℂ)) ^ 2 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hz
  refine ⟨Real.sqrt z.re, Real.sqrt_pos.mpr h1, ?_⟩
  rw [← Complex.ofReal_pow, Real.sq_sqrt h1.le]
  exact Complex.ext rfl (by simp [← h2])

theorem scalar_pos {μ : ℂ} (hμ : (avgH ρ)ᵀ * avgH ρ = μ • 1) : 0 < μ := by
  set H := avgH ρ
  have hP := avgH_posDef hO
  set e : V3 := Pi.single 0 1
  have he : e ≠ 0 := by
    intro h; have := congrFun h 0; simp [e] at this
  have hp := hP.dotProduct_mulVec_pos he
  have hy : H *ᵥ e ≠ 0 := fun h => by rw [h, dotProduct_zero] at hp; exact lt_irrefl _ hp
  have hq := hP.transpose.dotProduct_mulVec_pos hy
  have hrel : star (H *ᵥ e) ⬝ᵥ (Hᵀ *ᵥ (H *ᵥ e)) = μ * (star e ⬝ᵥ (H *ᵥ e)) := by
    rw [mulVec_mulVec, hμ, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, star_mulVec,
      ← dotProduct_mulVec, avgH_herm hO]
  rw [hrel] at hq
  set p := star e ⬝ᵥ (H *ᵥ e)
  obtain ⟨hp1, hp2⟩ := Complex.pos_iff.mp hp
  obtain ⟨hq1, hq2⟩ := Complex.pos_iff.mp hq
  rw [Complex.mul_re, ← hp2, mul_zero, sub_zero] at hq1
  rw [Complex.mul_im, ← hp2, mul_zero, zero_add] at hq2
  have him : μ.im = 0 := by
    have := hq2.symm
    exact (mul_eq_zero.mp this).resolve_right hp1.ne'
  have hre : 0 < μ.re := pos_of_mul_pos_left hq1 hp1.le
  exact Complex.pos_iff.mpr ⟨hre, him.symm⟩

/-- The normalized form `H₁ = r⁻¹ H`, with `H₁ᵀ H₁ = 1`. -/
structure RealForm (ρ : Γ →* M3) where
  H : M3
  herm : Hᴴ = H
  orth : Hᵀ * H = 1
  det : H.det = 1
  pos : ∀ x : V3, x ≠ 0 → 0 < star x ⬝ᵥ (H *ᵥ x)
  comm : ∀ g, H * ρ g = (ρ g).map star * H

theorem exists_realForm {μ : ℂ} (hμ : (avgH ρ)ᵀ * avgH ρ = μ • 1) : Nonempty (RealForm ρ) := by
  obtain ⟨r, hr, hμr⟩ := exists_real_of_pos (scalar_pos hO hμ)
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hP := avgH_posDef hO
  set c : ℂ := ((r⁻¹ : ℝ) : ℂ)
  have hc : star c = c := Complex.conj_ofReal _
  have hcpos : 0 < c := by
    rw [show c = ((r⁻¹ : ℝ) : ℂ) from rfl]; exact_mod_cast inv_pos.mpr hr
  have horth : (c • avgH ρ)ᵀ * (c • avgH ρ) = 1 := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul, hμr, smul_smul,
      show c = (r : ℂ)⁻¹ by simp [c]]
    rw [show (r : ℂ)⁻¹ * (r : ℂ)⁻¹ * (r : ℂ) ^ 2 = 1 by field_simp, one_smul]
  refine ⟨⟨c • avgH ρ, by rw [conjTranspose_smul, hc, avgH_herm hO], horth, ?_, ?_, ?_⟩⟩
  · have h1 : (c • avgH ρ).det * (c • avgH ρ).det = 1 := by
      have := congrArg det horth
      rwa [det_mul, det_transpose, det_one] at this
    have hdpos : 0 < (c • avgH ρ).det := by
      rw [det_smul, Fintype.card_fin]
      exact mul_pos (pow_pos hcpos 3) hP.det_pos
    have : ((c • avgH ρ).det - 1) * ((c • avgH ρ).det + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      rw [eq_neg_of_add_eq_zero_left h] at hdpos
      have := (Complex.pos_iff.mp hdpos).1
      norm_num at this
  · intro x hx
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hcpos (hP.dotProduct_mulVec_pos hx)
  · intro g
    rw [Matrix.smul_mul, Matrix.mul_smul, avgH_mul hO]


end Avg

section Frame

variable {Γ : Type*} [Group Γ] {ρ : Γ →* M3} (F : RealForm ρ)

namespace RealForm

/-- The antilinear involution `J x = conj(H₁ x)`. -/
noncomputable def J (x : V3) : V3 := star (F.H *ᵥ x)

theorem H_transpose : F.Hᵀ = F.H.map star := by
  ext i j
  have := congrFun (congrFun F.herm j) i
  simp only [conjTranspose_apply] at this
  simp [transpose_apply, ← this]

theorem J_J (x : V3) : F.J (F.J x) = x := by
  simp only [J]
  rw [star_mulVec', star_star, mulVec_mulVec]
  rw [show F.H.map star = F.Hᵀ from (H_transpose F).symm, F.orth, one_mulVec]

theorem J_add (x y : V3) : F.J (x + y) = F.J x + F.J y := by simp [J, mulVec_add]

theorem J_smul (a : ℂ) (x : V3) : F.J (a • x) = star a • F.J x := by
  simp [J, mulVec_smul, star_smul]

theorem J_cross (a b : V3) : F.J (a ⨯₃ b) = F.J a ⨯₃ F.J b := by
  simp only [J]
  rw [cross_of_orth F.orth F.det, star_cross]

theorem J_comm (g : Γ) (x : V3) : ρ g *ᵥ F.J x = F.J (ρ g *ᵥ x) := by
  simp only [J]
  rw [mulVec_mulVec, F.comm, star_mulVec', star_mulVec', map_star_mul, map_star_map_star,
    ← mulVec_mulVec]

theorem fix_dot_real {x y : V3} (hx : F.J x = x) (hy : F.J y = y) : star (x ⬝ᵥ y) = x ⬝ᵥ y := by
  have hx' : star x = F.H *ᵥ x := by conv_lhs => rw [← hx, J, star_star]
  have hy' : star y = F.H *ᵥ y := by conv_lhs => rw [← hy, J, star_star]
  rw [← star_dotProduct_star, hy', hx', dot_mulVec_orth F.orth, dotProduct_comm]

theorem fix_dot_pos {x : V3} (hx : F.J x = x) (h0 : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have hp := F.pos x h0
  have : x ⬝ᵥ x = star x ⬝ᵥ (F.H *ᵥ x) := by
    calc x ⬝ᵥ x = F.J x ⬝ᵥ x := by rw [hx]
      _ = _ := by rw [J, star_mulVec, ← dotProduct_mulVec, F.herm]
  rw [this]; exact hp

theorem J_real_smul (t : ℝ) (x : V3) : F.J ((t : ℂ) • x) = (t : ℂ) • F.J x := by
  rw [J_smul, Complex.star_def, Complex.conj_ofReal]

/-- Normalization of a nonzero fixed vector. -/
theorem exists_unit {x : V3} (hx : F.J x = x) (h0 : x ≠ 0) :
    ∃ t : ℝ, F.J ((t : ℂ) • x) = (t : ℂ) • x ∧ ((t : ℂ) • x) ⬝ᵥ ((t : ℂ) • x) = 1 := by
  obtain ⟨r, hr, hxr⟩ := exists_real_of_pos (fix_dot_pos F hx h0)
  refine ⟨r⁻¹, by rw [J_real_smul, hx], ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hxr]
  have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp

theorem fixP (y : V3) : F.J (y + F.J y) = y + F.J y := by rw [J_add, J_J, add_comm]

theorem fixQ (y : V3) : F.J (Complex.I • (y - F.J y)) = Complex.I • (y - F.J y) := by
  have hsub : F.J (y - F.J y) = F.J y - y := by
    simp only [J, mulVec_sub, star_sub]
    rw [show star (F.H *ᵥ star (F.H *ᵥ y)) = F.J (F.J y) from rfl, J_J]
  rw [J_smul, hsub, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem decomp (y : V3) :
    (2 : ℂ) • y = (y + F.J y) - Complex.I • (Complex.I • (y - F.J y)) := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, two_smul]
  abel

/-- If every fixed vector satisfies a linear condition `L z = 0`, then `L = 0`. -/
theorem linear_of_fix (L : V3 →ₗ[ℂ] V3) (hL : ∀ z, F.J z = z → L z = 0) (y : V3) : L y = 0 := by
  have h := congrArg L (decomp F y)
  rw [map_smul, map_sub, map_smul, hL _ (fixP F y), hL _ (fixQ F y), smul_zero, sub_zero] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

theorem exists_fix_ne_zero : ∃ x : V3, F.J x = x ∧ x ≠ 0 := by
  by_contra h
  push Not at h
  have := linear_of_fix F LinearMap.id (fun z hz => h z hz) (Pi.single 0 1)
  have := congrFun this 0
  simp at this

/-- **An orthonormal pair of fixed vectors.** -/
theorem exists_frame : ∃ v₁ v₂ : V3, F.J v₁ = v₁ ∧ F.J v₂ = v₂ ∧ v₁ ⬝ᵥ v₁ = 1 ∧ v₂ ⬝ᵥ v₂ = 1 ∧
    v₁ ⬝ᵥ v₂ = 0 := by
  obtain ⟨x, hx, hx0⟩ := exists_fix_ne_zero F
  obtain ⟨t, hv1, hn1⟩ := exists_unit F hx hx0
  set v₁ := (t : ℂ) • x
  obtain ⟨z, hz, hz0⟩ : ∃ z : V3, F.J z = z ∧ v₁ ⨯₃ z ≠ 0 := by
    by_contra h
    push Not at h
    have hL := linear_of_fix F (crossProduct v₁) (fun z hz => h z hz)
    have hv : v₁ = 0 := by
      ext i
      have h0 := congrFun (hL (Pi.single 0 1)) 
      have h1 := congrFun (hL (Pi.single 1 1))
      fin_cases i
      · simpa [cross_apply] using h1 2
      · simpa [cross_apply] using h0 2
      · simpa [cross_apply] using h0 1
    rw [hv, zero_dotProduct] at hn1
    exact zero_ne_one hn1
  have hfz : F.J (v₁ ⨯₃ z) = v₁ ⨯₃ z := by rw [J_cross, hv1, hz]
  obtain ⟨s, hv2, hn2⟩ := exists_unit F hfz hz0
  refine ⟨v₁, (s : ℂ) • (v₁ ⨯₃ z), hv1, hv2, hn1, hn2, ?_⟩
  rw [dotProduct_smul, dot_self_cross, smul_zero]


/-- The frame `v₁, v₂, v₁ × v₂`. -/
def frameVec (v₁ v₂ : V3) : Fin 3 → V3 := ![v₁, v₂, v₁ ⨯₃ v₂]

/-- The matrix with columns `v₁, v₂, v₁ × v₂`. -/
def frameMat (v₁ v₂ : V3) : M3 := Matrix.of fun i j => frameVec v₁ v₂ j i

theorem frame_entry (v₁ v₂ : V3) (M : M3) (i j : Fin 3) :
    ((frameMat v₁ v₂)ᵀ * M * frameMat v₁ v₂) i j
      = frameVec v₁ v₂ i ⬝ᵥ (M *ᵥ frameVec v₁ v₂ j) := by
  simp only [mul_apply, transpose_apply, frameMat, of_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem frame_orth {v₁ v₂ : V3} (h1 : v₁ ⬝ᵥ v₁ = 1) (h2 : v₂ ⬝ᵥ v₂ = 1) (h12 : v₁ ⬝ᵥ v₂ = 0) :
    (frameMat v₁ v₂)ᵀ * frameMat v₁ v₂ = 1 := by
  have h21 : v₂ ⬝ᵥ v₁ = 0 := by rw [dotProduct_comm, h12]
  ext i j
  have := frame_entry v₁ v₂ 1 i j
  rw [Matrix.mul_one, one_mulVec] at this
  rw [this]
  fin_cases i <;> fin_cases j <;>
    simp [frameVec, h1, h2, h12, h21, dot_self_cross, dot_cross_self, cross_dot_cross]
  · rw [dotProduct_comm, dot_self_cross]
  · rw [dotProduct_comm, dot_cross_self]

/-- **The scalar case gives an embedding into `SO(3, ℝ)`.** -/
theorem exists_so3 (F : RealForm ρ) (hO : ∀ g, (ρ g)ᵀ * ρ g = 1) (hD : ∀ g, (ρ g).det = 1) :
    ∃ σ : Γ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ g, σ g = 1 → ρ g = 1 := by
  obtain ⟨v₁, v₂, hf1, hf2, h1, h2, h12⟩ := exists_frame F
  set C := frameMat v₁ v₂
  have hCC : Cᵀ * C = 1 := frame_orth h1 h2 h12
  have hCC' : C * Cᵀ = 1 := mul_eq_one_comm.mp hCC
  have hfix : ∀ k, F.J (frameVec v₁ v₂ k) = frameVec v₁ v₂ k := by
    intro k; fin_cases k
    · exact hf1
    · exact hf2
    · change F.J (v₁ ⨯₃ v₂) = v₁ ⨯₃ v₂
      rw [J_cross, hf1, hf2]
  set T : Γ → M3 := fun g => Cᵀ * ρ g * C
  have hreal : ∀ g i j, star (T g i j) = T g i j := by
    intro g i j
    simp only [T]
    rw [frame_entry]
    exact fix_dot_real F (hfix i) (by rw [← J_comm, hfix])
  let σ0 : Γ → Matrix (Fin 3) (Fin 3) ℝ := fun g => Matrix.of fun i j => (T g i j).re
  have hσ0 : ∀ g, (σ0 g).map Complex.ofRealHom = T g := by
    intro g; ext i j
    have := hreal g i j
    rw [Complex.star_def, Complex.conj_eq_iff_re] at this
    simp only [map_apply, of_apply, σ0, Complex.ofRealHom_eq_coe]
    exact this
  have hinj : Function.Injective (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.map Complex.ofRealHom) :=
    Matrix.map_injective Complex.ofReal_injective
  have hTmul : ∀ g h, T (g * h) = T g * T h := by
    intro g h
    calc T (g * h) = Cᵀ * ρ g * (C * Cᵀ) * ρ h * C := by
          rw [hCC', Matrix.mul_one]; simp only [T, map_mul, Matrix.mul_assoc]
      _ = T g * T h := by simp only [T, Matrix.mul_assoc]
  have hT1 : T 1 = 1 := by simp only [T, map_one, Matrix.mul_one, hCC]
  have hTorth : ∀ g, (T g)ᵀ * T g = 1 := by
    intro g
    calc (T g)ᵀ * T g = Cᵀ * (ρ g)ᵀ * (C * Cᵀ) * ρ g * C := by
          simp only [T, transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = Cᵀ * ((ρ g)ᵀ * ρ g) * C := by
          rw [hCC', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hO, Matrix.mul_one, hCC]
  have hTdet : ∀ g, (T g).det = 1 := by
    intro g
    simp only [T]
    rw [det_mul, det_mul, hD, mul_one, ← det_mul, hCC, det_one]
  have hmem : ∀ g, σ0 g ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    intro g
    refine (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨(Matrix.mem_orthogonalGroup_iff' _ _).mpr ?_, ?_⟩
    · apply hinj
      simp only [Matrix.map_mul, transpose_map, hσ0, hTorth, Matrix.map_one, map_zero, map_one]
    · have := RingHom.map_det Complex.ofRealHom (σ0 g)
      rw [RingHom.mapMatrix_apply, hσ0, hTdet, Complex.ofRealHom_eq_coe] at this
      exact Complex.ofReal_eq_one.mp this
  refine ⟨{ toFun := fun g => ⟨σ0 g, hmem g⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    change σ0 1 = 1
    apply hinj
    change (σ0 1).map _ = (1 : Matrix (Fin 3) (Fin 3) ℝ).map _
    rw [hσ0, hT1, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro g h
    apply Subtype.ext
    apply hinj
    change (σ0 (g * h)).map _ = (σ0 g * σ0 h).map _
    rw [Matrix.map_mul, hσ0, hσ0, hσ0, hTmul]
  · intro g hg
    have h1 : σ0 g = 1 := congrArg Subtype.val hg
    have h2 : T g = 1 := by rw [← hσ0, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc ρ g = (C * Cᵀ) * ρ g * (C * Cᵀ) := by rw [hCC', Matrix.one_mul, Matrix.mul_one]
      _ = C * T g * Cᵀ := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hCC']

end RealForm

/-- **Finite subgroups of `SO(3, ℂ)`** (the unitary trick). A finite group acting by
complex-orthogonal matrices of determinant `1` either fixes an anisotropic unit vector up to sign,
or embeds in `SO(3, ℝ)` (compatibly with `ρ`). -/
theorem so3c_dichotomy [Fintype Γ] (hO : ∀ g, (ρ g)ᵀ * ρ g = 1) (hD : ∀ g, (ρ g).det = 1) :
    (∃ u : V3, u ⬝ᵥ u = 1 ∧ ∀ g, ρ g *ᵥ u = u ∨ ρ g *ᵥ u = -u) ∨
      ∃ σ : Γ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ g, σ g = 1 → ρ g = 1 := by
  rcases scalar_or_line hO with ⟨μ, hμ⟩ | ⟨v, hv, hinv⟩
  · right
    obtain ⟨F⟩ := exists_realForm hO hμ
    exact RealForm.exists_so3 F hO hD
  · left
    exact pm_of_line hO hD hv hinv

end Frame

end VOA.Classification.COne.SO3C

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN Matrix

/-! ## Assembly -/

private theorem inCOneList_of_iso' {𝒱 𝒲 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲]
    [Module ℂ 𝒲] {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}
    (h : VOAIsomorphic V T) (hT : InCOneList T) : InCOneList V := by
  rcases hT with ⟨m, hm, h'⟩ | ⟨m, hm, h2, h'⟩ | ⟨G, hG, h'⟩ | ⟨G, hG, h'⟩ | ⟨G, hG, h'⟩
  · exact Or.inl ⟨m, hm, voaIso_trans' h h'⟩
  · exact Or.inr (Or.inl ⟨m, hm, h2, voaIso_trans' h h'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨G, hG, voaIso_trans' h h'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨G, hG, voaIso_trans' h h'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨G, hG, voaIso_trans' h h'⟩)))

/-- If `φ G φ⁻¹` lies in the torus normalizer, `V₂^G` is in the list. -/
theorem inCOneList_of_conj_normalizer (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G]
    {φ : Aut (V2m 1 le_rfl)} (hN : InNormalizer 1 le_rfl (G.map (MulAut.conj φ).toMonoidHom)) :
    InCOneList (orbifoldVOA G) := by
  haveI : Finite (G.map (MulAut.conj φ).toMonoidHom) :=
    Finite.of_surjective _ (G.equivMapOfInjective _ (MulAut.conj φ).injective).surjective
  exact inCOneList_of_iso' (orbifold_conj_iso φ G) (inCOneList_orbifold_V2_normalizer_all _ hN)

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- An automorphism sending `h ↦ ±h` lies in the torus normalizer. -/
theorem normalizer_of_pm (y : Aut V1)
    (h : y (hSt (latP 1) (a1 1)) = hSt (latP 1) (a1 1) ∨
      y (hSt (latP 1) (a1 1)) = -hSt (latP 1) (a1 1)) :
    (∃ u, y = charU 1 le_rfl u) ∨ (∃ u, y = thetaM 1 le_rfl * charU 1 le_rfl u) := by
  rcases h with h | h
  · exact Or.inl (eq_charU_of_fix_h y h)
  · right
    obtain ⟨u, hu⟩ := eq_charU_of_fix_h (thetaM 1 le_rfl * y) (by
      rw [Aut.mul_apply, h, map_neg, thetaAut_apply, thetaLat_hSt', neg_neg])
    refine ⟨u, ?_⟩
    rw [← hu, ← mul_assoc, thetaM_mul_self, one_mul]

/-- A subgroup of `Aut V₂` preserving an anisotropic axis of `(V₂)₁` up to sign is conjugate
into the torus normalizer (move the axis to `h` by transitivity). -/
theorem inNormalizer_conj_of_axis (G : Subgroup (Aut V1)) {u : Fin 3 → ℂ}
    (hu : u ⬝ᵥ u = 1) (hpm : ∀ x ∈ G, rho x *ᵥ u = u ∨ rho x *ᵥ u = -u) :
    ∃ φ : Aut V1, InNormalizer 1 le_rfl (G.map (MulAut.conj φ).toMonoidHom) := by
  obtain ⟨φ, hφ⟩ := exists_aut_xyzL_eq_h u hu
  refine ⟨φ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hinv : φ⁻¹ (hSt (latP 1) (a1 1)) = xyzL u := by
    rw [← hφ, Aut.inv_apply]; exact φ.toLinearEquiv.symm_apply_apply _
  apply normalizer_of_pm
  change (φ * x * φ⁻¹) _ = _ ∨ (φ * x * φ⁻¹) _ = _
  rw [Aut.mul_apply, Aut.mul_apply, hinv, aut_xyzL]
  rcases hpm x hx with h | h
  · left; rw [h, hφ]
  · right; rw [h, map_neg, map_neg, hφ]

/-- **C6b: every finite orbifold of `V₂` is in the list** (the `m = 1` half of
`IEnumeration`, Gannon–Rayhaun Prop. C.4). Unconditional. -/
theorem enumeration_m1 (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : Finite G) :
    InCOneList (orbifoldVOA G) := by
  haveI := hG
  haveI : Fintype G := Fintype.ofFinite G
  rcases SO3C.so3c_dichotomy (ρ := rho.comp G.subtype)
      (fun g => rho_transpose_mul (g : Aut (V2m 1 le_rfl)))
      (fun g => rho_det (g : Aut (V2m 1 le_rfl))) with ⟨u, hu, hpm⟩ | ⟨σ, hσ1⟩
  · obtain ⟨φ, hN⟩ := inNormalizer_conj_of_axis G hu (fun x hx => hpm ⟨x, hx⟩)
    exact inCOneList_of_conj_normalizer G hN
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (rho_injective ((hσ1 g hg).trans (map_one rho).symm))
  set K := σ.range
  haveI : Finite K := Finite.of_surjective _ (MonoidHom.ofInjective hσ).surjective
  let eK : G ≃* K := MonoidHom.ofInjective hσ
  rcases FiniteRotation.classification (G := K) with he | ⟨n, hn, -, he⟩ | he | he | he <;>
    obtain ⟨e⟩ := he
  · haveI : IsCyclic G := isCyclic_of_surjective (eK.trans e).symm
      (eK.trans e).symm.surjective
    obtain ⟨φ, hN⟩ := @inNormalizer_conj_of_isCyclic G hG this
    exact inCOneList_of_conj_normalizer G hN
  · obtain ⟨φ, hN⟩ := @inNormalizer_conj_of_dihedral G hG n hn (eK.trans e)
    exact inCOneList_of_conj_normalizer G hN
  · exact Or.inr (Or.inr (Or.inl ⟨G, ⟨eK.trans e⟩, voaIsomorphic_refl' _⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨G, ⟨eK.trans e⟩, voaIsomorphic_refl' _⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨G, ⟨eK.trans e⟩, voaIsomorphic_refl' _⟩)))

/-- **The enumeration input `IEnumeration` is a theorem**: with the `m ≥ 2` half
(`inCOneList_orbifold_V2m`, C7b), every finite orbifold of every `V_{2m}` is in the list. -/
theorem iEnumeration : IEnumeration := by
  intro m hm G hG
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    exact enumeration_m1 G hG
  · exact inCOneList_orbifold_V2m m hm h G

end VOA.Classification.COne
