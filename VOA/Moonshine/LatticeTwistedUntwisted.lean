/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedFields
import VOA.Moonshine.HeisenbergTwistedModuleProductFormula

/-!
# Products in the untwisted lattice VOA `V_L`  (Moonshine step M6)

The right-hand sides of the twisted product formula live in `V_L = latticeVOAGen L`.  This file
computes the products needed there:

* `hgen b = h_b(−1)𝟙` and its products `smul_hgen` (`b₍ₙ₎(p ⊗ e^β)` is the oscillator `b(n)`
  on `p`, plus `β_b` at `n = 0`); `smul_hgen_neg` (creation as `X_{(k,b)} ·`),
  `smul_hgen_echg_nonneg`;
* `echg α = e^α` and `smul_echg_echg`:
  `e^α₍ℓ₎e^β = ε(α,β) S_{−ℓ−1−⟨α,β⟩}(α) e^{α+β}` (vector Schur polynomial `vSchur`);
* `T_echg`: `T e^α = Σ_b α_b h_b(−1) e^α`;
* generic VOA facts: the translation is a derivation (`T_smul'`), `(Tu)₍ₙ₎ = −n u₍ₙ₋₁₎`;
* the involution: `theta_hgen` (`θ h_b = −h_b`), the projections `piE e u = ½(u + (−1)ᵉ θu)`
  (`piE_smul_hgen`, `piE_of_mem`).

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

/-! ## Generic VOA facts -/

section Generic

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

theorem T_eq_smul_omega' (u : 𝒱) :
    W.toPreVertexAlgebra.T u = W.smul W.conformalVector 0 u := by
  rw [VertexOperatorAlgebra.T_eq_Lneg1, VertexOperatorAlgebra.L_def]
  rfl

/-- `(Tu)₍ₙ₎ = −n u₍ₙ₋₁₎`, with a complex scalar. -/
theorem smul_T_left' (u : 𝒱) (n : ℤ) (w : 𝒱) :
    W.smul (W.toPreVertexAlgebra.T u) n w = (-(n : ℂ)) • W.smul u (n - 1) w := by
  rw [PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, VertexOperatorAlgebra.mode_Y_T,
    ← Int.cast_smul_eq_zsmul ℂ (-n), LinearMap.smul_apply, Int.cast_neg]

/-- `T` is a derivation of the products: `T(b₍q₎w) = b₍q₎(Tw) − q b₍q₋₁₎w`. -/
theorem T_smul' (u : 𝒱) (q : ℤ) (w : 𝒱) :
    W.toPreVertexAlgebra.T (W.smul u q w)
      = W.smul u q (W.toPreVertexAlgebra.T w) - (q : ℂ) • W.smul u (q - 1) w := by
  rw [T_eq_smul_omega', VertexOperatorAlgebra.zeroMode_leibniz, ← T_eq_smul_omega',
    ← T_eq_smul_omega', smul_T_left', neg_smul, add_comm, ← sub_eq_add_neg]

end Generic

/-! ## The lattice VOA -/

section Lattice

open IntegralLattice LatGen

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-- The generator `h_b(−1)𝟙 = X_{(0,b)} ⊗ e^0`. -/
noncomputable def hgen (b : Fin (rank L)) : LatModuleGen L :=
  (X (0, b) : FockN (rank L)) ⊗ₜ[ℂ] eGen L 0

/-- The exponential state `e^α = 1 ⊗ e^α`. -/
noncomputable abbrev echg (α : L.carrier) : LatModuleGen L := latChargeGen L α

theorem echg_eq (α : L.carrier) : echg L α = (1 : FockN (rank L)) ⊗ₜ[ℂ] eGen L α := rfl

theorem nprod_eq_of_eq_idField {V : Type*} [AddCommGroup V] [Module ℂ V]
    {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) (h : b = idField) :
    VOA.nprod ha hb = a := by
  subst h
  exact nprod_idField ha

theorem Yeαvec_zero_eq_idField : Yeαvec L 0 = (idField : FormalDist (End ℂ (LatModuleGen L))) := by
  funext t
  refine LinearMap.ext fun y => ?_
  rw [Yeαvec_zero_apply, idField_apply]
  split_ifs <;> rfl

/-- `Y(h_b(−1)𝟙, z) = α^b(z)`. -/
theorem Y_hgen (b : Fin (rank L)) :
    (latticeVOAGen L hEven hPos).Y (hgen L b) = alphaLatGen L b := by
  have h1 : hgen L b = wordStateLatGen L [((0 : ℕ), b)] 0 := by
    rw [wordStateLatGen_eq, wordStateN_cons, wordStateN_nil, mul_one]
    rfl
  change YfullGen L hEven hPos (hgen L b) = _
  rw [h1, YfullGen_word, YwordLatGen_cons]
  rw [nprod_eq_of_eq_idField _ _ (by rw [YwordLatGen_nil]; exact Yeαvec_zero_eq_idField L)]
  exact genFieldLatGen_zero L b

/-- **The generator products**: `b₍ₙ₎(p ⊗ e^β) = b(n)p ⊗ e^β + δ_{n0} β_b p ⊗ e^β`. -/
theorem smul_hgen (b : Fin (rank L)) (n : ℤ) (p : FockN (rank L)) (β : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (hgen L b) n (p ⊗ₜ[ℂ] eGen L β)
      = (oscN (rank L) 1 b n p) ⊗ₜ[ℂ] eGen L β
        + (if n = 0 then chargeCoord L β b • (p ⊗ₜ[ℂ] eGen L β) else 0) := by
  rw [PreVertexAlgebra.smul_def]
  rw [show (latticeVOAGen L hEven hPos).toPreVertexAlgebra.Y (hgen L b) = alphaLatGen L b from
    Y_hgen L hEven hPos b, mode_apply, alphaLatGen_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    currentN_apply, show -(-n - 1) - 1 = n by ring]
  congr 1
  by_cases hn : n = 0
  · rw [if_pos (by omega), if_pos hn]
    exact zGradeOpGen_latStateGen L b p β
  · rw [if_neg (by omega), if_neg hn]
    rfl

/-- Creation: `b₍₋ₖ₋₁₎w = (X_{(k,b)} · ⊗ 1) w`. -/
theorem smul_hgen_neg (b : Fin (rank L)) (k : ℕ) (w : LatModuleGen L) :
    (latticeVOAGen L hEven hPos).smul (hgen L b) (-(k : ℤ) - 1) w
      = (LinearMap.mulLeft ℂ (X (k, b) : FockN (rank L))).rTensor _ w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [PreVertexAlgebra.smul_zero_right, map_zero]
  | add x y hx hy => rw [PreVertexAlgebra.smul_add_right, hx, hy, map_add]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => rw [TensorProduct.tmul_zero, PreVertexAlgebra.smul_zero_right, map_zero]
      | add g₁ g₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, PreVertexAlgebra.smul_add_right, h₁, h₂, map_add]
      | single β c =>
          rw [show (Finsupp.single β c : L.carrier →₀ ℂ) = c • eGen L β by
              rw [eGen, Finsupp.smul_single_one],
            TensorProduct.tmul_smul, PreVertexAlgebra.smul_smul_right, smul_hgen,
            if_neg (by omega), add_zero, oscN_neg_eq_mulXN, LinearMap.map_smul,
            LinearMap.rTensor_tmul, LinearMap.mulLeft_apply]

theorem smul_hgen_echg_nonneg (b : Fin (rank L)) {n : ℤ} (hn : 0 ≤ n) (β : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (hgen L b) n (echg L β)
      = if n = 0 then chargeCoord L β b • echg L β else 0 := by
  rw [echg_eq, smul_hgen]
  rcases eq_or_lt_of_le hn with h0 | hpos
  · subst h0
    rw [oscN_zero, LinearMap.zero_apply, TensorProduct.zero_tmul, zero_add, if_pos rfl]
  · rw [oscN_apply_pos _ _ _ hpos, if_neg (show n ≠ 0 by omega), add_zero,
      show (1 : FockN (rank L)) = MvPolynomial.C 1 by rw [map_one], pderiv_C, smul_zero, smul_zero,
      TensorProduct.zero_tmul]

/-- **The exponential products**:
`e^α₍ℓ₎e^β = ε(α,β) S_{−ℓ−1−⟨α,β⟩}(α) e^{α+β}` (zero when the index is negative). -/
theorem smul_echg_echg (α β : L.carrier) (ℓ : ℤ) :
    (latticeVOAGen L hEven hPos).smul (echg L α) ℓ (echg L β)
      = latticeCocycle L α β • ((if 0 ≤ -ℓ - 1 - L.form α β then
          vSchur L α (-ℓ - 1 - L.form α β).toNat else 0) ⊗ₜ[ℂ] eGen L (α + β)) := by
  rw [PreVertexAlgebra.smul_def]
  change mode (YfullGen L hEven hPos (wordStateLatGen L [] α)) ℓ (latStateGen L
    (vacuumN (rank L)) β) = _
  rw [YfullGen_word, YwordLatGen_nil, mode_apply, Yeαvec_tmul, latStateGen, EEVec_vacuum]

theorem latticeCocycle_zero_mul (α : L.carrier) : L.form α 0 = 0 := by simp

/-- `T e^α = Σ_b α_b h_b(−1) e^α`. -/
theorem T_echg (α : L.carrier) :
    (latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (echg L α)
      = ∑ b, chargeCoord L α b •
          (latticeVOAGen L hEven hPos).smul (hgen L b) (-1) (echg L α) := by
  have hv1 : vSchur L α 1 = vVar L α 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, vSchur_succ]
    simp [vSchur_zero]
  rw [PreVertexAlgebra.T_apply]
  change (latticeVOAGen L hEven hPos).smul (echg L α) (-2) (echg L 0) = _
  rw [smul_echg_echg, latticeCocycle_zero_right, one_smul, latticeCocycle_zero_mul, add_zero,
    if_pos (by norm_num), show (-(-2 : ℤ) - 1 - 0).toNat = 1 by norm_num, hv1, vVar,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num, smul_hgen_neg, echg_eq,
    LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, mul_one, TensorProduct.smul_tmul']

/-! ## The involution -/

theorem theta_hgen (b : Fin (rank L)) : thetaLat L (hgen L b) = -hgen L b := by
  rw [hgen, thetaLat_tmul, sigmaN_X, neg_zero, TensorProduct.neg_tmul]

/-- `θ(b₍ₘ₎w) = −b₍ₘ₎(θw)`. -/
theorem theta_smul_hgen (b : Fin (rank L)) (m : ℤ) (w : LatModuleGen L) :
    thetaLat L ((latticeVOAGen L hEven hPos).smul (hgen L b) m w)
      = -(latticeVOAGen L hEven hPos).smul (hgen L b) m (thetaLat L w) := by
  have h := thetaLat_mode L hEven hPos (hgen L b) m w
  rw [theta_hgen, map_neg] at h
  change thetaLat L ((latticeVOAGen L hEven hPos).smul (hgen L b) m w) = _ at h
  rw [h]
  rfl

/-- **The projection onto the `θ`-class of `e`**: `piE e u = ½(u + (−1)ᵉ θu)`. -/
noncomputable def piE (e : ℤ) (u : LatModuleGen L) : LatModuleGen L :=
  (1 / 2 : ℂ) • (u + ((-1 : ℂ) ^ e) • thetaLat L u)

theorem piE_add (e : ℤ) (u v : LatModuleGen L) : piE L e (u + v) = piE L e u + piE L e v := by
  simp only [piE, map_add, smul_add]; abel

theorem piE_smul (e : ℤ) (c : ℂ) (u : LatModuleGen L) : piE L e (c • u) = c • piE L e u := by
  simp only [piE, map_smul, smul_add, smul_comm c]

/-- `piE` and the generator modes: `piE e (b₍ₘ₎w) = b₍ₘ₎ (piE (e−1) w)`. -/
theorem piE_smul_hgen (e : ℤ) (b : Fin (rank L)) (m : ℤ) (w : LatModuleGen L) :
    piE L e ((latticeVOAGen L hEven hPos).smul (hgen L b) m w)
      = (latticeVOAGen L hEven hPos).smul (hgen L b) m (piE L (e - 1) w) := by
  simp only [piE, theta_smul_hgen L hEven hPos, PreVertexAlgebra.smul_smul_right,
    PreVertexAlgebra.smul_add_right]
  congr 2
  rw [smul_neg, ← neg_smul, zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  congr 1
  field_simp

/-- On a `θ`-eigenvector of eigenvalue `(−1)ʲ` and `e ≡ j`, `piE e u = u`. -/
theorem piE_of_mem (j : ℕ) (u : LatModuleGen L)
    (hu : u ∈ (thetaAut L hEven hPos).twistedEigenspace 2 j) (e : ℤ) (he : (e + j) % 2 = 0) :
    piE L e u = u := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, HeisenbergN.exp_twisted_two] at hu
  have hu' : thetaLat L u = ((-1 : ℂ) ^ j) • u := hu
  rw [piE, hu', smul_smul, ← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    neg_one_zpow_congr (b := 0) (by omega), zpow_zero, one_smul, ← two_smul ℂ u, smul_smul]
  norm_num

end Lattice

end VOA.Moonshine.LatticeTwisted
