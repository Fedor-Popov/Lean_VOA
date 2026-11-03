/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenReconstruct
import VOA.Examples.HeisenbergNVertex

/-!
# Boson generator fields on `V_L` (general even positive-definite `L`)

The `rTensor`-lift of the rank-`(rank L)` orthonormal Heisenberg currents to
`LatModuleGen L = FockN (rank L) ⊗ (L.carrier →₀ ℂ)`, together with the lattice-momentum zero mode
`α^a₀ = zGradeOpGen a` (acting on `e^β` by the direction-`a` frame coordinate `orthCoord β a`).
Cross-charge lift of A₁'s `LatticeLift`/`LatticeFields`/`LatticeWordFields` boson machinery:

* `zGradeLGen a` / `zGradeOpGen a` — the momentum operator on the charge factor.
* `alphaLatGen a` — the boson current `α^a(z)` on `V_L` (lifted current + momentum at index `-1`).
* `liftFGen` — the reusable `rTensor` field-lift, commuting with `bracketDist`/`mulBySubPow`.
* `alphaLatGen_isField`, `alphaLatGen_self_local` (the momentum drops out of the boson commutator),
  `genFieldLatGen`, its `IsField`/self-locality/vacuum-annihilation/`z⁰`-creation.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-! ## §1  The lattice-momentum operator `α^a₀ = zGradeOpGen a`. -/

/-- `chargeCoord L 0 a = 0` (the neutral charge sector has zero momentum). -/
theorem chargeCoord_zero (a : Fin (rank L)) : chargeCoord L (0 : L.carrier) a = 0 := by
  rw [chargeCoord]
  have hc : coordR L (0 : L.carrier) = 0 := by
    funext i
    simp only [coordR, coord, map_zero, Finsupp.zero_apply, Int.cast_zero, Pi.zero_apply]
  have h0 : orthCoord L (0 : L.carrier) (rankEquiv L a) = 0 := by
    rw [orthCoord, hc, Matrix.mulVec_zero]; rfl
  rw [h0, Complex.ofReal_zero]

/-- The **direction-`a` momentum** `α^a₀ = ⟨e_a, ·⟩` on `ℂ{L}`: diagonal, acting by the frame
coordinate `chargeCoord β a` on `e^β`. -/
noncomputable def zGradeLGen (a : Fin (rank L)) : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ (fun γ => (chargeCoord L γ a) •
    (Finsupp.lsingle γ : ℂ →ₗ[ℂ] (L.carrier →₀ ℂ)))

theorem zGradeLGen_eGen (a : Fin (rank L)) (β : L.carrier) :
    zGradeLGen L a (eGen L β) = (chargeCoord L β a) • eGen L β := by
  rw [zGradeLGen]
  show (Finsupp.lsum ℂ (fun γ => (chargeCoord L γ a) •
      (Finsupp.lsingle γ : ℂ →ₗ[ℂ] (L.carrier →₀ ℂ)))) (Finsupp.single β 1) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]
  simp only [eGen]

/-- The **momentum operator** `α^a₀ : LatModuleGen L →ₗ LatModuleGen L` (boson factor untouched). -/
noncomputable def zGradeOpGen (a : Fin (rank L)) : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  LinearMap.lTensor (FockN (rank L)) (zGradeLGen L a)

theorem zGradeOpGen_latStateGen (a : Fin (rank L)) (p : FockN (rank L)) (β : L.carrier) :
    zGradeOpGen L a (latStateGen L p β)
      = (chargeCoord L β a) • latStateGen L p β := by
  rw [zGradeOpGen, latStateGen, LinearMap.lTensor_tmul, zGradeLGen_eGen, TensorProduct.tmul_smul]

theorem zGradeOpGen_vacuum (a : Fin (rank L)) : zGradeOpGen L a (latVacuumGen L) = 0 := by
  rw [latVacuumGen, zGradeOpGen_latStateGen, chargeCoord_zero, zero_smul]

/-! ## §2  The `rTensor`-lift `FockN (rank L) → LatModuleGen L`. -/

/-- Lift a boson field to `V_L` (act on the Fock tensor factor). -/
noncomputable def liftFGen (f : FormalDist (End ℂ (FockN (rank L)))) :
    FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => LinearMap.rTensor (L.carrier →₀ ℂ) (f j)

/-- Lift a two-variable boson distribution to `V_L`. -/
noncomputable def liftF₂Gen (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    FormalDist₂ (End ℂ (LatModuleGen L)) :=
  fun m n => LinearMap.rTensor (L.carrier →₀ ℂ) (F m n)

theorem liftF₂Gen_zero : liftF₂Gen L (0 : FormalDist₂ (End ℂ (FockN (rank L)))) = 0 := by
  funext m n
  change LinearMap.rTensor (L.carrier →₀ ℂ) (0 : End ℂ (FockN (rank L))) = 0
  rw [LinearMap.rTensor_zero]

theorem rTensorGen_mul (f g : End ℂ (FockN (rank L))) :
    LinearMap.rTensor (L.carrier →₀ ℂ) (f * g)
      = LinearMap.rTensor (L.carrier →₀ ℂ) f * LinearMap.rTensor (L.carrier →₀ ℂ) g := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp]

theorem bracketDist_liftFGen (f g : FormalDist (End ℂ (FockN (rank L)))) :
    bracketDist (liftFGen L f) (liftFGen L g) = liftF₂Gen L (bracketDist f g) := by
  funext m n
  rw [bracketDist_apply]
  change LinearMap.rTensor (L.carrier →₀ ℂ) (f m) * LinearMap.rTensor (L.carrier →₀ ℂ) (g n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (g n) * LinearMap.rTensor (L.carrier →₀ ℂ) (f m)
    = LinearMap.rTensor (L.carrier →₀ ℂ) ((bracketDist f g) m n)
  rw [bracketDist_apply, ← rTensorGen_mul, ← rTensorGen_mul, ← LinearMap.rTensor_sub]

theorem mulBySub_liftF₂Gen (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    mulBySub (liftF₂Gen L F) = liftF₂Gen L (mulBySub F) := by
  funext m n
  rw [mulBySub_apply]
  change LinearMap.rTensor (L.carrier →₀ ℂ) (F (m - 1) n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (F m (n - 1))
    = LinearMap.rTensor (L.carrier →₀ ℂ) ((mulBySub F) m n)
  rw [mulBySub_apply, ← LinearMap.rTensor_sub]

theorem mulBySubPow_liftF₂Gen (N : ℕ) (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    mulBySubPow N (liftF₂Gen L F) = liftF₂Gen L (mulBySubPow N F) := by
  induction N generalizing F with
  | zero => rw [mulBySubPow_zero, mulBySubPow_zero]; rfl
  | succ n ih =>
      have h1 : mulBySubPow (n + 1) (liftF₂Gen L F) = mulBySub (mulBySubPow n (liftF₂Gen L F)) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      have h2 : mulBySubPow (n + 1) F = mulBySub (mulBySubPow n F) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      rw [h1, ih, mulBySub_liftF₂Gen, h2]

theorem Local_liftFGen {f g : FormalDist (End ℂ (FockN (rank L)))} (h : Local f g) :
    Local (liftFGen L f) (liftFGen L g) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [bracketDist_liftFGen, mulBySubPow_liftF₂Gen, hN, liftF₂Gen_zero]⟩

theorem liftFGen_isField {f : FormalDist (End ℂ (FockN (rank L)))} (hf : IsField f) :
    IsField (liftFGen L f) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (liftFGen L f n).map_zero⟩
  | tmul p g =>
      obtain ⟨Bp, hBp⟩ := hf p
      refine ⟨Bp, fun n hn => ?_⟩
      change LinearMap.rTensor (L.carrier →₀ ℂ) (f n) (p ⊗ₜ[ℂ] g) = 0
      rw [LinearMap.rTensor_tmul, hBp n hn, TensorProduct.zero_tmul]
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (liftFGen L f n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]

/-! ## §3  The boson current `α^a(z)` on `V_L`. -/

/-- The **boson current** `α^a(z)` on `V_L`: the lifted orthonormal Heisenberg current plus the
zero-mode momentum `α^a₀ = zGradeOpGen a` at the `z₁⁻¹`-coefficient (index `-1`). -/
noncomputable def alphaLatGen (a : Fin (rank L)) : FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j)
    + (if j = -1 then zGradeOpGen L a else 0)

theorem alphaLatGen_apply (a : Fin (rank L)) (j : ℤ) :
    alphaLatGen L a j = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j)
      + (if j = -1 then zGradeOpGen L a else 0) := rfl

/-- **The boson current is a field**: the lifted current is a field, the momentum sits only at `-1`. -/
theorem alphaLatGen_isField (a : Fin (rank L)) : IsField (alphaLatGen L a) := by
  intro x
  obtain ⟨B, hB⟩ := liftFGen_isField L (currentN_isField (rank L) 1 a) x
  refine ⟨min B (-1), fun n hn => ?_⟩
  rw [alphaLatGen_apply, if_neg (by omega : ¬ n = -1), LinearMap.add_apply, LinearMap.zero_apply,
    add_zero]
  exact hB n (lt_of_lt_of_le hn (min_le_left _ _))

/-! ## §4  Boson-current self-locality (the momentum drops out of the commutator). -/

/-- `zGradeOpGen a` commutes with every lifted boson endomorphism (different tensor factors). -/
theorem zGradeOpGen_comm_rTensor (a : Fin (rank L)) (f : End ℂ (FockN (rank L))) :
    zGradeOpGen L a * (LinearMap.rTensor (L.carrier →₀ ℂ) f)
      = (LinearMap.rTensor (L.carrier →₀ ℂ) f) * zGradeOpGen L a := by
  simp only [zGradeOpGen, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-- The two direction momenta commute (both diagonal on `ℂ{L}`). -/
theorem zGradeOpGen_comm (a b : Fin (rank L)) :
    zGradeOpGen L a * zGradeOpGen L b = zGradeOpGen L b * zGradeOpGen L a := by
  simp only [zGradeOpGen, Module.End.mul_eq_comp, ← LinearMap.lTensor_comp]
  congr 1
  refine Finsupp.lhom_ext fun γ c => ?_
  simp only [LinearMap.comp_apply, show (Finsupp.single γ c : L.carrier →₀ ℂ)
    = c • eGen L γ from by rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one], map_smul,
    zGradeLGen_eGen, map_smul, zGradeLGen_eGen, smul_smul, mul_comm]

/-- The `alphaLatGen`-bracket equals the lifted current bracket: the `zGradeOpGen` corrections
commute out of the commutator. -/
theorem bracketDist_alphaLatGen (a b : Fin (rank L)) :
    bracketDist (alphaLatGen L a) (alphaLatGen L b)
      = bracketDist (liftFGen L (currentN (rank L) 1 a)) (liftFGen L (currentN (rank L) 1 b)) := by
  have key : ∀ (Am An cm cn : End ℂ (LatModuleGen L)),
      cn * Am = Am * cn → cm * An = An * cm → cm * cn = cn * cm →
      (Am + cm) * (An + cn) - (An + cn) * (Am + cm) = Am * An - An * Am := by
    intro Am An cm cn h1 h2 h3
    simp only [mul_add, add_mul]; rw [h1, h2, h3]; abel
  funext m n
  rw [bracketDist_apply, bracketDist_apply]
  change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
          + (if m = -1 then zGradeOpGen L a else 0))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
          + (if n = -1 then zGradeOpGen L b else 0))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
          + (if n = -1 then zGradeOpGen L b else 0))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
          + (if m = -1 then zGradeOpGen L a else 0))
    = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
        * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
        * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
  refine key _ _ _ _ ?_ ?_ ?_
  · by_cases hn : n = -1
    · rw [if_pos hn, zGradeOpGen_comm_rTensor]
    · rw [if_neg hn, zero_mul, mul_zero]
  · by_cases hm : m = -1
    · rw [if_pos hm, zGradeOpGen_comm_rTensor]
    · rw [if_neg hm, zero_mul, mul_zero]
  · by_cases hm : m = -1 <;> by_cases hn : n = -1
    · rw [if_pos hm, if_pos hn, zGradeOpGen_comm]
    · rw [if_pos hm, if_neg hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_pos hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_neg hn, mul_zero]

/-- **The boson-current mutual locality on `V_L`** (`Local (alphaLatGen a) (alphaLatGen b)`), lifted
from the Heisenberg `currentN_local`. -/
theorem alphaLatGen_self_local (a b : Fin (rank L)) :
    Local (alphaLatGen L a) (alphaLatGen L b) := by
  rw [Local, bracketDist_alphaLatGen]
  exact Local_liftFGen L (currentN_local (rank L) 1 a b)

/-! ## §5  The scaled boson generator field `genFieldLatGen a i = (i!)⁻¹ ∂^i α^a`. -/

/-- The **scaled boson generator field** `genFieldLatGen a i := (i!)⁻¹ · ∂_z^i α^a(z)` — the field
`Y(α^a₋(i+1)·|0⟩, z)`.  Cross-charge lift of A₁'s `genFieldLat`. -/
noncomputable def genFieldLatGen (a : Fin (rank L)) (i : ℕ) : FormalDist (End ℂ (LatModuleGen L)) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a))

theorem genFieldLatGen_isField (a : Fin (rank L)) (i : ℕ) : IsField (genFieldLatGen L a i) := by
  intro x
  obtain ⟨B, hB⟩ := (alphaLatGen_isField L a).deriv_iterate i x
  exact ⟨B, fun n hn => by
    change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

theorem genFieldLatGen_zero (a : Fin (rank L)) : genFieldLatGen L a 0 = alphaLatGen L a := by
  rw [genFieldLatGen, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

theorem dalphaLatGen_local (a b : Fin (rank L)) (i j : ℕ) :
    Local (VOA.deriv^[i] (alphaLatGen L a)) (VOA.deriv^[j] (alphaLatGen L b)) :=
  ((alphaLatGen_self_local L a b).deriv_iterate_left i).deriv_iterate_right j

theorem genFieldLatGen_local (a b : Fin (rank L)) (i j : ℕ) :
    Local (genFieldLatGen L a i) (genFieldLatGen L b j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a)))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] (alphaLatGen L b)))
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dalphaLatGen_local L a b i j))

/-- The boson current annihilates the vacuum below degree `0`. -/
theorem alphaLatGen_vacuum_neg (a : Fin (rank L)) {q : ℤ} (hq : q < 0) :
    alphaLatGen L a q (latVacuumGen L) = 0 := by
  rw [alphaLatGen_apply, LinearMap.add_apply]
  have hb : LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a q) (latVacuumGen L) = 0 := by
    rw [latVacuumGen, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
      oscN_vacuum (rank L) 1 a (-q - 1) (by omega), TensorProduct.zero_tmul]
  rw [hb, zero_add]
  by_cases hq1 : q = -1
  · rw [if_pos hq1, zGradeOpGen_vacuum]
  · rw [if_neg hq1]; rfl

/-- The boson generator field annihilates the vacuum below degree `0`. -/
theorem genFieldLatGen_vacuum_neg (a : Fin (rank L)) (i : ℕ) {q : ℤ} (hq : q < 0) :
    genFieldLatGen L a i q (latVacuumGen L) = 0 := by
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a)) q) (latVacuumGen L) = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [alphaLatGen_vacuum_neg L a (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The boson generator field's `z⁰`-coefficient is the lifted boson creation `α^a₋(i+1)`. -/
theorem genFieldLatGen_zero_op (a : Fin (rank L)) (i : ℕ) :
    (genFieldLatGen L a i) 0 = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a i) := by
  change (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (alphaLatGen L a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, alphaLatGen_apply,
    if_neg (by omega : ¬ (i : ℤ) = -1), add_zero]

end VOA.LatGen
