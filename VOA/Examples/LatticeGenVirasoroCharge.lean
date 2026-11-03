/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVirasoroEminus

/-!
# The charge-seed translation covariance `DCovariant TrecGen (Y(e^α,z))`

Combining the `E⁺` Virasoro covariance (`LvirN_comm_aExpVecZ`), the `E⁻` defect
(`LvirN_comm_EminusVec`), and the momentum-dressing commutator
`[chargeOsc γ(-1), EEVec β] = ⟨β,γ⟩·EEVec β(r+1)` (from `alphaFieldGen_comm_EEVec` at `j=0`), the
`TrecGen`-covariance of the charge vertex operator `Y(e^β,z)` follows: the `chargeOsc β(-1)` defect
of `[L₋₁, EEVec β]` is cancelled by the momentum coupling `chargeOsc(β+γ)(-1) − chargeOsc γ(-1)`.

Cross-charge lift of A₁'s `Trec_Yemα_DCovariant`.  All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-- **The E⁺ Virasoro covariance** `[L₋₁, E⁺(β)_t] = (t+1)·E⁺(β)_{t+1}` (from `LvirN_comm_aExpVecZ`). -/
theorem LvirN_comm_EplusVecField (β : L.carrier) (t : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * EplusVecField L β t
      - EplusVecField L β t * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((t + 1 : ℤ)) • EplusVecField L β (t + 1) := by
  rw [EplusVecField_eq_aExpVecZ, EplusVecField_eq_aExpVecZ, show -(t + 1) = -t - 1 from by ring,
    LvirN_comm_aExpVecZ L β (-t),
    show (1 : ℂ) - ((-t : ℤ) : ℂ) = (((t + 1 : ℤ)) : ℂ) from by push_cast; ring]
  exact Int.cast_smul_eq_zsmul ℂ (t + 1) (aExpVecZ L β (-t - 1))

/-- `chargeOsc` is additive in the lattice vector. -/
theorem chargeOsc_add (α β : L.carrier) (n : ℤ) :
    chargeOsc L (α + β) n = chargeOsc L α n + chargeOsc L β n := by
  rw [chargeOsc_eq_sum, chargeOsc_eq_sum, chargeOsc_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chargeCoord_add, add_smul]

/-- **The momentum-dressing commutator** `[chargeOsc γ(-1), EEVec β r] = ⟨β,γ⟩·EEVec β(r+1)`: the
frame sum `∑_a chargeCoord γ a · [α^a(-1), EEVec β r] = ∑_a chargeCoord γ a · chargeCoord β a ·
EEVec β(r+1) = ⟨β,γ⟩·EEVec β(r+1)`. -/
theorem chargeOsc_neg1_comm_EEVec (hPos : L.PosDef) (γ β : L.carrier) (r : ℤ) :
    chargeOsc L γ (-1) * EEVec L β r - EEVec L β r * chargeOsc L γ (-1)
      = ((L.form β γ : ℤ) : ℂ) • EEVec L β (r + 1) := by
  rw [chargeOsc_eq_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ a, ((chargeCoord L γ a • oscN (rank L) 1 a (-1)) * EEVec L β r
            - EEVec L β r * (chargeCoord L γ a • oscN (rank L) 1 a (-1))))
        = ∑ a, chargeCoord L γ a • (chargeCoord L β a • EEVec L β (r + 1)) from
      Finset.sum_congr rfl fun a _ => by
        rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
        congr 1
        have h := alphaFieldGen_comm_EEVec L a β 0 r
        rw [if_neg (by norm_num : ¬ (0 : ℤ) = -1), bracketDist_apply, currentN_apply,
          show -(0 : ℤ) - 1 = -1 from by ring, show r + 0 + 1 = r + 1 from by ring] at h
        exact h]
  rw [show (∑ a, chargeCoord L γ a • (chargeCoord L β a • EEVec L β (r + 1)))
        = (∑ a, chargeCoord L γ a * chargeCoord L β a) • EEVec L β (r + 1) from by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun a _ => by rw [smul_smul],
    sum_chargeCoord L hPos γ β, form_symm L γ β]

/-- **The `EEVec` `L₋₁`-covariance with the `chargeOsc β(-1)` defect**:
`[L₋₁, EEVec β r] = (r+1)·EEVec β(r+1) − chargeOsc β(-1)·EEVec β r`.  nprod-Leibniz combine of the
`E⁻` defect (`LvirN_comm_EminusVecField`) and the `E⁺` clean covariance (`LvirN_comm_EplusVecField`).
Cross-charge lift of A₁'s `LvirN_comm_EEC`. -/
theorem LvirN_comm_EEVec (β : L.carrier) (r : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * EEVec L β r - EEVec L β r * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((r + 1 : ℤ)) • EEVec L β (r + 1) - chargeOsc L β (-1) * EEVec L β r := by
  set Lv : End ℂ (FockN (rank L)) := HeisenbergN.LvirN (rank L) 1 (-1) with hLv
  have ha := EminusVecField_isField L β
  have hb := EplusVecField_isField L β
  have NO_term : ∀ k : ℤ,
      Lv * normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k)
        - normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k) * Lv
      = normalOrdered (VOA.deriv (EminusVecField L β)) (EplusVecField L β) k (r - k)
        + normalOrdered (EminusVecField L β) (VOA.deriv (EplusVecField L β)) k (r - k)
        - chargeOsc L β (-1) * normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k) := by
    intro k
    by_cases hk : 0 ≤ k
    · simp only [normalOrdered_apply, if_pos hk, deriv_apply]
      rw [show Lv * (EminusVecField L β k * EplusVecField L β (r - k))
              - EminusVecField L β k * EplusVecField L β (r - k) * Lv
            = (Lv * EminusVecField L β k - EminusVecField L β k * Lv) * EplusVecField L β (r - k)
              + EminusVecField L β k * (Lv * EplusVecField L β (r - k)
                  - EplusVecField L β (r - k) * Lv) from by
            simp only [sub_mul, mul_sub, mul_assoc]; abel,
        hLv, LvirN_comm_EminusVecField, LvirN_comm_EplusVecField]
      simp only [sub_mul, smul_mul_assoc]
      rw [show chargeOsc L β (-1) * EminusVecField L β k * EplusVecField L β (r - k)
          = chargeOsc L β (-1) * (EminusVecField L β k * EplusVecField L β (r - k)) from
            mul_assoc _ _ _]
      abel
    · simp only [normalOrdered_apply, if_neg hk]
      have hEm0 : EminusVecField L β k = 0 := EminusVecField_neg L β (by omega)
      have hdEm0 : VOA.deriv (EminusVecField L β) k = 0 := by
        rw [deriv_apply]
        rcases lt_or_eq_of_le (show k + 1 ≤ 0 by omega) with h | h
        · rw [EminusVecField_neg L β h]; exact smul_zero _
        · rw [h, zero_smul]
      rw [hEm0, hdEm0]; simp
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, EEVec, nprod_apply,
    map_finsum Lv (normalOrdered_diag_support_finite ha hb r x), nprod_apply]
  have hfinDL : (Function.support (fun k : ℤ =>
      Lv (normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero])
  have hcleanFin : (Function.support (fun k : ℤ =>
      normalOrdered (VOA.deriv (EminusVecField L β)) (EplusVecField L β) k (r - k) x
        + normalOrdered (EminusVecField L β) (VOA.deriv (EplusVecField L β)) k (r - k) x)).Finite := by
    apply Set.Finite.subset ((normalOrdered_diag_support_finite ha.deriv hb r x).union
      (normalOrdered_diag_support_finite ha hb.deriv r x))
    intro k hk
    rw [Function.mem_support] at hk
    simp only [Set.mem_union, Function.mem_support]
    by_contra hcon
    push_neg at hcon
    exact hk (by rw [hcon.1, hcon.2, add_zero])
  have hdefectFin : (Function.support (fun k : ℤ =>
      chargeOsc L β (-1) (normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero])
  have hclean : (∑ᶠ k : ℤ, (normalOrdered (VOA.deriv (EminusVecField L β)) (EplusVecField L β) k (r - k) x
        + normalOrdered (EminusVecField L β) (VOA.deriv (EplusVecField L β)) k (r - k) x))
      = ((r + 1 : ℤ) • EEVec L β (r + 1)) x := by
    rw [finsum_add_distrib (normalOrdered_diag_support_finite ha.deriv hb r x)
        (normalOrdered_diag_support_finite ha hb.deriv r x),
      show (∑ᶠ k : ℤ, normalOrdered (VOA.deriv (EminusVecField L β)) (EplusVecField L β) k (r - k) x)
          = VOA.nprod ha.deriv hb r x from (nprod_apply ha.deriv hb r x).symm,
      show (∑ᶠ k : ℤ, normalOrdered (EminusVecField L β) (VOA.deriv (EplusVecField L β)) k (r - k) x)
          = VOA.nprod ha hb.deriv r x from (nprod_apply ha hb.deriv r x).symm]
    have hadd : (VOA.nprod ha.deriv hb r) x + (VOA.nprod ha hb.deriv r) x
        = (VOA.deriv (VOA.nprod ha hb)) r x := by rw [deriv_nprod]; rfl
    rw [hadd, deriv_apply]; rfl
  have hdefect : (∑ᶠ k : ℤ, chargeOsc L β (-1) (normalOrdered (EminusVecField L β) (EplusVecField L β) k (r - k) x))
      = (chargeOsc L β (-1) * EEVec L β r) x := by
    rw [Module.End.mul_apply, EEVec, nprod_apply,
      map_finsum (chargeOsc L β (-1)) (normalOrdered_diag_support_finite ha hb r x)]
  rw [← finsum_sub_distrib hfinDL (normalOrdered_diag_support_finite ha hb r (Lv x)),
    finsum_congr (fun k => by
      have := congrArg (fun (T : End ℂ (FockN (rank L))) => T x) (NO_term k)
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.smul_apply] using this),
    finsum_sub_distrib hcleanFin hdefectFin, hclean, hdefect]
  exact (LinearMap.sub_apply _ _ x).symm

/-! ## §Assembly  `TrecGen`-covariance of the charge seed. -/

/-- `TrecGen` on a basis state: `L₋₁` on the boson factor plus the momentum `chargeOsc γ(-1)`. -/
theorem TrecGen_tmul (q : FockN (rank L)) (γ : L.carrier) :
    TrecGen L (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-1) q) γ
        + latStateGen L (chargeOsc L γ (-1) q) γ := by
  have hrt : LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1))
      (latStateGen L q γ) = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-1) q) γ := by
    show LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) (q ⊗ₜ[ℂ] eGen L γ)
        = (HeisenbergN.LvirN (rank L) 1 (-1) q) ⊗ₜ[ℂ] eGen L γ
    rw [LinearMap.rTensor_tmul]
  have hmom : momGen L (latStateGen L q γ) = latStateGen L (chargeOsc L γ (-1) q) γ := by
    rw [momGen, LinearMap.coe_sum, Finset.sum_apply,
      show latStateGen L (chargeOsc L γ (-1) q) γ = (chargeOsc L γ (-1) q) ⊗ₜ[ℂ] eGen L γ from rfl,
      chargeOsc_eq_sum, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Module.End.mul_apply,
      show zGradeOpGen L a (latStateGen L q γ) = chargeCoord L γ a • latStateGen L q γ from
        zGradeOpGen_latStateGen L a q γ,
      show latStateGen L q γ = q ⊗ₜ[ℂ] eGen L γ from rfl,
      map_smul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul', LinearMap.smul_apply]
  rw [TrecGen, LinearMap.add_apply, hrt, hmom]

/-- **The boson operator identity** behind the charge covariance: the `chargeOsc β(-1)` defect of
`[L₋₁, EEVec β]` is cancelled by the momentum coupling `chargeOsc(β+γ)(-1) − chargeOsc γ(-1)`, and
the residual `[chargeOsc γ(-1), EEVec β]` supplies the `⟨β,γ⟩` shift, leaving `(s+1)·EEVec`. -/
theorem TrecGen_Yeαvec_bosonOp (hPos : L.PosDef) (β : L.carrier) (s : ℤ) (γ : L.carrier) :
    HeisenbergN.LvirN (rank L) 1 (-1) * EEVec L β (s - L.form β γ)
        - EEVec L β (s - L.form β γ) * HeisenbergN.LvirN (rank L) 1 (-1)
      + chargeOsc L (β + γ) (-1) * EEVec L β (s - L.form β γ)
      - EEVec L β (s - L.form β γ) * chargeOsc L γ (-1)
    = ((s + 1 : ℤ)) • EEVec L β (s + 1 - L.form β γ) := by
  rw [show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring, chargeOsc_add, add_mul,
    ← Int.cast_smul_eq_zsmul ℂ (s + 1)]
  have hL := LvirN_comm_EEVec L β (s - L.form β γ)
  have hcomm := chargeOsc_neg1_comm_EEVec L hPos γ β (s - L.form β γ)
  rw [← Int.cast_smul_eq_zsmul ℂ ((s - L.form β γ) + 1)] at hL
  have hLZ : HeisenbergN.LvirN (rank L) 1 (-1) * EEVec L β (s - L.form β γ)
      = EEVec L β (s - L.form β γ) * HeisenbergN.LvirN (rank L) 1 (-1)
        + ((((s - L.form β γ) + 1 : ℤ) : ℂ) • EEVec L β ((s - L.form β γ) + 1)
          - chargeOsc L β (-1) * EEVec L β (s - L.form β γ)) := by rw [← hL]; abel
  have hcZ : chargeOsc L γ (-1) * EEVec L β (s - L.form β γ)
      = EEVec L β (s - L.form β γ) * chargeOsc L γ (-1)
        + ((L.form β γ : ℤ) : ℂ) • EEVec L β ((s - L.form β γ) + 1) := by rw [← hcomm]; abel
  rw [hLZ, hcZ]
  push_cast
  module

/-- The charge seed covariance on a basis state `p ⊗ e^γ`. -/
theorem TrecGen_Yeαvec_on_state (hPos : L.PosDef) (β : L.carrier) (s : ℤ) (γ : L.carrier)
    (p : FockN (rank L)) :
    (TrecGen L * Yeαvec L β s - Yeαvec L β s * TrecGen L) (latStateGen L p γ)
      = ((s + 1 : ℤ)) • Yeαvec L β (s + 1) (latStateGen L p γ) := by
  have hp := congrArg (fun T : End ℂ (FockN (rank L)) => T p) (TrecGen_Yeαvec_bosonOp L hPos β s γ)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at hp
  rw [← Int.cast_smul_eq_zsmul ℂ (s + 1)] at hp
  have hbracket : HeisenbergN.LvirN (rank L) 1 (-1) (EEVec L β (s - L.form β γ) p)
        + chargeOsc L (β + γ) (-1) (EEVec L β (s - L.form β γ) p)
        - (EEVec L β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
          + EEVec L β (s - L.form β γ) (chargeOsc L γ (-1) p))
      = (((s + 1 : ℤ) : ℂ)) • EEVec L β ((s - L.form β γ) + 1) p := by
    rw [show HeisenbergN.LvirN (rank L) 1 (-1) (EEVec L β (s - L.form β γ) p)
            + chargeOsc L (β + γ) (-1) (EEVec L β (s - L.form β γ) p)
            - (EEVec L β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
              + EEVec L β (s - L.form β γ) (chargeOsc L γ (-1) p))
          = HeisenbergN.LvirN (rank L) 1 (-1) (EEVec L β (s - L.form β γ) p)
            - EEVec L β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
            + chargeOsc L (β + γ) (-1) (EEVec L β (s - L.form β γ) p)
            - EEVec L β (s - L.form β γ) (chargeOsc L γ (-1) p) from by abel,
      hp, show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring, LinearMap.smul_apply]
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Yeαvec_tmul, map_smul,
    TrecGen_tmul, TrecGen_tmul, map_add, Yeαvec_tmul, Yeαvec_tmul, smul_add,
    ← latStateGen_smul_boson, ← latStateGen_smul_boson, ← latStateGen_smul_boson,
    ← latStateGen_smul_boson, ← latStateGen_add_boson, ← latStateGen_add_boson,
    ← latStateGen_sub_boson,
    show latticeCocycle L β γ • HeisenbergN.LvirN (rank L) 1 (-1) (EEVec L β (s - L.form β γ) p)
          + latticeCocycle L β γ • chargeOsc L (β + γ) (-1) (EEVec L β (s - L.form β γ) p)
          - (latticeCocycle L β γ • EEVec L β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
            + latticeCocycle L β γ • EEVec L β (s - L.form β γ) (chargeOsc L γ (-1) p))
        = latticeCocycle L β γ • ((((s + 1 : ℤ) : ℂ)) • EEVec L β ((s - L.form β γ) + 1) p) from by
      rw [← smul_add, ← smul_add, ← smul_sub, hbracket],
    latStateGen_smul_boson, latStateGen_smul_boson,
    ← Int.cast_smul_eq_zsmul ℂ (s + 1), Yeαvec_tmul,
    smul_comm, show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring]

/-- **The charge generator `Y(e^β,z)` is `TrecGen`-covariant** — the charged-generator crux for the
lattice reconstruction (charged analogue of `TrecGen_alphaLatGen_DCovariant`). -/
theorem TrecGen_Yeαvec_DCovariant (hPos : L.PosDef) (β : L.carrier) :
    Reconstruction.DCovariant (TrecGen L) (Yeαvec L β) := by
  intro s
  refine LinearMap.ext fun y => ?_
  change (TrecGen L * Yeαvec L β s - Yeαvec L β s * TrecGen L) y
    = ((s + 1 : ℤ)) • Yeαvec L β (s + 1) y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, zsmul_zero]
  | add y1 y2 h1 h2 =>
      rw [map_add (TrecGen L * Yeαvec L β s - Yeαvec L β s * TrecGen L) y1 y2, h1, h2,
        map_add (Yeαvec L β (s + 1)) y1 y2]
      exact (smul_add _ _ _).symm
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; simp only [map_zero, zsmul_zero]
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]
          simp only [map_add, h1, h2]
          exact (smul_add _ _ _).symm
      | single γ a =>
          rw [(Finsupp.smul_single_one γ a).symm,
            show (Finsupp.single γ (1 : ℂ) : L.carrier →₀ ℂ) = eGen L γ from rfl]
          erw [TensorProduct.tmul_smul, map_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            TrecGen_Yeαvec_on_state L hPos β s γ]
          rw [← Int.cast_smul_eq_zsmul ℂ (s + 1) (Yeαvec L β (s + 1) (latStateGen L p γ)),
            ← Int.cast_smul_eq_zsmul ℂ (s + 1) (a • Yeαvec L β (s + 1) (latStateGen L p γ)), smul_comm]

/-- Every boson generator field `genFieldLatGen a i` is `TrecGen`-covariant (lift the boson current
covariance along `∂_z` and the `(i!)⁻¹` scalar). -/
theorem TrecGen_genFieldLatGen_DCovariant (a : Fin (rank L)) (i : ℕ) :
    Reconstruction.DCovariant (TrecGen L) (genFieldLatGen L a i) := by
  rw [genFieldLatGen]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (TrecGen_alphaLatGen_DCovariant L a) i)

end VOA.LatGen
