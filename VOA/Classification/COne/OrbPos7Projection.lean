import VOA.Classification.COne.OrbPos7Current

/-! # Charge-residue projections for the torus shift -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open Moonshine.LatticeTwisted
open scoped TensorProduct

noncomputable def chargeDiagonal (c : ℤ → ℂ) : Space →ₗ[ℂ] Space :=
  TensorProduct.map LinearMap.id
    (Finsupp.lsum ℂ fun β : ℤ => LinearMap.toSpanSingleton ℂ (ℤ →₀ ℂ)
      (c β • eGen (latP 1) β))

theorem chargeDiagonal_latState (c : ℤ → ℂ) (p : Osc) (β : ℤ) :
    chargeDiagonal c (latStateGen (latP 1) p β) = c β • latStateGen (latP 1) p β := by
  rw [latStateGen, chargeDiagonal, TensorProduct.map_tmul]
  change p ⊗ₜ[ℂ] ((Finsupp.lsum ℂ _) (Finsupp.single β 1)) = _
  rw [Finsupp.lsum_single]
  change p ⊗ₜ[ℂ] ((1 : ℂ) • (c β • eGen (latP 1) β)) = _
  rw [one_smul, TensorProduct.tmul_smul]

noncomputable def residueProjection (n : ℕ) (a e : ℤ) : Space →ₗ[ℂ] Space :=
  chargeDiagonal fun β => if (e - a * β) % (n : ℤ) = 0 then 1 else 0

theorem residueProjection_latState (n : ℕ) (a e β : ℤ) (p : Osc) :
    residueProjection n a e (latStateGen (latP 1) p β) =
      if (e - a * β) % (n : ℤ) = 0 then latStateGen (latP 1) p β else 0 := by
  rw [residueProjection, chargeDiagonal_latState]
  split_ifs <;> simp

theorem chargeDiagonal_current (c : ℤ → ℂ) (ℓ : ℤ) (v : Space) :
    chargeDiagonal c ((V2m 1 le_rfl).smul h ℓ v) =
      (V2m 1 le_rfl).smul h ℓ (chargeDiagonal c v) := by
  have hh : (chargeDiagonal c).comp (mode ((V2m 1 le_rfl).Y h) ℓ) =
      (mode ((V2m 1 le_rfl).Y h) ℓ).comp (chargeDiagonal c) := by
    apply LinearMap.ext_on_range (latStateGen_span (latP 1))
    rintro ⟨p, β⟩
    change ℤ at β
    change chargeDiagonal c ((V2m 1 le_rfl).smul h ℓ (latStateGen (latP 1) p β)) =
      (V2m 1 le_rfl).smul h ℓ (chargeDiagonal c (latStateGen (latP 1) p β))
    have hs := smul_hgen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (a0 1) ℓ p β
    change (V2m 1 le_rfl).smul h ℓ (latStateGen (latP 1) p β) = _ at hs
    rw [chargeDiagonal_latState, PreVertexAlgebra.smul_smul_right, hs, map_add]
    change chargeDiagonal c (latStateGen (latP 1) _ β) + _ = _
    rw [chargeDiagonal_latState, smul_add]
    congr 1
    split_ifs
    · rw [map_smul]
      change chargeCoord (latP 1) β (a0 1) • chargeDiagonal c (latStateGen (latP 1) p β) = _
      rw [chargeDiagonal_latState, smul_comm]
      rfl
    · rw [map_zero, smul_zero]
  exact congrArg (fun f : Space →ₗ[ℂ] Space => f v) hh

theorem residueProjection_current (n : ℕ) (a e ℓ : ℤ) (v : Space) :
    residueProjection n a e ((V2m 1 le_rfl).smul h ℓ v) =
      (V2m 1 le_rfl).smul h ℓ (residueProjection n a e v) :=
  chargeDiagonal_current _ ℓ v

/-- On the indicated torus eigenspace, the charge-residue projection is the identity. -/
theorem residueProjection_eigen {n : ℕ} (hn : 0 < n) (a e : ℤ) (u : Space)
    (hu : shiftAut n a u = phase n e • u) : residueProjection n a e u = u := by
  let Q := chargeDiagonal fun β => if (e - a * β) % (n : ℤ) = 0 then 0
    else (phase n (a*β) - phase n e)⁻¹
  have hh : Q.comp ((shiftAut n a).toLinearEquiv.toLinearMap - phase n e • LinearMap.id) =
      LinearMap.id - residueProjection n a e := by
    apply LinearMap.ext_on_range (latStateGen_span (latP 1))
    rintro ⟨p, β⟩
    change ℤ at β
    change Q (shiftAut n a (latStateGen (latP 1) p β) -
      phase n e • latStateGen (latP 1) p β) =
      latStateGen (latP 1) p β - residueProjection n a e (latStateGen (latP 1) p β)
    rw [shiftAut_latState, ← sub_smul, map_smul, residueProjection_latState]
    dsimp only [Q]
    rw [chargeDiagonal_latState]
    by_cases he : (e - a * β) % (n : ℤ) = 0
    · rw [if_pos he, if_pos he, zero_smul, smul_zero, sub_self]
    · have hne : phase n (a*β) - phase n e ≠ 0 := by
        intro hh
        exact he ((phase_eq_iff hn e (a*β)).mp (sub_eq_zero.mp hh).symm)
      rw [if_neg he, if_neg he, smul_smul, mul_inv_cancel₀ hne, one_smul, sub_zero]
  have hv := congrArg (fun f : Space →ₗ[ℂ] Space => f u) hh
  change Q (shiftAut n a u - phase n e • u) = u - residueProjection n a e u at hv
  rw [hu, sub_self, map_zero] at hv
  exact (sub_eq_zero.mp hv.symm).symm

end VOA.Classification.COne.OrbPos7
