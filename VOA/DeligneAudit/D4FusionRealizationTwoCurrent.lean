/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoAction

/-! The exact two-jet current operator in standard tensor coordinates. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorLoop

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
    (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

/-- All evaluation points are kept explicit in the actual coordinate formula. -/
theorem coordinates_current (z : Fin 2 → ℂ) (c : Fin n) (k : ℕ)
    (v : D1TensorG.Space n 2) :
    coordinates n ((D1TensorG.rep f hJ hskew z).op c k v) =
      ((z 0 ^ k • leftAction (siteAction (D1SiteG.zeroOp f c)) +
        ((k : ℂ) * z 0 ^ (k - 1)) • leftAction (siteAction (D1SiteG.oneOp c))) +
       (z 1 ^ k • rightAction (siteAction (D1SiteG.zeroOp f c)) +
        ((k : ℂ) * z 1 ^ (k - 1)) • rightAction (siteAction (D1SiteG.oneOp c))))
        (coordinates n v) := by
  rw [D1TensorG.op_eq_jetOp]
  simp only [JetInterpolation.jetOp, Fin.sum_univ_two, LinearMap.add_apply,
    LinearMap.smul_apply, map_add, map_smul, coordinates_local_left,
    coordinates_local_right]

/-- The chosen two distinct evaluation points. -/
def twoPoints : Fin 2 → ℂ := ![0, 1]

/-- The finite calculation uses the actual coadjoint and one-jet matrices. -/
def coordinateOp (c : Fin n) (k : ℕ) : Module.End ℂ (TwoVector n) :=
  (match k with
    | 0 => leftAction (siteAction (D1SiteG.zeroOp f c))
    | 1 => leftAction (siteAction (D1SiteG.oneOp c))
    | _ + 2 => 0) +
  rightAction (siteAction (D1SiteG.zeroOp f c)) +
    (k : ℂ) • rightAction (siteAction (D1SiteG.oneOp c))

/-- Every mode, including arbitrarily high modes, is the actual source operator. -/
theorem coordinates_current_two (c : Fin n) (k : ℕ) (v : D1TensorG.Space n 2) :
    coordinates n ((D1TensorG.rep f hJ hskew twoPoints).op c k v) =
      coordinateOp f c k (coordinates n v) := by
  rw [coordinates_current]
  rcases k with _ | _ | k <;>
    simp [twoPoints, coordinateOp, LinearMap.add_apply, LinearMap.smul_apply, add_assoc]

/-- The highest tensor generator has the expected single standard coordinate. -/
theorem coordinates_generator (c₀ : Fin n) :
    coordinates n (PiTensorProduct.tprod ℂ (fun _ : Fin 2 => D1SiteG.w c₀)) =
      Pi.single (Sum.inl c₀, Sum.inl c₀) 1 := by
  funext p
  rw [coordinates_tprod]
  rcases p with ⟨i, j⟩
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases hi : i = c₀ <;> by_cases hj : j = c₀ <;>
            simp_all [D1SiteG.w, Pi.single_apply, Prod.mk.injEq, eq_comm]
      | inr j => cases j; simp [D1SiteG.w]
  | inr i => cases i; simp [D1SiteG.w]

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.coordinates_current_two
#print axioms VOA.DeligneAudit.D4Two.coordinates_generator
