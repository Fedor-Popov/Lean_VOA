import VOA.Huang.GenusOneWardClauses
import VOA.Huang.GenusOneScaleModes

/-!
# The minus-one identity for the shifted conformal state `ω − c/24`

For `ω` the zero-mode trace is the `L₀`-weighted trace; for the vacuum the
square mode `1[m]` is `δ_{m,−1}`. Together the minus-one identity for
`ω̃ = ω − (c/24)𝟙` reads

`Φ(ω̃[−1]x, y) = Θ_{h−c/24} Φ(x,y) + Σ G_{2m+2} Φ(ω̃[2m+1]x, y)
  + Σ (Π_m + δ_{m0}/2) Φ(x, ω̃[m]y)`,

with `Θ_λ` multiplying the level-`n` coefficient by `λ + n`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound)
open VOA.Huang.GenusOne (sqAct)
open VOA.Huang.GenusOne.SquareModule (shiftedOmega)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The twisted Euler operator on the outer variable. -/
def thetaR2 (lam : ℂ) (f : R2) : R2 := mk2 fun n k => (lam + n) * c2 f n k

theorem thetaR2_add (lam : ℂ) (f g : R2) : thetaR2 lam (f + g) = thetaR2 lam f + thetaR2 lam g :=
  ext2 fun n k => by simp [thetaR2]; ring

theorem thetaR2_sub_const (lam a : ℂ) (f : R2) :
    thetaR2 lam f - a • f = thetaR2 (lam - a) f :=
  ext2 fun n k => by simp [thetaR2]; ring

section Mixed
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem Om_conformal (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ W.conformalVector x y = thetaR2 N.h (Phi Y₁ Y₂ x y) := by
  refine FusionTop.induction_weight P₁.isMod x (by apply ext2; intro n k; simp [thetaR2])
    (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hb, thetaR2_add]
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y (by apply ext2; intro n k; simp [thetaR2])
    (fun a b ha hb => ?_) ?_
  · simp only [map_add, ha, hb, thetaR2_add]
  intro α₂ y hy
  rw [Om_homog Y₁ Y₂ _ hx hy, Phi_homog Y₁ Y₂ hx hy]
  apply ext2
  intro n k
  simp only [ofZ, omZ, c2_mk2, thetaR2, phiH, tauZ, lvl, oMod_conformalVector,
    gradedTraceOp_L0_mul]
  congr 1
  push_cast
  ring

theorem Om_vacuum (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ W.vacuum x y = Phi Y₁ Y₂ x y := by
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply, ha, hb]
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, ha, hb]
  intro α₂ y hy
  rw [Om_homog Y₁ Y₂ _ hx hy, Phi_homog Y₁ Y₂ hx hy]
  apply ext2
  intro n k
  simp only [ofZ, omZ, c2_mk2, phiH, tauZ, oMod_vacuum]
  rfl

theorem Om_shiftedOmega (x : P₁.carrier) (y : P₂.carrier) :
    Om Y₁ Y₂ (shiftedOmega W) x y =
      thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y) := by
  rw [shiftedOmega, sub_eq_add_neg, ← neg_smul, Om_add, Om_smul, Om_conformal, Om_vacuum,
    neg_smul, ← sub_eq_add_neg, thetaR2_sub_const]

/-- Square modes of `ω̃` in terms of those of `ω`. -/
theorem sqMode_shiftedOmega_eq {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) (m : ℤ) (w : M) :
    GenusOne.SquareModule.sqMode A m (shiftedOmega W) w =
      sqAct A W.conformalVector 2 m w -
        (if m = -1 then W.centralCharge / 24 else 0) • w := by
  rw [shiftedOmega, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    GenusOne.SquareModule.sqMode_of_mem_grading A W.conformal_mem,
    GenusOne.SquareModule.sqMode_of_mem_grading A W.vacuum_mem_grading_zero]
  simp only [show (2 : ℤ).toNat = 2 from rfl, Int.toNat_zero,
    GenusOne.SquareModule.sqAct_vacuum]
  split_ifs <;> simp

/-- The formal mixed expression (minus-one identity for `ω̃`, as a difference). -/
def mixedLHS (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) : R2 :=
  Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y -
    (thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y) +
      ∑ m ∈ Finset.range K, eis (m + 1) *
        Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ) (shiftedOmega W) x) y +
      ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y))

theorem mixedLHS_homog {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    EvZero (mixedLHS Y₁ Y₂ x y) := by
  obtain ⟨T, hT⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule
    W.conformalVector x y
  refine ⟨T, fun K hK => ?_⟩
  have h := ward_neg_one_phi Y₁ Y₂ (kc := 2) (by norm_num) W.conformal_mem hx hy K
    (tailBound_mono hK hT)
  rw [Om_conformal] at h
  unfold mixedLHS
  simp only [sqMode_shiftedOmega_eq, if_pos rfl, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply]
  have hne : ∀ m : ℕ, ((2 * m + 1 : ℕ) : ℤ) ≠ -1 := fun m => by omega
  have hne' : ∀ m : ℕ, ((m : ℕ) : ℤ) ≠ -1 := fun m => by omega
  simp only [hne, hne', if_false, zero_smul, sub_zero, map_zero]
  rw [h, ← thetaR2_sub_const, if_pos trivial]
  abel

theorem mixedLHS_add_left (x x' : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    mixedLHS Y₁ Y₂ (x + x') y K = mixedLHS Y₁ Y₂ x y K + mixedLHS Y₁ Y₂ x' y K := by
  simp only [mixedLHS, map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib,
    thetaR2_add]
  abel

theorem mixedLHS_add_right (x : P₁.carrier) (y y' : P₂.carrier) (K : ℕ) :
    mixedLHS Y₁ Y₂ x (y + y') K = mixedLHS Y₁ Y₂ x y K + mixedLHS Y₁ Y₂ x y' K := by
  simp only [mixedLHS, map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib,
    thetaR2_add]
  abel

/-- **Minus-one identity for `ω̃`, general insertions.** -/
theorem mixedLHS_evZero (x : P₁.carrier) (y : P₂.carrier) : EvZero (mixedLHS Y₁ Y₂ x y) := by
  refine FusionTop.induction_weight P₁.isMod x
    (evZero_of_eq_zero fun K => by simp [mixedLHS, thetaR2]; apply ext2; intro n k; simp)
    (fun a a' ha ha' => ?_) ?_
  · rw [show mixedLHS Y₁ Y₂ (a + a') y = fun K => mixedLHS Y₁ Y₂ a y K + mixedLHS Y₁ Y₂ a' y K
      from funext fun K => mixedLHS_add_left Y₁ Y₂ a a' y K]
    exact ha.add ha'
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y
    (evZero_of_eq_zero fun K => by simp [mixedLHS, thetaR2]; apply ext2; intro n k; simp)
    (fun a a' ha ha' => ?_) ?_
  · rw [show mixedLHS Y₁ Y₂ x (a + a') = fun K => mixedLHS Y₁ Y₂ x a K + mixedLHS Y₁ Y₂ x a' K
      from funext fun K => mixedLHS_add_right Y₁ Y₂ x a a' K]
    exact ha.add ha'
  intro α₂ y hy
  exact mixedLHS_homog Y₁ Y₂ hx hy

/-- The zero-mode relation for `ω̃`, all insertions. -/
theorem Phi_zero_mode_shiftedOmega (x : P₁.carrier) (y : P₂.carrier) :
    Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((0 : ℕ) : ℤ) (shiftedOmega W) x) y +
      Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod ((0 : ℕ) : ℤ) (shiftedOmega W) y) = 0 := by
  refine FusionTop.induction_weight P₁.isMod x (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    linear_combination ha + hb
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y (by simp) (fun a b ha hb => ?_) ?_
  · simp only [map_add] at ha hb ⊢
    linear_combination ha + hb
  intro α₂ y hy
  obtain ⟨T, hT⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule
    W.conformalVector x y
  have h := Phi_zero_mode Y₁ Y₂ (kb := 2) W.conformal_mem hx hy T hT
  simp only [sqMode_shiftedOmega_eq]
  simp only [show ((0 : ℕ) : ℤ) ≠ -1 by omega, if_false, zero_smul, sub_zero]
  exact h

end Mixed

end VOA.Huang.GenusOneWard
