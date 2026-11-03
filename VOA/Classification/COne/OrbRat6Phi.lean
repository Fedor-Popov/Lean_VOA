import VOA.Classification.COne.OrbRat6Mult

/-! # The commuting operator `φ = P F P`

`F = lift GR` lifts `rotC`, `P = ½(1 + lift (GC (−1)))` is the projection onto the even charge
sectors (it lifts the Klein element `charU (−1)`).  Both commute with the modes of every vector
fixed by `rotC` and `charU (−1)`, hence so does `φ = P F P`.

On the quartet: `φ (b q₁ + d q₃) = (−i/2 b + 3i d) q₁ + (−i/4 b − i/2 d) q₃` (`phi_Q`);
on every spin-½ doublet top `v` in sector `0`: `φ v = i v` (`phi_doublet`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial

/-- The even-sector projection. -/
def Pk : Sp →ₗ[ℂ] Sp := (2⁻¹ : ℂ) • (LinearMap.id + CK)

/-- The commuting operator. -/
def phi : Sp →ₗ[ℂ] Sp := Pk ∘ₗ FR ∘ₗ Pk

theorem Pk_apply (x : Sp) : Pk x = (2⁻¹ : ℂ) • (x + CK x) := rfl

theorem Pk_mode {u : Sp} (hu : charU 1 le_rfl (-1) u = u) (n : ℤ) (x : Sp) :
    Pk (mode (Mo.YM u) n x) = mode (Mo.YM u) n (Pk x) := by
  rw [Pk_apply, Pk_apply, CK, lift_mode (presR_GC _) (GC_Phi _), hu, map_smul, map_add]

theorem phi_mode {u : Sp} (hu : charU 1 le_rfl (-1) u = u) (hr : rotC u = u) (n : ℤ) (x : Sp) :
    phi (mode (Mo.YM u) n x) = mode (Mo.YM u) n (phi x) := by
  change Pk (FR (Pk _)) = _
  rw [Pk_mode hu, FR_mode, hr, Pk_mode hu]
  rfl

theorem CK_Sd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) :
    CK x = (((-1 : ℂˣ) ^ n : ℂˣ) : ℂ) • x := lift_GC_Sd _ hx

theorem Pk_even {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) (hn : Even n) : Pk x = x := by
  rw [Pk_apply, CK_Sd hx, Units.val_zpow_eq_zpow_val]
  simp only [Units.val_neg, Units.val_one]
  rw [hn.neg_one_zpow, one_smul, ← two_smul ℂ x, smul_smul]
  norm_num

theorem Pk_odd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) (hn : Odd n) : Pk x = 0 := by
  rw [Pk_apply, CK_Sd hx, Units.val_zpow_eq_zpow_val]
  simp only [Units.val_neg, Units.val_one]
  rw [hn.neg_one_zpow, neg_one_smul, add_neg_cancel, smul_zero]

theorem CK_CK (x : Sp) : CK (CK x) = x := by
  have hx : x ∈ (⊤ : Submodule ℂ Sp) := trivial
  rw [← latStateGen_span (latP 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨p, n⟩, rfl⟩ := hy
    dsimp only
    rw [CK, lift_GC, map_smul, lift_GC, smul_smul]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]
    rcases Int.even_or_odd n with h | h
    · rw [h.neg_one_zpow]; simp
    · rw [h.neg_one_zpow]; simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, hy]

theorem Pk_Pk (x : Sp) : Pk (Pk x) = Pk x := by
  rw [Pk_apply, Pk_apply, map_smul, map_add, CK_CK]
  module

/-! ## The quartet -/

theorem Pk_Q (a b c d : ℂ) : Pk (Q a b c d) = Q 0 b 0 d := by
  rw [Pk_apply]
  change (2⁻¹ : ℂ) • (Q a b c d + lift (GC (-1)) (Q a b c d)) = _
  rw [lift_GC_Q]
  simp only [Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one]
  rw [Q_add, Q_smul]
  apply Q_congr <;> norm_num <;> ring

theorem unitI_val (n : ℤ) : ((unitI ^ n : ℂˣ) : ℂ) = I ^ n := by
  rw [Units.val_zpow_eq_zpow_val]; rfl

theorem unitHalf_val (n : ℤ) : ((unitHalf ^ n : ℂˣ) : ℂ) = (1 / 2 : ℂ) ^ n := by
  rw [Units.val_zpow_eq_zpow_val]; rfl

theorem FR_Q (b d : ℂ) :
    Pk (FR (Q 0 b 0 d)) = Q 0 (-I / 2 * b + 3 * I * d) 0 (-I / 4 * b - I / 2 * d) := by
  rw [FR_eq, lift_GC_Q, lift_GC_Q, lift_GE_Q, lift_GF_Q, lift_GE_Q, Pk_Q]
  simp only [unitI_val, unitHalf_val]
  have hI : I ^ (-1 : ℤ) = -I := by rw [zpow_neg_one, inv_I]
  have hI2 : I ^ (-2 : ℤ) = -1 := by
    rw [show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add₀ I_ne_zero, hI]; ring_nf; rw [I_sq]
  have h2 : (1 / 2 : ℂ) ^ (-2 : ℤ) = 4 := by norm_num
  have h1 : (1 / 2 : ℂ) ^ (-1 : ℤ) = 2 := by norm_num
  rw [hI, hI2, h2, h1]
  simp only [zpow_one, zpow_zero]
  rcases eps1_cases with h | h <;> rw [h] <;> apply Q_congr <;>
    (ring_nf; try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six]; try ring_nf)

theorem phi_Q (b d : ℂ) :
    phi (Q 0 b 0 d) = Q 0 (-I / 2 * b + 3 * I * d) 0 (-I / 4 * b - I / 2 * d) := by
  change Pk (FR (Pk (Q 0 b 0 d))) = _
  rw [Pk_Q, FR_Q]

/-! ## Doublets -/

section Doublet

variable {v : Sp} {d₁ d₂ : ℤ} (hv : v ∈ Sd 0 d₁) (hfv : Fm v ∈ Sd (-1) d₂) (hE : Ep v = 0)
  (hEF' : Ep (Fm v) = eps1 • v) (hFF : Fm (Fm v) = 0)

/-- `a v + b F v`. -/
def D2 (v : Sp) (a b : ℂ) : Sp := a • v + b • Fm v

include hE hEF' in
theorem Ep_D2 (a b : ℂ) : Ep (D2 v a b) = D2 v (eps1 * b) 0 := by
  simp only [D2, map_add, map_smul, hE, hEF', smul_zero, zero_add, smul_smul, zero_smul,
    add_zero]
  module

include hFF in
theorem Fm_D2 (a b : ℂ) : Fm (D2 v a b) = D2 v 0 a := by
  simp only [D2, map_add, map_smul, hFF, smul_zero, add_zero, zero_smul, zero_add]

include hv hfv in
theorem GC_D2 (u : ℂˣ) (a b : ℂ) :
    lift (GC u) (D2 v a b) = D2 v a (((u ^ (-1 : ℤ) : ℂˣ) : ℂ) * b) := by
  simp only [D2, map_add, map_smul]
  rw [lift_GC_Sd u hv, lift_GC_Sd u hfv]
  simp [smul_smul, mul_comm]

include hE hEF' in
theorem GE_D2 (t a b : ℂ) : lift (GE t) (D2 v a b) = D2 v (a + eps1 * t * b) b := by
  have hpow : (Ep ^ 4) (D2 v a b) = 0 := by
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Ep_D2 hE hEF']
    simp [D2, hE]
  rw [lift_GX root_pos t hpow, expSum_four]
  simp only [LinearMap.smul_apply, map_smul, Ep_D2 hE hEF']
  simp only [D2]
  module

include hFF in
theorem GF_D2 (t a b : ℂ) : lift (GF t) (D2 v a b) = D2 v a (b + t * a) := by
  have hpow : (Fm ^ 4) (D2 v a b) = 0 := by
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Fm_D2 hFF]
    simp [D2, hFF]
  rw [lift_GX root_neg t hpow, expSum_four]
  simp only [LinearMap.smul_apply, map_smul, Fm_D2 hFF]
  simp only [D2]
  module

include hv hfv hE hEF' hFF in
/-- `φ v = i v` for a doublet top in sector `0`. -/
theorem phi_doublet : phi v = I • v := by
  have hP : Pk v = v := Pk_even hv (by decide)
  have hPf : Pk (Fm v) = 0 := Pk_odd hfv (by decide)
  have hv' : v = D2 v 1 0 := by simp [D2]
  change Pk (FR (Pk v)) = _
  rw [hP, FR_eq, hv', GC_D2 hv hfv, GC_D2 hv hfv, GE_D2 hE hEF', GF_D2 hFF, GE_D2 hE hEF']
  simp only [D2, map_add, map_smul, hP, hPf, smul_zero, add_zero, one_smul, zero_smul]
  congr 1
  rcases eps1_cases with h | h <;> rw [h] <;> ring

end Doublet

end VOA.Classification.COne.OrbRat6
