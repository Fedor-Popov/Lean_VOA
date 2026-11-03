/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Series

/-!
# Pochhammer ratio identities for the D₄ kernel (layer 3)

All shifts of the kernel `M` used in the paper are ratios of finitely many factors:

* `rescale_kernelM` (`t ↦ q²t`, i.e. `s ↦ qs`):  `M(qs)·(1-t)(1-qt)D₊D₋ = M·P₀`.

Further shifts (`x ↦ qx`, the half shift, `z ↦ q^{-θ}z`, Weyl invariance) follow the same pattern.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- `∏_{v ∈ vs} 1/(c(v) z^v s; q)_∞`. -/
def prodE (vs : List V) (cf : V → Kq) : S := (vs.map fun v => EInv (cf v) v 1 one_ne_zero).prod

/-- `∏_{v ∈ vs} (1 - c(v) z^v s)`. -/
def prodLin (vs : List V) (cf : V → Kq) : S := (vs.map fun v => (1 - mon v (cf v) • X ^ 1)).prod

theorem hyperFactors_eq : hyperFactors = prodE hyperVecs fun _ => 1 := rfl

theorem prodE_cons (v : V) (vs : List V) (cf : V → Kq) :
    prodE (v :: vs) cf = EInv (cf v) v 1 one_ne_zero * prodE vs cf := by
  simp [prodE]

theorem rescale_prodE (a : Kq) (vs : List V) (cf : V → Kq) :
    rescale (algebraMap Kq R a) (prodE vs cf) = prodE vs fun v => a * cf v := by
  induction vs with
  | nil => simp [prodE]
  | cons v vs ih =>
      simp only [prodE, List.map_cons, List.prod_cons, map_mul] at ih ⊢
      rw [ih, rescale_EInv, pow_one]

theorem prodE_mul_prodLin (vs : List V) (cf : V → Kq) :
    prodE vs cf * prodLin vs cf = prodE vs fun v => qq * cf v := by
  induction vs with
  | nil => simp [prodE, prodLin]
  | cons v vs ih =>
      simp only [prodE, prodLin, List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih, ← EInv_mul_one_sub]
      ring

/-- `t = s²`. -/
def tS : S := X ^ 2

/-- `qq` as a scalar in `S`. -/
def qS : S := C (algebraMap Kq R qq)

/-- `x²`, `x⁻²`. -/
def xPow (j : ℤ) : R := mon (j • xv) 1

/-- `D₊ = (1-tx²)(1-qtx²)`, `D₋ = (1-tx⁻²)(1-qtx⁻²)`. -/
def Dp : S := (1 - mon (2 • xv) 1 • X ^ 2) * (1 - mon (2 • xv) qq • X ^ 2)
def Dm : S := (1 - mon (-2 • xv) 1 • X ^ 2) * (1 - mon (-2 • xv) qq • X ^ 2)

/-- `(1-t)(1-qt)`. -/
def Tden : S := (1 - mon 0 1 • X ^ 2) * (1 - mon 0 qq • X ^ 2)

/-- `P₀ = ∏_{ε,a}(1 - s x^ε a)`. -/
def P0S : S := prodLin hyperVecs fun _ => 1

theorem rescale_EPos_two (c : Kq) (v : V) :
    rescale (algebraMap Kq R qq) (EPos c v 2 two_ne_zero) * ((1 - mon v c • X ^ 2) *
      (1 - mon v (qq * c) • X ^ 2)) = EPos c v 2 two_ne_zero := by
  rw [rescale_EPos, EPos_eq c v, EPos_eq (qq * c) v, ← mul_assoc qq qq c, ← sq]
  ring

/-- **`s ↦ qs`** (i.e. `t ↦ q²t`): `M(qs)·(1-t)(1-qt)D₊D₋ = M·P₀`. -/
theorem rescale_kernelM :
    rescale (algebraMap Kq R qq) kernelM * (Tden * Dp * Dm) = kernelM * P0S := by
  rw [kernelM, tFactors, map_mul, map_mul, map_mul, hyperFactors_eq, rescale_prodE, P0S,
    ← prodE_mul_prodLin]
  have h1 := rescale_EPos_two 1 0
  have h2 := rescale_EPos_two 1 (2 • xv)
  have h3 := rescale_EPos_two 1 (-2 • xv)
  simp only [mul_one] at h1 h2 h3
  rw [Tden, Dp, Dm]
  conv_rhs => rw [← h1, ← h2, ← h3]
  ring

/-! ## Twisted products -/

theorem map_twist_prodE (χ : V →+ ℤ) (b : Kq) (hb : b ≠ 0) (vs : List V) (cf : V → Kq) :
    PowerSeries.map (twist χ b hb : R →+* R) (prodE vs cf) = prodE vs fun v => b ^ χ v * cf v := by
  induction vs with
  | nil => simp [prodE]
  | cons v vs ih =>
      simp only [prodE, List.map_cons, List.prod_cons, map_mul] at ih ⊢
      rw [ih, map_twist_EInv]

theorem prodE_congr (vs : List V) {cf cf' : V → Kq} (h : ∀ v ∈ vs, cf v = cf' v) :
    prodE vs cf = prodE vs cf' := by
  unfold prodE
  congr 1
  exact List.map_congr_left fun v hv => by rw [h v hv]

theorem prodLin_congr (vs : List V) {cf cf' : V → Kq} (h : ∀ v ∈ vs, cf v = cf' v) :
    prodLin vs cf = prodLin vs cf' := by
  unfold prodLin
  congr 1
  exact List.map_congr_left fun v hv => by rw [h v hv]

theorem prodE_append (vs ws : List V) (cf : V → Kq) :
    prodE (vs ++ ws) cf = prodE vs cf * prodE ws cf := by
  simp [prodE]

theorem prodLin_append (vs ws : List V) (cf : V → Kq) :
    prodLin (vs ++ ws) cf = prodLin vs cf * prodLin ws cf := by
  simp [prodLin]

/-- One half of the hypermultiplet weights, `x^ε z_i^σ` for fixed `ε`. -/
def hyperHalf (ε : ℤ) : List V :=
  (List.finRange 4).flatMap fun i => [1, -1].map fun σ : ℤ => ε • xv + σ • zv i

theorem hyperVecs_eq : hyperVecs = hyperHalf 1 ++ hyperHalf (-1) := by
  simp [hyperVecs, hyperHalf]

/-- The `x`-exponent. -/
def chiX : V →+ ℤ := Pi.evalAddMonoidHom (fun _ => ℤ) 0

theorem chiX_hyperHalf (ε : ℤ) : ∀ v ∈ hyperHalf ε, chiX v = ε := by
  intro v hv
  simp only [hyperHalf, List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false, true_and] at hv
  obtain ⟨i, σ, -, rfl⟩ := hv
  simp [chiX, xv, zv, Fin.succ_ne_zero]

/-- `P(x) = ∏_a (1 - s x a)` and `P(x⁻¹)`. -/
def PplusS : S := prodLin (hyperHalf 1) fun _ => 1
def PminusS : S := prodLin (hyperHalf (-1)) fun _ => 1

theorem P0S_eq : P0S = PplusS * PminusS := by
  rw [P0S, hyperVecs_eq, prodLin_append, PplusS, PminusS]

/-- **Half shift** `(s, x) ↦ (√q s, √q x)`: `H(M)·(1-t)·D₊ = M·P(x)`. -/
theorem halfShift_kernelM :
    rescale (algebraMap Kq R rr) (PowerSeries.map (twist chiX rr rr_ne_zero : R →+* R) kernelM) *
      ((1 - mon 0 1 • X ^ 2) * Dp) = kernelM * PplusS := by
  have hx0 : chiX 0 = 0 := map_zero _
  have hx1 : chiX xv = 1 := by simp [chiX, xv]
  have hx2 : chiX (2 • xv) = 2 := by rw [map_nsmul, hx1]; rfl
  have hx3 : chiX (-2 • xv) = -2 := by rw [map_zsmul, hx1]; rfl
  have hr2 : rr ^ 2 = qq := qq_eq_rr_sq.symm
  have hrr : rr ≠ 0 := rr_ne_zero
  rw [kernelM, tFactors, hyperFactors_eq, hyperVecs_eq, prodE_append]
  simp only [map_mul, map_twist_EPos, map_twist_prodE, rescale_EPos, rescale_prodE, hx0, hx2, hx3]
  have e1 : rr ^ 2 * (rr ^ (0 : ℤ) * 1) = qq * 1 := by rw [zpow_zero, hr2]; ring
  have e2 : rr ^ 2 * (rr ^ (2 : ℤ) * 1) = qq * (qq * 1) := by
    rw [zpow_ofNat, hr2, mul_one]
  have e3 : rr ^ 2 * (rr ^ (-2 : ℤ) * 1) = 1 := by
    rw [zpow_neg, zpow_ofNat, mul_one, mul_inv_cancel₀ (pow_ne_zero 2 hrr)]
  rw [e1, e2, e3]
  have hp : (prodE (hyperHalf 1) fun v => rr * (rr ^ chiX v * 1)) =
      prodE (hyperHalf 1) fun v => qq * 1 :=
    prodE_congr _ fun v hv => by rw [chiX_hyperHalf 1 v hv, zpow_one, ← hr2]; ring
  have hm : (prodE (hyperHalf (-1)) fun v => rr * (rr ^ chiX v * 1)) =
      prodE (hyperHalf (-1)) fun v => 1 :=
    prodE_congr _ fun v hv => by
      rw [chiX_hyperHalf (-1) v hv, zpow_neg, zpow_one, mul_one, mul_inv_cancel₀ hrr]
  rw [hp, hm, ← prodE_mul_prodLin, EPos_eq 1 0, EPos_eq 1 (2 • xv), EPos_eq (qq * 1) (2 • xv),
    Dp, PplusS]
  simp only [mul_one]
  ring

/-- Factorwise comparison of two `prodE`s. -/
theorem prodE_eq_mul (vs : List V) (cf cf' : V → Kq) (g : V → S)
    (h : ∀ v ∈ vs, EInv (cf' v) v 1 one_ne_zero = EInv (cf v) v 1 one_ne_zero * g v) :
    prodE vs cf' = prodE vs cf * (vs.map g).prod := by
  induction vs with
  | nil => simp [prodE]
  | cons v vs ih =>
      simp only [prodE, List.map_cons, List.prod_cons] at ih ⊢
      rw [h v (List.mem_cons_self), ih fun w hw => h w (List.mem_cons_of_mem _ hw)]
      ring

theorem EInv_qq (v : V) : EInv qq v 1 one_ne_zero =
    EInv 1 v 1 one_ne_zero * (1 - mon v 1 • X ^ 1) := by
  rw [EInv_mul_one_sub, mul_one]

theorem EInv_qq_sq (v : V) : EInv (qq * qq) v 1 one_ne_zero =
    EInv 1 v 1 one_ne_zero * ((1 - mon v 1 • X ^ 1) * (1 - mon v qq • X ^ 1)) := by
  rw [← mul_assoc, EInv_mul_one_sub, mul_one, EInv_mul_one_sub]

theorem EInv_qq_inv (v : V) : EInv qq⁻¹ v 1 one_ne_zero * (1 - mon v qq⁻¹ • X ^ 1) =
    EInv 1 v 1 one_ne_zero := by
  rw [EInv_mul_one_sub, mul_inv_cancel₀ qq_ne_zero]

/-- The `z₁z₂` exponent `(μ, θ)` for `θ = e₁ + e₂`. -/
def chiTheta : V →+ ℤ :=
  Pi.evalAddMonoidHom (fun _ => ℤ) 1 + Pi.evalAddMonoidHom (fun _ => ℤ) 2

/-- The factor of `P_θ` attached to the hypermultiplet weight `v`. -/
def pThetaFactor (v : V) : S :=
  if chiTheta v = -1 then (1 - mon v 1 • X ^ 1) * (1 - mon v qq • X ^ 1)
  else if chiTheta v = 1 then 1 else 1 - mon v 1 • X ^ 1

/-- `P_θ = ∏_v pThetaFactor v`. -/
def PthetaS : S := (hyperVecs.map pThetaFactor).prod

theorem chiTheta_hyperVecs :
    ∀ v ∈ hyperVecs, chiTheta v = -1 ∨ chiTheta v = 0 ∨ chiTheta v = 1 := by
  decide

/-- **`z ↦ q^{-θ}z` on `M(qs)`**: `M(qs)(q^{-θ}z)·(1-t)(1-qt)D₊D₋ = M·P_θ`. -/
theorem thetaShift_kernelM :
    PowerSeries.map (twist chiTheta qq⁻¹ (inv_ne_zero qq_ne_zero) : R →+* R)
        (rescale (algebraMap Kq R qq) kernelM) * (Tden * Dp * Dm) = kernelM * PthetaS := by
  have h0 : chiTheta 0 = 0 := map_zero _
  have h2 : chiTheta (2 • xv) = 0 := by decide
  have h3 : chiTheta (-2 • xv) = 0 := by decide
  rw [kernelM, tFactors, hyperFactors_eq]
  simp only [map_mul, rescale_EPos, rescale_prodE, map_twist_EPos, map_twist_prodE, h0, h2, h3,
    zpow_zero, one_mul, mul_one]
  rw [prodE_eq_mul hyperVecs (fun _ => 1) _ pThetaFactor]
  · have h1 := rescale_EPos_two 1 0
    have h2' := rescale_EPos_two 1 (2 • xv)
    have h3' := rescale_EPos_two 1 (-2 • xv)
    simp only [rescale_EPos, mul_one] at h1 h2' h3'
    rw [Tden, Dp, Dm, PthetaS]
    conv_rhs => rw [← h1, ← h2', ← h3']
    ring
  · intro v hv
    rcases chiTheta_hyperVecs v hv with h | h | h
    · rw [h, pThetaFactor, if_pos h, zpow_neg, zpow_one, inv_inv, ← EInv_qq_sq]
    · rw [h, pThetaFactor, if_neg (by omega), if_neg (by omega), zpow_zero, one_mul, EInv_qq]
    · rw [h, pThetaFactor, if_neg (by omega), if_pos h, zpow_one, mul_one,
        inv_mul_cancel₀ qq_ne_zero]

/-- The factor attached to `v` under `x ↦ qx`: `1 - s x a` for `ε = 1`, `1/(1 - q⁻¹ s x⁻¹ a)` for
`ε = -1` (recorded on the other side). -/
def xShiftNum (v : V) : S :=
  if chiX v = 1 then 1 - mon v 1 • X ^ 1 else 1
def xShiftDen (v : V) : S := if chiX v = -1 then 1 - mon v qq⁻¹ • X ^ 1 else 1

theorem chiX_hyperVecs : ∀ v ∈ hyperVecs, chiX v = 1 ∨ chiX v = -1 := by
  decide

/-- **`x ↦ qx`**: `M(qx)·D₊·∏_{ε=-1}(1 - q⁻¹ s x⁻¹ a) = M·(1 - q⁻²tx⁻²)(1 - q⁻¹tx⁻²)·P(x)`. -/
theorem xShift_kernelM :
    PowerSeries.map (twist chiX qq qq_ne_zero : R →+* R) kernelM * Dp *
        (hyperVecs.map xShiftDen).prod =
      kernelM * ((1 - mon (-2 • xv) (qq ^ (-2 : ℤ)) • X ^ 2) *
        (1 - mon (-2 • xv) (qq ^ (-1 : ℤ)) • X ^ 2)) * (hyperVecs.map xShiftNum).prod := by
  have hx0 : chiX 0 = 0 := map_zero _
  have hx2 : chiX (2 • xv) = 2 := by decide
  have hx3 : chiX (-2 • xv) = -2 := by decide
  have hq : qq ≠ 0 := qq_ne_zero
  rw [kernelM, tFactors, hyperFactors_eq]
  simp only [map_mul, map_twist_EPos, map_twist_prodE, hx0, hx2, hx3, zpow_zero, mul_one]
  -- hyper factors: `EInv(q^{χ v}) · den = EInv(1) · num`
  have hh : ∀ vs : List V, (∀ v ∈ vs, chiX v = 1 ∨ chiX v = -1) →
      prodE vs (fun v => qq ^ chiX v) * (vs.map xShiftDen).prod =
        prodE vs (fun _ => 1) * (vs.map xShiftNum).prod := by
    intro vs hvs
    induction vs with
    | nil => simp [prodE]
    | cons v vs ih =>
        have ih' := ih fun w hw => hvs w (List.mem_cons_of_mem _ hw)
        rw [prodE_cons, prodE_cons, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
        rcases hvs v List.mem_cons_self with h | h
        · rw [xShiftDen, xShiftNum, if_neg (by omega), if_pos h, h, zpow_one, EInv_qq]
          calc _ = (EInv 1 v 1 one_ne_zero * (1 - mon v 1 • X ^ 1)) *
                (prodE vs (fun v => qq ^ chiX v) * (vs.map xShiftDen).prod) := by ring
            _ = _ := by rw [ih']; ring
        · rw [xShiftDen, xShiftNum, if_pos h, if_neg (by omega), h, zpow_neg, zpow_one]
          calc _ = (EInv qq⁻¹ v 1 one_ne_zero * (1 - mon v qq⁻¹ • X ^ 1)) *
                (prodE vs (fun v => qq ^ chiX v) * (vs.map xShiftDen).prod) := by ring
            _ = _ := by rw [EInv_qq_inv, ih']; ring
  have e2 : EPos 1 (2 • xv) 2 two_ne_zero = Dp * EPos (qq ^ (2 : ℤ)) (2 • xv) 2 two_ne_zero := by
    rw [EPos_eq 1, EPos_eq (qq * 1), Dp, zpow_ofNat, sq]; simp only [mul_one]; ring_nf
  have e3 : EPos (qq ^ (-2 : ℤ)) (-2 • xv) 2 two_ne_zero =
      (1 - mon (-2 • xv) (qq ^ (-2 : ℤ)) • X ^ 2) * ((1 - mon (-2 • xv) (qq ^ (-1 : ℤ)) • X ^ 2) *
        EPos 1 (-2 • xv) 2 two_ne_zero) := by
    rw [EPos_eq, EPos_eq (qq * qq ^ (-2 : ℤ))]
    have a1 : qq * qq ^ (-2 : ℤ) = qq ^ (-1 : ℤ) := by
      rw [← zpow_one_add₀ hq]; norm_num
    have a2 : qq * (qq * qq ^ (-2 : ℤ)) = 1 := by
      rw [a1, ← zpow_one_add₀ hq]; norm_num
    rw [a2, a1]
  rw [e3]
  conv_rhs => rw [e2]
  have := hh hyperVecs chiX_hyperVecs
  calc _ = EPos 1 0 2 two_ne_zero * EPos (qq ^ (2 : ℤ)) (2 • xv) 2 two_ne_zero *
        ((1 - mon (-2 • xv) (qq ^ (-2 : ℤ)) • X ^ 2) * ((1 - mon (-2 • xv) (qq ^ (-1 : ℤ)) • X ^ 2) *
          EPos 1 (-2 • xv) 2 two_ne_zero)) * Dp *
        (prodE hyperVecs (fun v => qq ^ chiX v) * (hyperVecs.map xShiftDen).prod) := by ring
    _ = _ := by rw [this]; ring

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.rescale_kernelM
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.halfShift_kernelM
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.thetaShift_kernelM
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.xShift_kernelM
end AxiomAudit
