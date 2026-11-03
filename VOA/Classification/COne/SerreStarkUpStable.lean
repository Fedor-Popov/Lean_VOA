/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelFricke

/-!
# Serre–Stark S5-1: the operator `U(p²)` at a prime `p ∣ N`

For a prime `p` dividing the level `N` (`24 ∣ N`) the operator

`U(p²) f (τ) = p⁻² Σ_{b mod p²} f((τ + b)/p²) = Σ_n a(p² n) qⁿ`

preserves θ-type forms of level `N` and `M_{1/2}(N, χ)` (Shimura 1973, `T(p²)` at `p ∣ N`;
Achimescu–Saha arXiv:0803.3788 Lemma 4.4 for `U(p)`). The proof needs no Gauss sums:

* `thetaSq_law`: `θ(p²τ)` satisfies the θ-multiplier law on all of `Γ₀(N p²)`
  (from the proved Weil Galois law `thetaLaw_G` at the coset `∞` and `T`-invariance);
* `upFact`: for `γ = (a b; c d) ∈ Γ₀(N)` and `A_b = (1 b; 0 p²)`, `A_b γ = δ_b A_{σ b}` with
  `δ_b = (a + bc, *; p²c, d − c σb) ∈ Γ₀(N p²)`; since `p²(δ_b w) = γτ + b` for `w = A_{σ b} τ`,
  the law of `θ(p²·)` at `δ_b` is exactly the transport law `θ(A_b γ τ) θ(τ) = θ(γτ) θ(A_{σb} τ)`.

Main results: `isThetaTypeForm_upOp`, `upOp_chiLaw`, `coeff_upOp` (`b(n) = a(p² n)`),
`isClassForm_upOp` (class forms are stable), and the finite-dimensionality consequence
`exists_upRecurrence` (along `p`-powers the coefficients of a class form satisfy one fixed
linear recurrence).
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

variable {p : ℕ}

/-! ## `θ(p² τ)` on `Γ₀(N p²)` -/

/-- The law of `θ(p²·)` for `γ ≡ diag(ℓ, ℓ') (mod N p²)` (the Weil Galois law at the coset `∞`). -/
theorem thetaSq_law_diag [hpf : Fact p.Prime] {N : ℕ} (h24 : 24 ∣ N) (ℓ : ℕ)
    (hℓ : ℓ.Coprime (N * p ^ 2)) (ℓ' : ℤ) (hℓℓ : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD (N * p ^ 2 : ℕ)])
    (γ : SL(2, ℤ)) (h00 : γ 0 0 ≡ ℓ [ZMOD (N * p ^ 2 : ℕ)])
    (h11 : γ 1 1 ≡ ℓ' [ZMOD (N * p ^ 2 : ℕ)]) (h01 : γ 0 1 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)])
    (h10 : γ 1 0 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)]) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef ((p : ℂ) ^ 2 * mobius γ τ) * thetaRef τ =
      thetaRef (mobius γ τ) * thetaRef ((p : ℂ) ^ 2 * τ) := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have h := thetaLaw_G hpf.out h4 h24 ℓ hℓ ℓ' hℓℓ γ h00 h11 h01 h10 (.inr (.inr ())) τ hτ
  simp only [sigmaG, mobZ_cosetMat_inr_inr, hw] at h
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpf.out.pos.ne'
  have hc : (1 / (p : ℂ)) ≠ 0 := by simp [hp0]
  apply mul_left_cancel₀ hc
  linear_combination h

/-- **`θ(p²τ)` satisfies the θ-multiplier law on `Γ₀(N p²)`** (`24 ∣ N`). -/
theorem thetaSq_law [hpf : Fact p.Prime] {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) (g : SL(2, ℤ))
    (hg : ((N * p ^ 2 : ℕ) : ℤ) ∣ g 1 0) {u : ℂ} (hu : 0 < u.im) :
    thetaRef ((p : ℂ) ^ 2 * mobius g u) * thetaRef u =
      thetaRef (mobius g u) * thetaRef ((p : ℂ) ^ 2 * u) := by
  set M : ℕ := N * p ^ 2 with hM
  have hM0 : 0 < M := Nat.mul_pos hN (pow_pos hpf.out.pos 2)
  set k : ℤ := g 0 1 * g 1 1 with hk
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := det_SL' g
  let g₂ : SL(2, ℤ) := ⟨!![g 0 0, g 0 1 - k * g 0 0; g 1 0, g 1 1 - k * g 1 0], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet⟩
  have e00 : g₂ 0 0 = g 0 0 := rfl
  have e01 : g₂ 0 1 = g 0 1 - k * g 0 0 := rfl
  have e10 : g₂ 1 0 = g 1 0 := rfl
  have e11 : g₂ 1 1 = g 1 1 - k * g 1 0 := rfl
  obtain ⟨m, hm⟩ := hg
  -- the residue `ℓ`
  set ℓ : ℕ := (g 0 0 % (M : ℤ)).toNat with hℓ
  have hℓeq : (ℓ : ℤ) = g 0 0 % (M : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM0.ne'))
  have hℓmod : g 0 0 ≡ ℓ [ZMOD M] := by rw [hℓeq]; exact (Int.mod_modEq _ _).symm
  have had : g 0 0 * g 1 1 ≡ 1 [ZMOD M] :=
    Int.modEq_iff_dvd.2 ⟨-(g 0 1 * m), by rw [hm] at hdet; linear_combination (-1 : ℤ) * hdet⟩
  have hℓℓ : (ℓ : ℤ) * g 1 1 ≡ 1 [ZMOD M] := (hℓmod.symm.mul_right _).trans had
  have hℓcop : ℓ.Coprime M := by
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 hℓℓ.symm
    exact Nat.isCoprime_iff_coprime.1 ⟨g 1 1, -t, by linear_combination ht⟩
  have h00 : g₂ 0 0 ≡ ℓ [ZMOD M] := by rw [e00]; exact hℓmod
  have h10 : g₂ 1 0 ≡ 0 [ZMOD M] := by rw [e10, hm]; exact Int.modEq_zero_iff_dvd.2 ⟨m, rfl⟩
  have h11 : g₂ 1 1 ≡ g 1 1 [ZMOD M] := by
    rw [e11, hm]; exact Int.modEq_iff_dvd.2 ⟨k * m, by ring⟩
  have h01 : g₂ 0 1 ≡ 0 [ZMOD M] := by
    rw [e01, hk]
    refine Int.modEq_iff_dvd.2 ⟨g 0 1 * g 0 1 * m, ?_⟩
    rw [hm] at hdet
    linear_combination (g 0 1) * hdet
  have hu' : 0 < (u + k).im := by simpa using hu
  have hlaw := thetaSq_law_diag h24 ℓ hℓcop (g 1 1) hℓℓ g₂ h00 h11 h01 h10 hu'
  have hmob : mobius g₂ (u + k) = mobius g u := by
    simp only [mobius, e00, e01, e10, e11]
    congr 1 <;> push_cast <;> ring
  rw [hmob, thetaRef_add_int] at hlaw
  rw [show (p : ℂ) ^ 2 * (u + (k : ℂ)) = (p : ℂ) ^ 2 * u + ((p ^ 2 * k : ℤ) : ℂ) by
    push_cast; ring, thetaRef_add_int] at hlaw
  exact hlaw


/-! ## The factorisation `A_b γ = δ_b A_{σ b}` for `p ∣ N` -/

section Fact

variable (hp : p.Prime) {N : ℕ}

include hp in
theorem upCoprime (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (b : ℤ) : IsCoprime (γ 0 0 + b * γ 1 0) (((p ^ 2 : ℕ)) : ℤ) := by
  apply isCoprime_sq_of_not_dvd hp
  intro h
  have hc : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  have hpc : (p : ℤ) ∣ γ 1 0 := hpN.trans hc
  have hpa : (p : ℤ) ∣ γ 0 0 := by
    have := dvd_sub h (dvd_mul_of_dvd_right hpc b)
    simpa using this
  have h1 : (p : ℤ) ∣ γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 :=
    dvd_sub (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_right hpc _)
  rw [det_SL' γ] at h1
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

/-- The induced permutation `σ_γ(b) ≡ (β + b d)(a + b c)⁻¹ (mod p²)`. -/
def upSigma (γ : SL(2, ℤ)) (b : Fin (p ^ 2)) : Fin (p ^ 2) :=
  rep (p ^ 2) (pow_pos hp.pos 2)
    ((γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1) * binv (p ^ 2) (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0))

/-- The factor `δ_b`. -/
def upDelta (γ : SL(2, ℤ)) (b : Fin (p ^ 2)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0,
    (γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1 -
      ((upSigma hp γ b : ℕ) : ℤ) * (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0)) / (p : ℤ) ^ 2;
    (p : ℤ) ^ 2 * γ 1 0, γ 1 1 - ((upSigma hp γ b : ℕ) : ℤ) * γ 1 0]

theorem upDelta_dvd (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (b : Fin (p ^ 2)) :
    (p : ℤ) ^ 2 ∣ γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1 -
      ((upSigma hp γ b : ℕ) : ℤ) * (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0) := by
  have hb := binv_spec (upCoprime hp hpN hγ ((b : ℕ) : ℤ))
  have hr := rep_modEq (pow_pos hp.pos 2)
    ((γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1) * binv (p ^ 2) (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0))
  have h1 := (hr.mul_right (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0))
  have h2 : (γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1) * binv (p ^ 2) (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0) *
      (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0) ≡ (γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1) * 1
      [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by
    have hb' : binv (p ^ 2) (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0) * (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0)
        ≡ 1 [ZMOD ((p ^ 2 : ℕ) : ℤ)] := by rw [mul_comm]; exact hb
    rw [mul_assoc]
    exact Int.ModEq.mul_left _ hb'
  have h3 := (h1.trans h2)
  rw [mul_one] at h3
  have := Int.ModEq.dvd h3.symm
  push_cast at this
  unfold upSigma
  rw [← neg_sub]
  exact (dvd_neg).2 this

/-- **Factorisation**: `A_b γ = δ_b A_{σ b}`. -/
theorem upFact (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (b : Fin (p ^ 2)) :
    cosetMat p (.inl b) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      upDelta hp γ b * cosetMat p (.inl (upSigma hp γ b)) := by
  obtain ⟨q, hq⟩ := upDelta_dvd hp hpN hγ b
  have hp2 : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.pos.ne')
  have hdiv : (γ 0 1 + ((b : ℕ) : ℤ) * γ 1 1 -
      ((upSigma hp γ b : ℕ) : ℤ) * (γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0)) / (p : ℤ) ^ 2 = q := by
    rw [hq]; exact Int.mul_ediv_cancel_left _ hp2
  simp only [upDelta, hdiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cosetMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hq | linear_combination (-1 : ℤ) * hq

end Fact


/-! ## The transport law for the `U`-cosets -/

section Law

variable (hp : p.Prime) {N : ℕ}

/-- `δ_b` as an element of `SL₂(ℤ)`. -/
def upDeltaSL (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (b : Fin (p ^ 2)) : SL(2, ℤ) :=
  factSL hp.pos γ (upDelta hp γ b) (upFact hp hpN hγ b)

variable (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
  (b : Fin (p ^ 2))

theorem upDeltaSL_coe :
    ((upDeltaSL hp hpN hγ b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = upDelta hp γ b := rfl

theorem upDeltaSL_00 : upDeltaSL hp hpN hγ b 0 0 = γ 0 0 + ((b : ℕ) : ℤ) * γ 1 0 := by
  rw [upDeltaSL_coe]; simp [upDelta]

theorem upDeltaSL_10 : upDeltaSL hp hpN hγ b 1 0 = (p : ℤ) ^ 2 * γ 1 0 := by
  rw [upDeltaSL_coe]; simp [upDelta]

theorem upDeltaSL_11 :
    upDeltaSL hp hpN hγ b 1 1 = γ 1 1 - ((upSigma hp γ b : ℕ) : ℤ) * γ 1 0 := by
  rw [upDeltaSL_coe]; simp [upDelta]

theorem mobius_upDeltaSL {τ : ℂ} (hτ : 0 < τ.im) :
    mobius (upDeltaSL hp hpN hγ b) (mobZ (cosetMat p (.inl (upSigma hp γ b))) τ) =
      mobZ (cosetMat p (.inl b)) (mobius γ τ) := by
  rw [← mobZ_cosetMat_mul_SL (.inl b) γ hτ, upFact hp hpN hγ b, ← upDeltaSL_coe hp hpN hγ b,
    mobZ_SL_mul_cosetMat hp.pos]

theorem sq_mul_mobius_upDeltaSL {τ : ℂ} (hτ : 0 < τ.im) :
    (p : ℂ) ^ 2 * mobius (upDeltaSL hp hpN hγ b) (mobZ (cosetMat p (.inl (upSigma hp γ b))) τ) =
      mobius γ τ + ((b : ℕ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  rw [mobius_upDeltaSL hp hpN hγ b hτ, mobZ_cosetMat_inl]
  field_simp

theorem upDeltaSL_mem : upDeltaSL hp hpN hγ b ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, upDeltaSL_10]
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ
  push_cast; rw [hc, mul_zero]

theorem upDeltaSL_00_mod :
    ((upDeltaSL hp hpN hγ b 0 0 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ
  rw [upDeltaSL_00]; push_cast; rw [hc, mul_zero, add_zero]

theorem upDeltaSL_11_mod :
    ((upDeltaSL hp hpN hγ b 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ
  rw [upDeltaSL_11]; push_cast; rw [hc, mul_zero, sub_zero]

include hpN hγ in
/-- **The theta transport law for the `U`-cosets** (`p ∣ N`, `24 ∣ N`):
`θ(A_b γ τ) θ(τ) = θ(γτ) θ(A_{σ b} τ)` for every `γ ∈ Γ₀(N)`. -/
theorem upTheta_law [Fact p.Prime] (hN : 0 < N) (h24 : 24 ∣ N) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (mobZ (cosetMat p (.inl b)) (mobius γ τ)) * thetaRef τ =
      thetaRef (mobius γ τ) * thetaRef (mobZ (cosetMat p (.inl (upSigma hp γ b))) τ) := by
  set δ := upDeltaSL hp hpN hγ b
  set w := mobZ (cosetMat p (.inl (upSigma hp γ b))) τ with hw
  have hw0 : 0 < w.im := im_mobZ_cosetMat hp.pos _ hτ
  have hδ : ((N * p ^ 2 : ℕ) : ℤ) ∣ δ 1 0 := by
    rw [upDeltaSL_10]
    have hc : (N : ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
    obtain ⟨m, hm⟩ := hc
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  have hlaw := thetaSq_law hN h24 δ hδ hw0
  rw [sq_mul_mobius_upDeltaSL hp hpN hγ b hτ,
    show mobius γ τ + ((b : ℕ) : ℂ) = mobius γ τ + (((b : ℕ) : ℤ) : ℂ) by push_cast; rfl,
    thetaRef_add_int, mobius_upDeltaSL hp hpN hγ b hτ] at hlaw
  have hpw : (p : ℂ) ^ 2 * w = τ + (((upSigma hp γ b : ℕ) : ℤ) : ℂ) := by
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
    rw [hw, mobZ_cosetMat_inl]; push_cast; field_simp
  rw [hpw, thetaRef_add_int] at hlaw
  linear_combination -hlaw

end Law

/-! ## Injectivity of `σ` -/

theorem upSigma_injective {N : ℕ} (hp : p.Prime) (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : Function.Injective (upSigma hp γ) := by
  intro b b' hbb
  have hp2 : 2 ≤ p := hp.two_le
  set g := upDeltaSL hp hpN hγ b
  set g' := upDeltaSL hp hpN hγ b'
  have h1 : cosetMat p (.inl b) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p (.inl (upSigma hp γ b)) := upFact hp hpN hγ b
  have h2 : cosetMat p (.inl b') * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (g' : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p (.inl (upSigma hp γ b)) := by
    rw [hbb]; exact upFact hp hpN hγ b'
  have hγi : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hg'i : ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g' : Matrix (Fin 2) (Fin 2) ℤ)
      = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : cosetMat p (.inl b) =
      ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p (.inl b') := by
    calc cosetMat p (.inl b) = cosetMat p (.inl b) * (γ : Matrix (Fin 2) (Fin 2) ℤ) *
          ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
            rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * (((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (g' : Matrix (Fin 2) (Fin 2) ℤ)) * cosetMat p (.inl (upSigma hp γ b)) *
          ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
            rw [h1, hg'i, Matrix.mul_one]
      _ = ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (cosetMat p (.inl b') *
          (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
            rw [h2, Matrix.SpecialLinearGroup.coe_mul]
            simp only [Matrix.mul_assoc]
      _ = ((g * g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * cosetMat p (.inl b') := by
            rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
  have := cosetMat_unique hp2 (g * g'⁻¹).det_coe key
  exact Sum.inl_injective this

/-! ## The operator `U(p²)` -/

/-- **`U(p²)`**: `U(p²) f (τ) = p⁻² Σ_{b mod p²} f((τ + b)/p²)`. -/
def upOp (p : ℕ) (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  1 / (p : ℂ) ^ 2 * ∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ)

/-- The abstract law: if `F` transforms with factor `κ` under every `δ ∈ Γ₀(N)` congruent to `γ`
on the diagonal, then so does `U(p²) F` under `γ`. -/
theorem upOp_law [Fact p.Prime] {N : ℕ} (hp : p.Prime) (hN : 0 < N) (h24 : 24 ∣ N)
    (hpN : (p : ℤ) ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (F : ℂ → ℂ)
    (κ : ℂ)
    (hF : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N →
      ((δ 0 0 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) →
      ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) →
      ∀ w : ℂ, 0 < w.im → F (mobius δ w) * thetaRef w = κ * thetaRef (mobius δ w) * F w)
    {τ : ℂ} (hτ : 0 < τ.im) :
    upOp p F (mobius γ τ) * thetaRef τ = κ * thetaRef (mobius γ τ) * upOp p F τ := by
  have hγτ := im_mobius_pos γ hτ
  have hθ := thetaRef_ne_zero_of_im_pos hτ
  -- each coset term
  have hb : ∀ b : Fin (p ^ 2), F (mobZ (cosetMat p (.inl b)) (mobius γ τ)) * thetaRef τ =
      κ * thetaRef (mobius γ τ) * F (mobZ (cosetMat p (.inl (upSigma hp γ b))) τ) := by
    intro b
    set w := mobZ (cosetMat p (.inl (upSigma hp γ b))) τ
    have hw0 : 0 < w.im := im_mobZ_cosetMat hp.pos _ hτ
    have hθw := thetaRef_ne_zero_of_im_pos hw0
    have h1 := hF _ (upDeltaSL_mem hp hpN hγ b) (upDeltaSL_00_mod hp hpN hγ b)
      (upDeltaSL_11_mod hp hpN hγ b) w hw0
    rw [mobius_upDeltaSL hp hpN hγ b hτ] at h1
    have h2 := upTheta_law hp hpN hγ b hN h24 hτ
    apply mul_right_cancel₀ hθw
    linear_combination thetaRef τ * h1 + κ * F w * h2
  have hsum : ∑ b : Fin (p ^ 2), F (mobZ (cosetMat p (.inl (upSigma hp γ b))) τ) =
      ∑ b : Fin (p ^ 2), F (mobZ (cosetMat p (.inl b)) τ) :=
    Fintype.sum_bijective _ (upSigma_injective hp hpN hγ).bijective_of_finite _ _
      (fun _ => rfl)
  unfold upOp
  rw [mul_assoc, Finset.sum_mul, Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum,
    hsum]
  ring


/-! ## `U(p²)` preserves θ-type forms and `M_{1/2}(N, χ)` -/

section Stable

variable {N : ℕ} [hpf : Fact p.Prime]

theorem upOp_holo {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperSet) :
    DifferentiableOn ℂ (upOp p f) upperSet := by
  have hp0 := hpf.out.pos
  have : upOp p f = fun τ =>
      1 / (p : ℂ) ^ 2 * ∑ b : Fin (p ^ 2), f (mobZ (cosetMat p (.inl b)) τ) := rfl
  rw [this]
  refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun b _ => ?_) _
  exact hf.comp (differentiable_mobZ_cosetMat _).differentiableOn
    (fun τ hτ => im_mobZ_cosetMat hp0 _ hτ)

theorem upOp_cusps (h4 : 4 ∣ N) (hN : 0 < N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f)
    (γ : SL(2, ℤ)) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖upOp p f (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  have hp : p.Prime := hpf.out
  choose C hC0 hC using fun b : Fin (p ^ 2) => coset_cusp_bound hp h4 hN hf (.inl b) γ
  refine ⟨‖1 / (p : ℂ) ^ 2‖ * ∑ b : Fin (p ^ 2), C b, fun τ hτ => ?_⟩
  unfold upOp
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b _ => hC b τ hτ

/-- **`U(p²)` preserves θ-type forms of level `N`** (`p ∣ N`, `24 ∣ N`). -/
theorem isThetaTypeForm_upOp (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) : IsThetaTypeForm N (upOp p f) := by
  have hp : p.Prime := hpf.out
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have hpNZ : (p : ℤ) ∣ N := by exact_mod_cast hpN
  refine ⟨upOp_holo hf.holo, fun γ hγ τ hτ => ?_, upOp_cusps h4 hN hf⟩
  have hγ0 := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  obtain ⟨h00, h11, _⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have := upOp_law hp hN h24 hpNZ hγ0 f 1 (fun δ hδ hd0 hd1 w hw => by
    have hδ1 : δ ∈ CongruenceSubgroup.Gamma1 N := by
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hd0.trans h00, hd1.trans h11, CongruenceSubgroup.Gamma0_mem.1 hδ⟩
    rw [one_mul]; exact hf.multiplier δ hδ1 w hw) hτ
  rw [one_mul] at this
  exact this

/-- **`U(p²)` preserves the `χ`-twisted law on `Γ₀(N)`** (`p ∣ N`, `24 ∣ N`). -/
theorem upOp_chiLaw (χ : DirichletCharacter ℂ N) (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N)
    {f : ℂ → ℂ} (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ChiLaw χ f γ) :
    ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ChiLaw χ (upOp p f) γ := by
  have hp : p.Prime := hpf.out
  have hpNZ : (p : ℤ) ∣ N := by exact_mod_cast hpN
  intro γ hγ τ hτ
  exact upOp_law hp hN h24 hpNZ hγ f (χ ((γ 1 1 : ℤ) : ZMod N))
    (fun δ hδ _ hd1 w hw => by rw [← hd1]; exact hf δ hδ w hw) hτ

/-- **`U(p²)` maps `M_{1/2}(N, χ)` to itself** (`p ∣ N`, `24 ∣ N`). -/
theorem isThetaTypeFormChar_upOp (χ : DirichletCharacter ℂ N) (hN : 0 < N) (h24 : 24 ∣ N)
    (hpN : p ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeFormChar N χ f) :
    IsThetaTypeFormChar N χ (upOp p f) :=
  ⟨isThetaTypeForm_upOp hN h24 hpN hf.thetaType,
    upOp_chiLaw χ hN h24 hpN (fun γ hγ τ hτ => hf.character γ hγ τ hτ)⟩

/-- **The coefficients of `U(p²) f`**: `b(n) = a(p² n)`. -/
theorem coeff_upOp (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) (n : ℕ) :
    thetaTypeCoeff (upOp p f) n = thetaTypeCoeff f (p ^ 2 * n) := by
  have hp0 := hpf.out.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  refine (isThetaTypeForm_upOp hN h24 hpN hf).coeff_eq_of_hasSum
    (c := fun m => thetaTypeCoeff f (p ^ 2 * m)) (fun τ hτ => ?_) n
  have H := (hasSum_piece_b (p := p) hf hτ).mul_left (1 / (p : ℂ) ^ 2)
  refine H.congr_fun fun m => ?_
  field_simp

end Stable

end SSHecke

end VOA.Classification.COne
