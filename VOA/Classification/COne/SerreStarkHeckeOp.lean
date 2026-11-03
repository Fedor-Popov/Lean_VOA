/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeLaw

/-!
# Serre–Stark S3-1e: Shimura's Hecke operator `T(p²)` preserves `M_{1/2}(N, χ)`

For a prime `p ∤ N` (`24 ∣ N`) and a Dirichlet character `χ` mod `N`,

`T(p²) f (τ) = p⁻² Σ_{b mod p²} f((τ+b)/p²) + χ(p) (p g_p)⁻¹ Σ_{h mod p} (h/p) f(τ + h/p)
  + χ(p)² p⁻¹ f(p²τ)`

(`g_p = g(p, 1)`, the quadratic Gauss sum). Proved here:

* `heckeT_law`: if `f` satisfies the `χ`-twisted `θ`-multiplier law on `Γ₀(N)` then so does
  `T(p²) f` (the law holds on generators by the theta transport laws, and the set of `γ` on which
  it holds is a subgroup, `lawGroup`, which contains `Γ₀(N)` by `mem_lawGroup_of_Gamma0`).
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The character factor `κ_i = χ(a_i)` (`a_i ∈ {1, p, p²}`). -/
def kap (p : ℕ) (i : HIdx p) : ℂ := χ ((aCo p i : ℤ) : ZMod N)

/-- **Shimura's Hecke operator `T(p²)`** on functions on `ℍ`. -/
def heckeT (p : ℕ) [Fact p.Prime] (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  ∑ i : HIdx p, hw p i * kap χ p i * f (mobZ (cosetMat p i) τ)

/-- The `χ`-twisted `θ`-multiplier law at `γ`. -/
def ChiLaw (F : ℂ → ℂ) (γ : SL(2, ℤ)) : Prop :=
  ∀ τ : ℂ, 0 < τ.im →
    F (mobius γ τ) * thetaRef τ = χ ((γ 1 1 : ℤ) : ZMod N) * thetaRef (mobius γ τ) * F τ

/-! ## The group of `γ` on which a law holds -/

theorem gamma0_d_mul {γ δ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (((γ * δ) 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) * ((δ 1 1 : ℤ) : ZMod N) := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hγ]; ring

/-- The subgroup of `γ ∈ Γ₀(N)` satisfying the law for `F`. -/
def lawGroup (F : ℂ → ℂ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧ ChiLaw χ F γ}
  one_mem' := ⟨Subgroup.one_mem _, fun τ _ => by simp [mobius_one, mul_comm]⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, lγ⟩ ⟨hδ, lδ⟩
    refine ⟨Subgroup.mul_mem _ hγ hδ, fun τ hτ => ?_⟩
    have hδτ := im_mobius_pos δ hτ
    have hθ := thetaRef_ne_zero_of_im_pos hδτ
    have h1 := lγ _ hδτ
    have h2 := lδ τ hτ
    rw [mobius_mul _ _ hτ, gamma0_d_mul hγ, map_mul]
    apply mul_right_cancel₀ hθ
    linear_combination (thetaRef τ) * h1 + χ ((γ 1 1 : ℤ) : ZMod N) *
      thetaRef (mobius γ (mobius δ τ)) * h2
  inv_mem' := by
    rintro γ ⟨hγ, lγ⟩
    refine ⟨Subgroup.inv_mem _ hγ, fun τ hτ => ?_⟩
    have hw := im_mobius_pos γ⁻¹ hτ
    have h1 := lγ _ hw
    rw [← mobius_mul _ _ hτ, mul_inv_cancel, mobius_one] at h1
    have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) γ.det_coe
      simp only [Matrix.det_fin_two] at this
      push_cast at this
      rw [CongruenceSubgroup.Gamma0_mem.1 hγ, mul_zero, sub_zero] at this
      exact this
    have hinv : ((γ⁻¹ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) := by
      simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [hinv]
    have hχ : χ ((γ 0 0 : ℤ) : ZMod N) * χ ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      rw [← map_mul, hdet, map_one]
    linear_combination (-χ ((γ 0 0 : ℤ) : ZMod N)) * h1 - F (mobius γ⁻¹ τ) * thetaRef τ * hχ


/-! ## Assembly: from a theta transport law to the `χ`-law of `T(p²) f` -/

theorem chi_ne_zero_of_isUnit {a : ZMod N} (ha : IsUnit a) : χ a ≠ 0 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  intro h0
  have := congrArg χ hb
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

variable {p : ℕ} (hp : p.Prime)

theorem kap_rel (hpN : Nat.Coprime p N) {i j : HIdx p} {γ δ : Matrix (Fin 2) (Fin 2) ℤ}
    (hγ : (N : ℤ) ∣ γ 1 0) (h : cosetMat p i * γ = δ * cosetMat p j) :
    χ ((δ 1 1 : ℤ) : ZMod N) * kap χ p i = χ ((γ 1 1 : ℤ) : ZMod N) * kap χ p j := by
  have h1 := congrArg χ (fact_11_mod hpN hγ h)
  rw [map_mul, map_mul] at h1
  have hai := congrArg (fun x : ℤ => χ (x : ZMod N)) (aCo_mul_dCo p i)
  have haj := congrArg (fun x : ℤ => χ (x : ZMod N)) (aCo_mul_dCo p j)
  simp only [Int.cast_mul, map_mul] at hai haj
  have hP : χ (((p : ℤ) ^ 2 : ℤ) : ZMod N) ≠ 0 := by
    apply chi_ne_zero_of_isUnit
    exact isUnit_of_coprime (by
      have := (Nat.isCoprime_iff_coprime.2 hpN).pow_left (m := 2); exact this)
  apply mul_right_cancel₀ hP
  unfold kap
  linear_combination (χ ((aCo p i : ℤ) : ZMod N) * χ ((aCo p j : ℤ) : ZMod N)) * h1 -
    (χ ((δ 1 1 : ℤ) : ZMod N) * χ ((aCo p i : ℤ) : ZMod N)) * haj +
    (χ ((γ 1 1 : ℤ) : ZMod N) * χ ((aCo p j : ℤ) : ZMod N)) * hai

include hp in
/-- **Assembly.** A factorisation `A_i γ = δ_i A_{σ i}` together with the theta transport law
for `γ` gives the `χ`-law of `T(p²) f` at `γ`. -/
theorem chiLaw_heckeT [Fact p.Prime] (hpN : Nat.Coprime p N) {f : ℂ → ℂ}
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ChiLaw χ f γ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (σ : HIdx p → HIdx p)
    (δ : HIdx p → Matrix (Fin 2) (Fin 2) ℤ)
    (hfact : ∀ i, cosetMat p i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = δ i * cosetMat p (σ i))
    (hlaw : ThetaLaw p γ σ) : ChiLaw χ (heckeT χ p f) γ := by
  intro τ hτ
  have hp0 := hp.pos
  have hγ10 : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  have hσ : Function.Bijective σ := (sigma_injective hp.two_le γ σ δ hfact).bijective_of_finite
  have hγτ := im_mobius_pos γ hτ
  -- each term
  have term : ∀ i, hw p i * kap χ p i * f (mobZ (cosetMat p i) (mobius γ τ)) * thetaRef τ =
      χ ((γ 1 1 : ℤ) : ZMod N) * thetaRef (mobius γ τ) *
        (hw p (σ i) * kap χ p (σ i) * f (mobZ (cosetMat p (σ i)) τ)) := by
    intro i
    set g := factSL hp0 γ (δ i) (hfact i)
    have hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = δ i := rfl
    have hgΓ : g ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by
        rw [hg]; exact fact_dvd_10 hpN hγ10 (hfact i))
    have hwp := im_mobZ_cosetMat hp0 (σ i) hτ
    have hmob : mobZ (cosetMat p i) (mobius γ τ) = mobius g (mobZ (cosetMat p (σ i)) τ) := by
      rw [← mobZ_cosetMat_mul_SL i γ hτ, hfact i, ← hg, mobZ_SL_mul_cosetMat hp0 g]
    have hfl := hf g hgΓ _ hwp
    have hk := kap_rel χ hpN hγ10 (hfact i)
    rw [← hg] at hk
    have hl := hlaw i τ hτ
    rw [hmob] at hl ⊢
    have hθw := thetaRef_ne_zero_of_im_pos hwp
    apply mul_right_cancel₀ hθw
    linear_combination (hw p i * kap χ p i * thetaRef τ) * hfl +
      (f (mobZ (cosetMat p (σ i)) τ) * thetaRef τ * thetaRef (mobius g (mobZ (cosetMat p (σ i)) τ))
        * hw p i) * hk +
      (χ ((γ 1 1 : ℤ) : ZMod N) * kap χ p (σ i) * f (mobZ (cosetMat p (σ i)) τ)) * hl
  unfold heckeT
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [term]
  exact (Equiv.ofBijective σ hσ).sum_comp (fun j => χ ((γ 1 1 : ℤ) : ZMod N) *
    thetaRef (mobius γ τ) * (hw p j * kap χ p j * f (mobZ (cosetMat p j) τ)))


/-! ## Generation of `Γ₀(N)` -/

theorem matT_eq : matT = ModularGroup.T := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matT, ModularGroup.T]

theorem coe_matT_zpow (n : ℤ) :
    ((matT ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := by
  rw [matT_eq, ModularGroup.coe_T_zpow]

theorem coe_matL_zpow (N : ℕ) (y : ℤ) :
    ((matL N ^ y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; N * y, 1] := by
  have h : matL N = ModularGroup.S * ModularGroup.T ^ (-(N : ℤ)) * ModularGroup.S⁻¹ := by
    rw [matL_eq_word, ← mul_assoc]
    congr 2
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [h, conj_zpow, ← zpow_mul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S,
      Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.vecMul, dotProduct]

theorem matT_zpow_mul_apply (n : ℤ) (γ : SL(2, ℤ)) :
    (matT ^ n * γ) 0 0 = γ 0 0 + n * γ 1 0 ∧ (matT ^ n * γ) 0 1 = γ 0 1 + n * γ 1 1 ∧
      (matT ^ n * γ) 1 0 = γ 1 0 ∧ (matT ^ n * γ) 1 1 = γ 1 1 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_matT_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp

theorem matL_zpow_mul_apply (N : ℕ) (y : ℤ) (γ : SL(2, ℤ)) :
    (matL N ^ y * γ) 0 0 = γ 0 0 ∧ (matL N ^ y * γ) 0 1 = γ 0 1 ∧
      (matL N ^ y * γ) 1 0 = N * y * γ 0 0 + γ 1 0 ∧
      (matL N ^ y * γ) 1 1 = N * y * γ 0 1 + γ 1 1 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_matL_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp

theorem det_SL' (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe; rwa [Matrix.det_fin_two] at this

/-- **Generation.** Every `γ ∈ Γ₀(N)` is `T^{−ε} L^{−Ny} T^{−x} γ₂` with
`γ₂ ≡ diag(ℓ, ℓ') (mod N p²)`. -/
theorem gamma0_decomp (hp : p.Prime) (hpN : ¬ (p : ℤ) ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ (ε y x : ℤ) (γ₂ : SL(2, ℤ)) (ℓ : ℕ) (ℓ' : ℤ),
      γ = matT ^ (-ε) * matL N ^ (-y) * matT ^ (-x) * γ₂ ∧ ℓ.Coprime (N * p ^ 2) ∧
      (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD (N * p ^ 2 : ℕ)] ∧ γ₂ 0 0 ≡ ℓ [ZMOD (N * p ^ 2 : ℕ)] ∧
      γ₂ 1 1 ≡ ℓ' [ZMOD (N * p ^ 2 : ℕ)] ∧ γ₂ 0 1 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] ∧
      γ₂ 1 0 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hγ10 : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  -- step A
  set ε : ℤ := if (p : ℤ) ∣ γ 0 0 then 1 else 0 with hε
  set γ₀ := matT ^ ε * γ with hγ₀
  obtain ⟨a0, b0, c0, d0⟩ := matT_zpow_mul_apply ε γ
  have ha0 : ¬ (p : ℤ) ∣ γ₀ 0 0 := by
    rw [a0]
    by_cases hd : (p : ℤ) ∣ γ 0 0
    · rw [hε, if_pos hd, one_mul]
      intro h2
      have hc : (p : ℤ) ∣ γ 1 0 := by simpa using dvd_sub h2 hd
      have := det_SL' γ
      have h1 : (p : ℤ) ∣ γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 :=
        dvd_sub (dvd_mul_of_dvd_left hd _) (dvd_mul_of_dvd_right hc _)
      rw [this] at h1
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
    · rw [hε, if_neg hd, zero_mul, add_zero]; exact hd
  -- step B
  have hNa : ¬ (p : ℤ) ∣ N * γ₀ 0 0 := by
    intro h; rcases hpp.dvd_or_dvd h with h | h
    · exact hpN h
    · exact ha0 h
  set y : ℤ := -(γ₀ 1 0) * binv (p ^ 2) (N * γ₀ 0 0) with hy
  set γ₁ := matL N ^ y * γ₀ with hγ₁
  obtain ⟨a1, b1, c1, d1⟩ := matL_zpow_mul_apply N y γ₀
  have hc1p : (p : ℤ) ^ 2 ∣ γ₁ 1 0 := by
    rw [c1]
    have hb := binv_spec (isCoprime_sq_of_not_dvd hp hNa)
    have := Int.ModEq.dvd ((hb.mul_left (-(γ₀ 1 0))))
    push_cast at this
    have e : (N : ℤ) * y * γ₀ 0 0 + γ₀ 1 0 =
        -((-(γ₀ 1 0) * 1) - (-(γ₀ 1 0)) * ((N * γ₀ 0 0) * binv (p ^ 2) (N * γ₀ 0 0))) := by
      rw [hy]; ring
    rw [e]
    exact (dvd_neg).2 this
  have hc1N : (N : ℤ) ∣ γ₁ 1 0 := by
    rw [c1, c0]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) hγ10
  have hcop : IsCoprime ((p : ℤ) ^ 2) (N : ℤ) :=
    (isCoprime_of_not_dvd hp hpN).symm.pow_left
  have hc1 : ((N * p ^ 2 : ℕ) : ℤ) ∣ γ₁ 1 0 := by
    push_cast; rw [mul_comm]; exact hcop.mul_dvd hc1p hc1N
  -- step C
  have hd1 : IsCoprime (γ₁ 1 1) ((N * p ^ 2 : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := hc1
    refine ⟨γ₁ 0 0, -(γ₁ 0 1 * k), ?_⟩
    have := det_SL' γ₁
    rw [hk] at this
    linear_combination this
  set x : ℤ := -(γ₁ 0 1) * binv (N * p ^ 2) (γ₁ 1 1) with hx
  set γ₂ := matT ^ x * γ₁ with hγ₂
  obtain ⟨a2, b2, c2, d2⟩ := matT_zpow_mul_apply x γ₁
  have hb2 : γ₂ 0 1 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] := by
    rw [b2]
    have hb := binv_spec hd1
    refine Int.modEq_iff_dvd.2 ?_
    have := Int.ModEq.dvd (hb.mul_left (-(γ₁ 0 1)))
    have e : (0 : ℤ) - (γ₁ 0 1 + x * γ₁ 1 1) =
        -(γ₁ 0 1) * 1 - (-(γ₁ 0 1)) * (γ₁ 1 1 * binv (N * p ^ 2) (γ₁ 1 1)) := by
      rw [hx]; ring
    rw [e]; exact this
  have hc2 : γ₂ 1 0 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] := by
    rw [c2]; exact (Int.modEq_zero_iff_dvd.2 hc1)
  -- `ℓ`
  have hM : 0 < N * p ^ 2 := by
    have : N ≠ 0 := by rintro rfl; exact hpN (dvd_zero _)
    have := hp.pos
    positivity
  have had : γ₂ 0 0 * γ₂ 1 1 ≡ 1 [ZMOD (N * p ^ 2 : ℕ)] := by
    have := det_SL' γ₂
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.1 hc2
    refine Int.modEq_iff_dvd.2 ⟨-(γ₂ 0 1 * k), ?_⟩
    rw [hk] at this
    linear_combination (-1 : ℤ) * this
  set ℓ : ℕ := (γ₂ 0 0 % ((N * p ^ 2 : ℕ) : ℤ)).toNat with hℓ
  have hℓeq : (ℓ : ℤ) = γ₂ 0 0 % ((N * p ^ 2 : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))
  have hℓmod : γ₂ 0 0 ≡ ℓ [ZMOD (N * p ^ 2 : ℕ)] := by
    rw [hℓeq]; exact (Int.mod_modEq _ _).symm
  have hℓℓ : (ℓ : ℤ) * γ₂ 1 1 ≡ 1 [ZMOD (N * p ^ 2 : ℕ)] :=
    (hℓmod.symm.mul_right _).trans had
  have hℓcop : ℓ.Coprime (N * p ^ 2) := by
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 hℓℓ.symm
    have : IsCoprime (ℓ : ℤ) ((N * p ^ 2 : ℕ) : ℤ) := ⟨γ₂ 1 1, -t, by linear_combination ht⟩
    exact Nat.isCoprime_iff_coprime.1 this
  refine ⟨ε, y, x, γ₂, ℓ, γ₂ 1 1, ?_, hℓcop, hℓℓ, hℓmod, Int.ModEq.refl _, hb2, hc2⟩
  rw [hγ₂, hγ₁, hγ₀]
  group


/-! ## The main law -/

theorem dvd_sub_of_modEq {M m : ℕ} (hm : m ∣ M) {a b : ℤ} (h : a ≡ b [ZMOD M]) :
    (m : ℤ) ∣ a - b := by
  have := (Int.ModEq.dvd h.symm)
  exact (Int.natCast_dvd_natCast.2 hm).trans this

theorem not_dvd_of_coprime' {p N : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) :
    ¬ (p : ℤ) ∣ N := by
  intro h
  have : p ∣ N := by exact_mod_cast h
  have := Nat.dvd_gcd (dvd_refl p) this
  rw [hpN] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

include hp in
/-- **Shimura's `T(p²)` preserves the `χ`-twisted `θ`-multiplier law on `Γ₀(N)`**
(`24 ∣ N`, `p ∤ N` an odd prime). -/
theorem heckeT_chiLaw [Fact p.Prime] (hp2 : p ≠ 2) (h24 : 24 ∣ N) (hpN : Nat.Coprime p N)
    {f : ℂ → ℂ} (hf : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ChiLaw χ f γ) :
    ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ChiLaw χ (heckeT χ p f) γ := by
  have hpNZ := not_dvd_of_coprime' hp hpN
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  obtain ⟨K₀, hK₀⟩ := h4
  have hNK : (N : ℤ) = 4 * (K₀ : ℤ) := by rw [hK₀]; push_cast; ring
  have h4' : 4 ∣ N := ⟨K₀, hK₀⟩
  set G := lawGroup χ (heckeT χ p f)
  have hT : matT ∈ G := ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N (matT_mem_Gamma1 N),
    chiLaw_heckeT χ hp hpN hf (CongruenceSubgroup.Gamma1_in_Gamma0 N (matT_mem_Gamma1 N))
      (sigmaT hp) (deltaT hp) (factT hp) (thetaLaw_T hp)⟩
  have hLΓ : matL N ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [matL]
  have hL : matL N ∈ G := ⟨hLΓ, chiLaw_heckeT χ hp hpN hf hLΓ (sigmaL hp N) (deltaL hp N)
    (factL hp N hpNZ) (thetaLaw_L hp hp2 hNK h24 hpNZ)⟩
  have hMp : p ^ 2 ∣ N * p ^ 2 := dvd_mul_left _ _
  have hMN : N ∣ N * p ^ 2 := dvd_mul_right _ _
  have hG3 : ∀ (γ₂ : SL(2, ℤ)) (ℓ : ℕ) (ℓ' : ℤ), ℓ.Coprime (N * p ^ 2) →
      (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD (N * p ^ 2 : ℕ)] → γ₂ 0 0 ≡ ℓ [ZMOD (N * p ^ 2 : ℕ)] →
      γ₂ 1 1 ≡ ℓ' [ZMOD (N * p ^ 2 : ℕ)] → γ₂ 0 1 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] →
      γ₂ 1 0 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)] → γ₂ ∈ G := by
    intro γ₂ ℓ ℓ' hℓ hℓℓ h00 h11 h01 h10
    have hΓ : γ₂ ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by
        have := dvd_sub_of_modEq hMN h10; simpa using this)
    have e00 := dvd_sub_of_modEq hMp h00
    have e11 := dvd_sub_of_modEq hMp h11
    have e01 : ((p ^ 2 : ℕ) : ℤ) ∣ γ₂ 0 1 := by simpa using dvd_sub_of_modEq hMp h01
    have e10 : ((p ^ 2 : ℕ) : ℤ) ∣ γ₂ 1 0 := by simpa using dvd_sub_of_modEq hMp h10
    have eℓ : ((p ^ 2 : ℕ) : ℤ) ∣ (ℓ : ℤ) * ℓ' - 1 := dvd_sub_of_modEq hMp hℓℓ
    push_cast at e00 e11 e01 e10 eℓ
    exact ⟨hΓ, chiLaw_heckeT χ hp hpN hf hΓ (sigmaG hp ℓ') (deltaG hp ℓ' γ₂)
      (factG hp ℓ' ℓ γ₂ e00 e11 e01 e10 eℓ)
      (thetaLaw_G hp h4' h24 ℓ hℓ ℓ' hℓℓ γ₂ h00 h11 h01 h10)⟩
  intro γ hγ
  obtain ⟨ε, y, x, γ₂, ℓ, ℓ', hdec, hℓ, hℓℓ, h00, h11, h01, h10⟩ := gamma0_decomp hp hpNZ hγ
  have hmem : γ ∈ G := by
    rw [hdec]
    exact G.mul_mem (G.mul_mem (G.mul_mem (G.zpow_mem hT _) (G.zpow_mem hL _))
      (G.zpow_mem hT _)) (hG3 γ₂ ℓ ℓ' hℓ hℓℓ h00 h11 h01 h10)
  exact hmem.2

end SSHecke

end VOA.Classification.COne
