/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSFinishLevel
import VOA.Huang.DLNAlgWord

/-!
# The Galois word from a scaled square-Galois twist law (Dong–Lin–Ng §4.3)

Let `ρ : SL(2, ℤ) →* Matrix ι ι ℂ` be a representation with `Γ(n) ≤ ker ρ`, put `s = ρ(S)`,
`t = ρ(T)`, and let `a b` satisfy `a b ≡ 1 (mod n)`.  Let `σ` be a field automorphism of `ℂ` and
`G` a matrix fixed by `σ` such that

* `σ(s) = G s` and `σ(s) G = s` (the Coste–Gannon signed-row law, DLN (4.4));
* `σ(t) = t^a` (`σ` restricts to `ζ_n ↦ ζ_n^a`);
* `G t = β · t^{a²} G` for **some scalar** `β` (the square-Galois twist law up to a scalar,
  DLN (4.10), which is what the Drinfeld-center Lemma 4.2 delivers before normalization).

Then `β = 1` and `G = ρ(t^a s t^b s t^a s⁻¹)` (`galoisWord_of_scaledTwist`).  This is the
algebraic part of the proof of DLN Theorem II(iii)–(iv) (arXiv:1201.6644v7, pp. 23–24), with
the scalar `β` eliminated exactly as there: `β³ = 1` from `(ST)³ = S²` under `σ²`, and
`σ⁻¹(β)⁴ = 1` from `S T S = T⁻¹ S T⁻¹` under `σ⁻¹` together with `W S W ≡ S (mod n)`.
-/

noncomputable section

namespace VOA.Huang.NSFinish

open Matrix VOA.Huang.DLN VOA.Huang.DLNAlg CongruenceSubgroup
open scoped MatrixGroups

/-! ## Identities in `SL(2, ℤ)` -/

theorem T_apply (i j : Fin 2) :
    ModularGroup.T i j = (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  have := T_zpow_apply 1 i j
  rwa [zpow_one] at this

theorem ST_cube : ModularGroup.S * ModularGroup.T * (ModularGroup.S * ModularGroup.T) *
    (ModularGroup.S * ModularGroup.T) = ModularGroup.S * ModularGroup.S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply', S_apply, T_apply]

theorem STS_eq : ModularGroup.S * ModularGroup.T * ModularGroup.S =
    ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply', S_apply, T_apply, Matrix.SpecialLinearGroup.SL2_inv_expl]

theorem word_alt (a b : ℤ) :
    ModularGroup.T ^ a * ModularGroup.S⁻¹ * ModularGroup.T ^ b * ModularGroup.S *
      ModularGroup.T ^ a * ModularGroup.S = diagonalWord a b := by
  ext i j
  rw [coe_diagonalWord]
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply', S_apply, T_zpow_apply, Matrix.SpecialLinearGroup.SL2_inv_expl] <;> ring

/-! ## Consequences of congruence -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rho_T_zpow_congr (ρ : SL2Z →* Matrix ι ι ℂ) {n : ℕ} (hk : KernelContainsGamma ρ n)
    {k l : ℤ} (hkl : k ≡ l [ZMOD n]) : ρ (ModularGroup.T ^ k) = ρ (ModularGroup.T ^ l) := by
  have hmem : ModularGroup.T ^ (k - l) ∈ Gamma n := by
    have e : ((k - l : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (Int.ModEq.dvd hkl.symm)
    rw [Gamma_mem]
    simp only [T_zpow_apply]
    simpa using e
  have h := hk _ hmem
  calc ρ (ModularGroup.T ^ k) = ρ (ModularGroup.T ^ (k - l) * ModularGroup.T ^ l) := by
        rw [← _root_.zpow_add, sub_add_cancel]
    _ = ρ (ModularGroup.T ^ l) := by rw [map_mul, h, one_mul]

/-- `W S W ≡ S (mod n)` for the diagonal word `W`. -/
theorem rho_word_S_word (ρ : SL2Z →* Matrix ι ι ℂ) {n : ℕ} (hk : KernelContainsGamma ρ n)
    {a b : ℤ} (hab : a * b ≡ 1 [ZMOD n]) :
    ρ (diagonalWord a b) * ρ ModularGroup.S * ρ (diagonalWord a b) = ρ ModularGroup.S := by
  rw [← map_mul, ← map_mul]
  apply hk.eq_of_reduction
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hw := diagonalWord_reduction hab
  have e : ((a : ℤ) : ZMod n) * (b : ZMod n) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff (a * b) 1 n).mpr hab
    push_cast at this
    exact this
  rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw]
  have hS : ((reduction n ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) :
      Matrix (Fin 2) (Fin 2) (ZMod n)) = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reduction, ModularGroup.coe_S]
  rw [hS]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e, mul_comm]

/-! ## Matrix maps along a field automorphism -/

/-- Entrywise application of `σ`, as a ring homomorphism of matrices. -/
abbrev mapσ (σ : ℂ ≃+* ℂ) : Matrix ι ι ℂ →+* Matrix ι ι ℂ := (σ : ℂ →+* ℂ).mapMatrix

theorem mapσ_smul (σ : ℂ ≃+* ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :
    mapσ σ (c • X) = σ c • mapσ σ X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem mapσ_symm_mapσ (σ : ℂ ≃+* ℂ) (X : Matrix ι ι ℂ) : mapσ σ.symm (mapσ σ X) = X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

/-- If `σ(ρ T) = ρ(T^c)`, then `σ(ρ(T^k)) = ρ(T^{c k})` for all integers `k`. -/
theorem mapσ_rho_T_zpow (ρ : SL2Z →* Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) {c : ℤ}
    (hT : mapσ σ (ρ ModularGroup.T) = ρ (ModularGroup.T ^ c)) (k : ℤ) :
    mapσ σ (ρ (ModularGroup.T ^ k)) = ρ (ModularGroup.T ^ (c * k)) := by
  let f : SL2Z →* Matrix ι ι ℂ := (mapσ σ).toMonoidHom.comp ρ
  have hu : f.toHomUnits ModularGroup.T = ρ.toHomUnits (ModularGroup.T ^ c) := by
    ext1
    exact hT
  have h2 : f.toHomUnits (ModularGroup.T ^ k) = ρ.toHomUnits (ModularGroup.T ^ (c * k)) := by
    rw [map_zpow, hu, ← map_zpow, ← _root_.zpow_mul]
  exact congrArg Units.val h2

/-! ## The DLN §4.3 algebra -/

theorem smul_eq_self_imp {X : Matrix ι ι ℂ} (hX : IsUnit X) [Nonempty ι] {c : ℂ}
    (h : c • X = X) : c = 1 := by
  obtain ⟨u, rfl⟩ := hX
  have h1 : c • (1 : Matrix ι ι ℂ) = 1 := by
    calc c • (1 : Matrix ι ι ℂ) = c • ((u : Matrix ι ι ℂ) * ↑u⁻¹) := by rw [Units.mul_inv]
      _ = (c • (u : Matrix ι ι ℂ)) * ↑u⁻¹ := by rw [smul_mul_assoc]
      _ = 1 := by rw [h, Units.mul_inv]
  let i : ι := Classical.arbitrary ι
  have := congrFun (congrFun h1 i) i
  simpa using this

/-- **DLN §4.3: the scaled twist law forces `β = 1` and the Galois word.** -/
theorem galoisWord_of_scaledTwist (ρ : SL2Z →* Matrix ι ι ℂ) {n : ℕ}
    (hk : KernelContainsGamma ρ n) {a b : ℤ} (hab : a * b ≡ 1 [ZMOD n]) (σ : ℂ ≃+* ℂ)
    (G : Matrix ι ι ℂ) (hGσ : mapσ σ G = G)
    (hrow : mapσ σ (ρ ModularGroup.S) = G * ρ ModularGroup.S)
    (hcol : mapσ σ (ρ ModularGroup.S) * G = ρ ModularGroup.S)
    (hT : mapσ σ (ρ ModularGroup.T) = ρ (ModularGroup.T ^ a)) (β : ℂ)
    (htw : G * ρ ModularGroup.T = β • (ρ (ModularGroup.T ^ (a * a)) * G)) :
    G = ρ (diagonalWord a b) ∧ (Nonempty ι → β = 1) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨Subsingleton.elim _ _, fun h => (IsEmpty.false (Classical.choice h)).elim⟩
  -- notation
  set s := ρ ModularGroup.S with hs
  set si := ρ ModularGroup.S⁻¹ with hsi
  have hssi : s * si = 1 := by rw [hs, hsi, ← map_mul, mul_inv_cancel, map_one]
  have hsis : si * s = 1 := by rw [hs, hsi, ← map_mul, inv_mul_cancel, map_one]
  let tt : ℤ → Matrix ι ι ℂ := fun k => ρ (ModularGroup.T ^ k)
  have htt : ∀ k l, tt k * tt l = tt (k + l) := by
    intro k l; simp only [tt, ← map_mul, ← _root_.zpow_add]
  have tt0 : tt 0 = 1 := by simp [tt]
  have tt1 : tt 1 = ρ ModularGroup.T := by simp [tt]
  have ttm1 : tt (-1) = ρ ModularGroup.T⁻¹ := by simp [tt]
  have ttc : ∀ {k l}, k ≡ l [ZMOD n] → tt k = tt l := fun h => rho_T_zpow_congr ρ hk h
  -- `G s G = s` and the inverse `Gi = s G s⁻¹`
  have hGsG : G * s * G = s := by rw [← hrow]; exact hcol
  set Gi := s * G * si with hGi
  have hGGi : G * Gi = 1 := by
    rw [hGi, ← mul_assoc, ← mul_assoc, hGsG, hssi]
  have hGiG : Gi * G = 1 := mul_eq_one_comm.mp hGGi
  have hGs : G * s = s * Gi := by
    calc G * s = G * s * (G * Gi) := by rw [hGGi, mul_one]
      _ = s * Gi := by rw [← mul_assoc, hGsG]
  have hsG : s * G = Gi * s := by
    calc s * G = Gi * (G * s * G) := by simp only [← mul_assoc, hGiG, one_mul]
      _ = Gi * s := by rw [hGsG]
  -- powers of `T` under `σ`, `σ⁻¹`
  have hTa : ∀ k, mapσ σ (tt k) = tt (a * k) := mapσ_rho_T_zpow ρ σ hT
  have hTb1 : mapσ σ.symm (ρ ModularGroup.T) = ρ (ModularGroup.T ^ b) := by
    have h := hTa b
    rw [ttc (k := a * b) (l := 1) hab, tt1] at h
    rw [← h, mapσ_symm_mapσ]
  have hTb : ∀ k, mapσ σ.symm (tt k) = tt (b * k) := mapσ_rho_T_zpow ρ σ.symm hTb1
  have hGσ' : mapσ σ.symm G = G := by
    have h := mapσ_symm_mapσ σ G
    rwa [hGσ] at h
  have hsσ' : mapσ σ.symm s = Gi * s := by
    have h : s = G * mapσ σ.symm s := by
      have := congrArg (mapσ σ.symm) hrow
      rw [mapσ_symm_mapσ, map_mul, hGσ'] at this
      exact this
    calc mapσ σ.symm s = Gi * (G * mapσ σ.symm s) := by rw [← mul_assoc, hGiG, one_mul]
      _ = Gi * s := by rw [← h]
  set β' := σ.symm β with hβ'
  -- twist law transported by `σ⁻¹`: `G t^b = β' t^a G`
  have htw' : G * tt b = β' • (tt a * G) := by
    have h := congrArg (mapσ σ.symm) htw
    rw [map_mul, mapσ_smul, map_mul, hGσ', ← tt1, hTb, hTb, mul_one] at h
    have e : b * (a * a) ≡ a [ZMOD n] := by
      have h' := Int.ModEq.mul_left a hab
      rwa [mul_one, show a * (a * b) = b * (a * a) by ring] at h'
    rw [h, ttc e]
  -- `t^{-a} G = β' G t^{-b}`
  have htw'' : tt (-a) * G = β' • (G * tt (-b)) := by
    calc tt (-a) * G = tt (-a) * (G * tt b) * tt (-b) := by
          rw [mul_assoc, mul_assoc, htt, add_neg_cancel, tt0, mul_one]
      _ = tt (-a) * (β' • (tt a * G)) * tt (-b) := by rw [htw']
      _ = β' • (G * tt (-b)) := by
          rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, htt, neg_add_cancel, tt0, one_mul]
  -- the braid relation under `σ⁻¹`
  have hbraid := congrArg (fun X => mapσ σ.symm X) (congrArg ρ STS_eq)
  simp only [map_mul] at hbraid
  rw [← hs, ← ttm1, ← tt1, hsσ', hTb, hTb, mul_one, mul_neg_one] at hbraid
  -- `hbraid : Gi s t^b Gi s = t^{-b} Gi s t^{-b}`; rewrite `Gi s = s G`.
  rw [← hsG] at hbraid
  have key : β' • (β' • (s * tt a * s)) = tt (-b) * s * tt (-a) * G := by
    have l : s * G * tt b * (s * G) = β' • (s * tt a * s) := by
      calc s * G * tt b * (s * G) = s * (G * tt b) * s * G := by simp only [mul_assoc]
        _ = s * (β' • (tt a * G)) * s * G := by rw [htw']
        _ = β' • (s * tt a * (G * s * G)) := by
            simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
        _ = β' • (s * tt a * s) := by rw [hGsG]
    have r : β' • (tt (-b) * (s * G) * tt (-b)) = tt (-b) * s * tt (-a) * G := by
      rw [mul_assoc (tt (-b) * s) (tt (-a)) G, htw'']
      simp only [mul_smul_comm, mul_assoc]
    rw [← l, hbraid, r]
  -- solve for `G`
  have hW : G = (β' * β') • ρ (diagonalWord a b) := by
    rw [← word_alt]
    simp only [map_mul]
    change G = (β' * β') • (tt a * si * tt b * s * tt a * s)
    have e1 : tt a * si * tt b * (tt (-b) * s * tt (-a) * G) = G := by
      calc tt a * si * tt b * (tt (-b) * s * tt (-a) * G)
          = tt a * si * (tt b * tt (-b)) * s * tt (-a) * G := by simp only [mul_assoc]
        _ = tt a * (si * s) * (tt (-a) * G) := by
            rw [htt, add_neg_cancel, tt0]; simp only [mul_assoc, one_mul]
        _ = G := by rw [hsis, mul_one, ← mul_assoc, htt, add_neg_cancel, tt0, one_mul]
    rw [← e1, ← key]
    simp only [mul_smul_comm, smul_smul, mul_assoc]
  -- `c² = 1` for `c = β'²`
  have hsU : IsUnit s := ⟨⟨s, si, hssi, hsis⟩, rfl⟩
  have hc2 : (β' * β') * (β' * β') = 1 := by
    apply smul_eq_self_imp hsU
    have h := hGsG
    rw [hW] at h
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at h
    rwa [rho_word_S_word ρ hk hab] at h
  -- `β³ = 1` from `(ST)³ = S²` under `σ²`
  have hGU : IsUnit G := ⟨⟨G, Gi, hGGi, hGiG⟩, rfl⟩
  have htU : IsUnit (ρ ModularGroup.T) := by
    refine ⟨⟨ρ ModularGroup.T, ρ ModularGroup.T⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel, map_one]
    · rw [← map_mul, inv_mul_cancel, map_one]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at htw
    have : IsUnit (G * ρ ModularGroup.T) := hGU.mul htU
    rw [htw] at this
    exact not_isUnit_zero this
  have hβ3 : β * β * β = 1 := by
    have hcube := congrArg (fun X => mapσ σ (mapσ σ X)) (congrArg ρ ST_cube)
    simp only [map_mul] at hcube
    rw [← hs, ← tt1, hTa, hTa, hrow, map_mul, hGσ, hrow, mul_one] at hcube
    -- `σ² s = G s Gi`, `t^{a a} = β⁻¹ G t Gi`
    have h1 : G * (G * s) = G * s * Gi := by rw [hGs, ← mul_assoc, ← hGs]
    have h2 : tt (a * a) = β⁻¹ • (G * ρ ModularGroup.T * Gi) := by
      rw [htw, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hβ0, one_smul, mul_assoc, hGGi,
        mul_one]
    rw [h1, h2] at hcube
    have h3 : G * s * Gi * (β⁻¹ • (G * ρ ModularGroup.T * Gi)) =
        β⁻¹ • (G * (s * ρ ModularGroup.T) * Gi) := by
      rw [mul_smul_comm]
      congr 1
      simp only [mul_assoc]
      rw [← mul_assoc Gi G, hGiG, one_mul]
    rw [h3] at hcube
    have hst := congrArg ρ ST_cube
    simp only [map_mul] at hst
    rw [← hs] at hst
    have lhs : β⁻¹ • (G * (s * ρ ModularGroup.T) * Gi) *
        (β⁻¹ • (G * (s * ρ ModularGroup.T) * Gi)) *
        (β⁻¹ • (G * (s * ρ ModularGroup.T) * Gi)) =
        (β⁻¹ * β⁻¹ * β⁻¹) • (G * (s * s) * Gi) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      · ring
      rw [← hst]
      simp only [mul_assoc]
      rw [← mul_assoc Gi G, hGiG, one_mul, ← mul_assoc Gi G, hGiG, one_mul]
    have rhs : G * s * Gi * (G * s * Gi) = G * (s * s) * Gi := by
      simp only [mul_assoc]
      rw [← mul_assoc Gi G, hGiG, one_mul]
    rw [lhs, rhs] at hcube
    have hXU : IsUnit (G * (s * s) * Gi) :=
      (hGU.mul (hsU.mul hsU)).mul ⟨⟨Gi, G, hGiG, hGGi⟩, rfl⟩
    have := smul_eq_self_imp hXU hcube
    have h' : (β * β * β) * (β⁻¹ * β⁻¹ * β⁻¹) = 1 := by field_simp
    rw [this, mul_one] at h'
    exact h'
  -- conclude `β' = 1`
  have hβ'3 : β' * β' * β' = 1 := by
    rw [hβ', ← map_mul, ← map_mul, hβ3, map_one]
  have hβ'1 : β' = 1 := by
    have : β' * (β' * β' * β') = 1 := by linear_combination hc2
    rwa [hβ'3, mul_one] at this
  refine ⟨by rw [hW, hβ'1]; simp, fun _ => ?_⟩
  have : σ β' = σ 1 := by rw [hβ'1]
  rwa [hβ', RingEquiv.apply_symm_apply, map_one] at this

end VOA.Huang.NSFinish
