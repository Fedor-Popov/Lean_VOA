import VOA.DeligneAudit.SL4TAdjointSiteKernelRelations

/-!
# Corollary K: the ring kernel at one adjoint site

Let `v` satisfy the local Weyl relations of weight `(1, B, 1)`, `f₂(h) v = 0` with `h ≥ 1`, and
let every current of mode at least `h + 1` vanish.

* **Lemma J₂ at level one** (`adjointSite_middleRadicalShift_mem_higherRadical`): shifting one
  `y`-letter of the zero-mode word `x^{d₁} y^{d₂} z^{d₃} v` to mode `h` gives a vector of
  `M_{>d}`, for `d₁ ≤ 1`. Without an `x`-letter, `y(h) = [g(h), x]` and `g(h)` kills the word
  without its `x`-letter, so the vector is `g(h)` of a vector of the higher key
  `(1, d₂ - 1, d₃)`; with one `x`-letter, `x² v = 0` gives `x y(h) W = -x y(h) W`.
* **Lemma J₃⁰ at level one** (`adjointSite_compoundHighMode_mem_higherRadical`):
  `q(h) y^n z v ∈ M_{>(0,n,1)}`, from `z = [F, y]`, `q(h) F v = 0` and the higher key
  `(0, n + 1, 0)`.
* **Theorem J₃¹(h)** (`adjointSite_compoundAlphabet_marked_zero`), **Lemma J₃⁰**
  (`adjointSite_compoundAlphabet_unmarked_zero`) and **Lemma J₂**
  (`adjointSite_middleRadical_mode_zero`): the vanishing of `π(p_h(g₂))` on the blocks over
  `(1, ·, 1)` and `(0, ·, 1)`, and of `π(p_h(x₂))` on every block. The proofs apply the
  explicit Cartan operators of `SL4TAdjointSiteKernelRelations` to the zero-mode representative
  of `π(1)`; for J₃¹ the result is `e₂ · q^{e₂-1} q(h) g^{e₁} x y^{d₂} z v`, which lies in the
  higher second Levi subspace by Proposition J and Lemma M(ii).
* **Corollary K** (`adjointSite_kernelIdeal_le_kernel`): `I_J(h) ⊆ ker π` on every block.
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- **The level-1 step of Lemma J₃⁰.** `q(h) y^n z v ∈ M_{>(0, n, 1)}`. -/
theorem adjointSite_compoundHighMode_mem_higherRadical (B h : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0) (n : ℕ) :
    ρ.op 10 h ((ρ.op 7 0 ^ n) (ρ.op 8 0 w)) ∈ higherRadicalCountClosure ρ w ![0, n, 1] := by
  have hqF : ρ.op 10 h (ρ.op 11 0 w) = 0 := (adjointSite_transported_relations ρ w B h hW hg).1
  have hhigh : (ρ.op 7 0 ^ (n + 1)) w ∈ higherRadicalCountClosure ρ w ![0, n, 1] := by
    have hk : higherRadicalCounts ![0, n, 1] ⟨0, n + 1, 0, 0⟩ := by
      simp [higherRadicalCounts]
    simpa using zeroModeWord_mem_higherRadical ρ w ![0, n, 1] 0 (n + 1) 0 hk
  have h₁ : ρ.op 10 h (ρ.op 11 0 ((ρ.op 7 0 ^ (n + 1)) w)) ∈
      higherRadicalCountClosure ρ w ![0, n, 1] := by
    rw [op_comm_of_zero_bracket ρ bracket_lastPair_last h 0]
    exact a3LeviClosure_inv ρ _ 4 0 (a3LeviClosure_inv ρ _ 5 h hhigh)
  have hz : ρ.op 8 0 ((ρ.op 7 0 ^ n) w) =
      ρ.op 11 0 ((ρ.op 7 0 ^ (n + 1)) w) - ρ.op 7 0 (ρ.op 11 0 ((ρ.op 7 0 ^ n) w)) := by
    have hc := op_comm_of_single_bracket ρ bracket_last_compound 0 0 ((ρ.op 7 0 ^ n) w)
    rw [pow_succ', Module.End.mul_apply, hc]
    simp
  have hyF : ρ.op 7 0 (ρ.op 11 0 ((ρ.op 7 0 ^ n) w)) =
      (ρ.op 7 0 ^ (n + 1)) (ρ.op 11 0 w) + (n : ℂ) • (ρ.op 7 0 ^ n) (ρ.op 8 0 w) := by
    cases n with
    | zero => simp
    | succ m =>
      rw [last_compoundPower_comm ρ 0 m w, map_add, map_smul,
        ← Module.End.mul_apply (ρ.op 7 0) (ρ.op 7 0 ^ (m + 1)), ← pow_succ',
        ← Module.End.mul_apply (ρ.op 7 0) (ρ.op 7 0 ^ m), ← pow_succ']
  have hq0 : ρ.op 10 h ((ρ.op 7 0 ^ (n + 1)) (ρ.op 11 0 w)) = 0 := by
    rw [op_pow_comm_of_zero_bracket ρ bracket_lastPair_compound, hqF, map_zero]
  have hzy : ρ.op 8 0 ((ρ.op 7 0 ^ n) w) = (ρ.op 7 0 ^ n) (ρ.op 8 0 w) :=
    op_pow_comm_of_zero_bracket ρ bracket_highest_compound 0 0 n w
  have e₁ := congrArg (ρ.op 10 h) hz
  rw [hzy, map_sub, hyF, map_add, map_smul, hq0, zero_add] at e₁
  have e₂ : ((n + 1 : ℕ) : ℂ) • ρ.op 10 h ((ρ.op 7 0 ^ n) (ρ.op 8 0 w)) =
      ρ.op 10 h (ρ.op 11 0 ((ρ.op 7 0 ^ (n + 1)) w)) := by
    rw [← eq_sub_iff_add_eq.mp e₁]
    push_cast
    module
  have h₂ : ((n + 1 : ℕ) : ℂ) • ρ.op 10 h ((ρ.op 7 0 ^ n) (ρ.op 8 0 w)) ∈
      higherRadicalCountClosure ρ w ![0, n, 1] := by
    rw [e₂]
    exact h₁
  have hs := (higherRadicalCountClosure ρ w ![0, n, 1]).smul_mem ((n + 1 : ℕ) : ℂ)⁻¹ h₂
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul] at hs

/-- **The level-1 step of Lemma J₂.** For `d₁ ≤ 1`, the middle alphabet current of mode
`h ≥ 1` sends the zero-mode word into `M_{>d}`. -/
theorem adjointSite_middleRadicalShift_mem_higherRadical (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0) (d : Fin 3 → ℕ)
    (hd : d 0 ≤ 1) :
    radicalAlphabetCurrent ρ 1 h ((ρ.op 6 0 ^ d 0) ((ρ.op 7 0 ^ d 1) ((ρ.op 8 0 ^ d 2) w))) ∈
      higherRadicalCountClosure ρ w d := by
  have hx (u : V) : radicalAlphabetCurrent ρ 1 h (ρ.op 6 0 u) =
      ρ.op 6 0 (radicalAlphabetCurrent ρ 1 h u) := by
    have hc := radicalAlphabetCurrent_comm ρ 1 0 h 0 u
    simp only [radicalOp, F, show (1 : Fin 3) ≠ 0 by decide, if_false, zero_smul] at hc
    exact sub_eq_zero.mp hc
  have hz (u : V) : radicalAlphabetCurrent ρ 1 h (ρ.op 8 0 u) =
      ρ.op 8 0 (radicalAlphabetCurrent ρ 1 h u) := by
    have hc := radicalAlphabetCurrent_comm ρ 1 2 h 0 u
    simp only [radicalOp, F, show (1 : Fin 3) ≠ 2 by decide, if_false, zero_smul] at hc
    exact sub_eq_zero.mp hc
  have hy (u : V) : radicalAlphabetCurrent ρ 1 h (ρ.op 7 0 u) =
      ρ.op 7 0 (radicalAlphabetCurrent ρ 1 h u) + ρ.op 7 h u := by
    have hc := radicalAlphabetCurrent_comm ρ 1 1 h 0 u
    simp only [radicalOp, F, ↓reduceIte, one_smul, add_zero] at hc
    exact sub_eq_iff_eq_add'.mp hc
  have hw0 : radicalAlphabetCurrent ρ 1 h w = 0 :=
    radicalAlphabetCurrent_source_zero ρ w 1 B 1 hW 1 h hh
  have hzpow : radicalAlphabetCurrent ρ 1 h ((ρ.op 8 0 ^ d 2) w) = 0 := by
    rw [endomorphism_commute_pow _ _ hz, hw0, map_zero]
  rw [endomorphism_commute_pow _ _ hx]
  rcases Nat.eq_zero_or_pos (d 1) with hd1 | hd1
  · rw [hd1, pow_zero, Module.End.one_apply, hzpow, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨m, hm⟩ : ∃ m, d 1 = m + 1 := ⟨d 1 - 1, by omega⟩
  rw [hm, endomorphism_derivation_pow _ _ _ hy
    (fun u => op_comm_of_zero_bracket ρ bracket_compound_compound h 0 u) m, hzpow, map_zero,
    zero_add, map_smul]
  apply Submodule.smul_mem
  obtain ⟨W, hWdef⟩ : ∃ W, W = (ρ.op 7 0 ^ m) ((ρ.op 8 0 ^ d 2) w) := ⟨_, rfl⟩
  rw [← op_pow_comm_of_zero_bracket ρ bracket_compound_compound h 0 m, ← hWdef]
  have hgW : ρ.op 9 h W = 0 := by
    apply middleLowering_kills_radicalLayer ρ w h hg ![0, m, d 2] rfl W
    rw [hWdef]
    simpa using zeroModeWord_mem_radicalCountLayer ρ w ![0, m, d 2]
  have hyh : ρ.op 7 h W = ρ.op 9 h (ρ.op 6 0 W) - ρ.op 6 0 (ρ.op 9 h W) := by
    rw [op_comm_of_single_bracket ρ bracket_middle_first h 0 W]
    simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd0 | hd0
  · rw [hd0, pow_zero, Module.End.one_apply, hyh, hgW, map_zero, sub_zero]
    have hk : higherRadicalCounts d ⟨1, m, d 2, 0⟩ := by
      dsimp only [higherRadicalCounts]
      omega
    have hxW : ρ.op 6 0 W ∈ higherRadicalCountClosure ρ w d := by
      rw [hWdef]
      simpa using zeroModeWord_mem_higherRadical ρ w d 1 m (d 2) hk
    exact a3LeviClosure_inv ρ _ 3 h hxW
  · rw [hd0, pow_one]
    have hx2 : ρ.op 6 0 (ρ.op 6 0 w) = 0 := lowering_square_of_label_one ρ w _ hW 0 rfl
    have hxx : ρ.op 6 0 (ρ.op 6 0 W) = 0 := by
      rw [hWdef, op_pow_comm_of_zero_bracket ρ bracket_first_compound,
        op_pow_comm_of_zero_bracket ρ bracket_first_compound,
        op_pow_comm_of_zero_bracket ρ bracket_first_highest,
        op_pow_comm_of_zero_bracket ρ bracket_first_highest,
        hx2, map_zero, map_zero]
    have hxy : ρ.op 6 0 (ρ.op 7 h W) = ρ.op 7 h (ρ.op 6 0 W) :=
      op_comm_of_zero_bracket ρ bracket_first_compound 0 h W
    have hxg : ρ.op 6 0 (ρ.op 9 h (ρ.op 6 0 W)) =
        ρ.op 9 h (ρ.op 6 0 (ρ.op 6 0 W)) - ρ.op 7 h (ρ.op 6 0 W) := by
      rw [op_comm_of_single_bracket ρ bracket_middle_first h 0 (ρ.op 6 0 W)]
      simp
    have e := congrArg (ρ.op 6 0) hyh
    rw [map_sub, hgW, map_zero, map_zero, sub_zero, hxg, hxx, map_zero, zero_sub,
      ← hxy] at e
    have h₂ : (2 : ℂ) • ρ.op 6 0 (ρ.op 7 h W) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [e]
      simp
    rw [(smul_eq_zero.mp h₂).resolve_left (by norm_num)]
    exact Submodule.zero_mem _

variable (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **Theorem J₃¹(h)**, the single vector. On a block over `d = (1, n, 1)`, the evaluation of
`p_h(g₂)` vanishes. -/
theorem adjointSite_compoundAlphabet_marked_zero (h : ℕ) (hh : 0 < h) (hg : ρ.op 9 h w = 0)
    (n e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂)) :
    mixedSecondLeviEvaluation ρ w 1 B hW ![1, n, 1] e₁ e₂ hv
      (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂)) 4
        (mixedLengths (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂) 4) h) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
  apply Subtype.ext
  have hrep := compoundAlphabetOperator_realizes ρ w ![1, n, 1] B hW e₁ e₂ hv s 1 _
    (mixedSecondLeviEvaluation_one_val ρ w 1 B hW ![1, n, 1] e₁ e₂ hv).symm
  rw [mul_one] at hrep
  rw [← hrep, ZeroMemClass.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    endomorphism_commute_pow _ _ (compoundAlphabetOperator_middle ρ w 1 B 1 hW ![1, n, 1]
      (s + 1) 0) e₁]
  have hamb : compoundAlphabetOperator ρ w 1 B 1 hW ![1, n, 1] (s + 1)
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1] 1) = 0 := by
    rw [compoundAlphabetOperator_ambient ρ w 1 B 1 hW ![1, n, 1] (s + 1) (by omega),
      radicalGrassmannianPowerSum_outer_eq_zero B ![1, n, 1] 2 (Or.inr ⟨rfl, by simp⟩) (s + 1)
        (by omega), zero_mul, map_zero]
  cases e₂ with
  | zero =>
    rw [pow_zero, Module.End.one_apply, hamb, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    rw [endomorphism_derivation_pow _ _ _
      (compoundAlphabetOperator_compound ρ w 1 B 1 hW ![1, n, 1] (s + 1) 0)
      (fun u => LinearMap.congr_fun (leviCompound_compound_commute
        (radicalCountQuotCurrent ρ w ![1, n, 1]) (s + 1 + 0) 0).eq u) m,
      hamb, map_zero, zero_add, map_smul, add_zero]
    apply Submodule.smul_mem
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      simp [MixedValid, mixedLabelBlockParams, mixedQ] at hv
      omega⟩
    have hβ : radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n' + 1, 1] 1 =
        (higherRadicalCountClosure ρ w ![1, n' + 1, 1]).mkQ
          (ρ.op 6 0 ((ρ.op 7 0 ^ (n' + 1)) (ρ.op 8 0 w))) := by
      rw [radicalGrassmannianAmbientEvaluation_one]
      simp
    have hJ := adjointSite_highModeCompound_mem_higherSecondLevi ρ w B (s + 1) hW hh hg n' e₁
    have hM := higherSecondLeviCountClosure_compoundPower_le _ _ e₁ 1 m hJ
    have hgq := congrArg (fun T : Module.End ℂ _ => T
      ((radicalCountQuotCurrent ρ w ![1, n' + 1, 1]).op 5 (s + 1)
        ((higherRadicalCountClosure ρ w ![1, n' + 1, 1]).mkQ
          (ρ.op 6 0 ((ρ.op 7 0 ^ (n' + 1)) (ρ.op 8 0 w))))))
      ((leviMiddle_compound_commute (radicalCountQuotCurrent ρ w ![1, n' + 1, 1]) 0 0).pow_pow
        e₁ m).eq
    simp only [Module.End.mul_apply] at hgq
    rw [hβ, hgq, ← leviCompound_middlePower_comm, show m + 1 = 1 + m by omega]
    exact hM

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **Lemma J₃⁰**, the single vector. On a block over `d = (0, n, 1)`, the evaluation of
`p_h(g₂)` vanishes. -/
theorem adjointSite_compoundAlphabet_unmarked_zero (h : ℕ) (hh : 0 < h) (hg : ρ.op 9 h w = 0)
    (n e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂)) :
    mixedSecondLeviEvaluation ρ w 1 B hW ![0, n, 1] e₁ e₂ hv
      (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂)) 4
        (mixedLengths (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂) 4) h) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
  apply Subtype.ext
  have hrep := compoundAlphabetOperator_realizes ρ w ![0, n, 1] B hW e₁ e₂ hv s 1 _
    (mixedSecondLeviEvaluation_one_val ρ w 1 B hW ![0, n, 1] e₁ e₂ hv).symm
  rw [mul_one] at hrep
  rw [← hrep, ZeroMemClass.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    endomorphism_commute_pow _ _ (compoundAlphabetOperator_middle ρ w 1 B 1 hW ![0, n, 1]
      (s + 1) 0) e₁]
  have hamb : compoundAlphabetOperator ρ w 1 B 1 hW ![0, n, 1] (s + 1)
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, n, 1] 1) = 0 := by
    rw [compoundAlphabetOperator_ambient ρ w 1 B 1 hW ![0, n, 1] (s + 1) (by omega),
      radicalGrassmannianPowerSum_outer_eq_zero B ![0, n, 1] 2 (Or.inr ⟨rfl, by simp⟩) (s + 1)
        (by omega), zero_mul, map_zero]
  cases e₂ with
  | zero =>
    rw [pow_zero, Module.End.one_apply, hamb, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    rw [endomorphism_derivation_pow _ _ _
      (compoundAlphabetOperator_compound ρ w 1 B 1 hW ![0, n, 1] (s + 1) 0)
      (fun u => LinearMap.congr_fun (leviCompound_compound_commute
        (radicalCountQuotCurrent ρ w ![0, n, 1]) (s + 1 + 0) 0).eq u) m,
      hamb, map_zero, zero_add, map_smul, add_zero]
    have hq : (radicalCountQuotCurrent ρ w ![0, n, 1]).op 5 (s + 1)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, n, 1] 1) = 0 := by
      rw [radicalGrassmannianAmbientEvaluation_one]
      have hw : (ρ.op 6 0 ^ (![0, n, 1] : Fin 3 → ℕ) 0)
          ((ρ.op 7 0 ^ (![0, n, 1] : Fin 3 → ℕ) 1) ((ρ.op 8 0 ^ (![0, n, 1] : Fin 3 → ℕ) 2) w)) =
          (ρ.op 7 0 ^ n) (ρ.op 8 0 w) := by
        simp
      rw [hw]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (adjointSite_compoundHighMode_mem_higherRadical ρ w B (s + 1) hW hg n)
    rw [hq, map_zero, map_zero, smul_zero]
    exact Submodule.zero_mem _

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **Lemma J₂**, the single vector. On every block, the evaluation of `p_h(x₂)` vanishes. -/
theorem adjointSite_middleRadical_mode_zero (h : ℕ) (hh : 0 < h) (hg : ρ.op 9 h w = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) :
    mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
      (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 1
        (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 1) h) = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
  have hd : d 0 ≤ 1 ∧ d 2 ≤ 1 := by
    simp [MixedValid, mixedLabelBlockParams] at hv
    omega
  apply Subtype.ext
  have hrep := middleRadicalOperator_realizes ρ w d B hW e₁ e₂ hv s 1 _
    (mixedSecondLeviEvaluation_one_val ρ w 1 B hW d e₁ e₂ hv).symm
  rw [mul_one] at hrep
  rw [← hrep, ZeroMemClass.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    endomorphism_commute_pow _ _ (middleRadicalOperator_middle ρ w 1 B 1 hW d (s + 1) 0) e₁,
    endomorphism_commute_pow _ _ (middleRadicalOperator_compound ρ w 1 B 1 hW d (s + 1) 0) e₂,
    middleRadicalOperator_ambient ρ w 1 B 1 hW d (s + 1) (by omega),
    radicalGrassmannianPowerSum_outer_eq_zero B d 0 (Or.inl ⟨rfl, hd.1⟩) (s + 1) (by omega),
    radicalGrassmannianPowerSum_outer_eq_zero B d 2 (Or.inr ⟨rfl, hd.2⟩) (s + 1) (by omega),
    zero_add, add_zero]
  have hX : radicalAlphabetQuotCurrent ρ w 1 B 1 hW d 1 (s + 1)
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d 1) =
      radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d
        (radicalGrassmannianPowerSum 1 B 1 d 1 (s + 1) * 1) :=
    radicalGrassmannianEvaluation_powerSum ρ w 1 B 1 hW d 1 (s + 1) (by omega) 1
  have h0 : (higherRadicalCountClosure ρ w d).mkQ (radicalAlphabetCurrent ρ 1 (s + 1)
      ((ρ.op 6 0 ^ d 0) ((ρ.op 7 0 ^ d 1) ((ρ.op 8 0 ^ d 2) w)))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr
      (adjointSite_middleRadicalShift_mem_higherRadical ρ w B (s + 1) (by omega) hW hg d hd.1)
  rw [← hX, radicalGrassmannianAmbientEvaluation_one, radicalAlphabetQuotCurrent_mk, h0,
    map_zero, map_zero]
  exact Submodule.zero_mem _

set_option maxHeartbeats 400000 in
-- The case analysis unfolds the six summands of the kernel ideal over a quotient ring.
set_option synthInstance.maxHeartbeats 100000 in
/-- **Corollary K.** On every block of a module with the relations of `M(B, h)`, `h ≥ 1`, the
ring kernel `I_J(h)` lies in the kernel of the second Levi multiplicity evaluation. -/
theorem adjointSite_kernelIdeal_le_kernel (h : ℕ) (hh : 0 < h)
    (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0) (hg : ρ.op 9 h w = 0)
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) :
    (adjointSiteKernelIdeal (mixedLabelBlockParams 1 B d e₁ e₂) h).restrictScalars ℂ ≤
      LinearMap.ker (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv) := by
  obtain ⟨a₀, n, c₀, rfl⟩ : ∃ a₀ n c₀, d = ![a₀, n, c₀] :=
    ⟨d 0, d 1, d 2, by funext i; fin_cases i <;> rfl⟩
  have hd : a₀ ≤ 1 ∧ c₀ ≤ 1 := by
    simp [MixedValid, mixedLabelBlockParams] at hv
    omega
  have htail (i : Fin 5) (L : ℕ) (hL : h + 1 ≤ L) :
      mixedAlphabetModeTailIdeal (mixedLabelBlockParams 1 B ![a₀, n, c₀] e₁ e₂) i L ≤
        evaluationAnnihilator (mixedSecondLeviEvaluation ρ w 1 B hW ![a₀, n, c₀] e₁ e₂ hv) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩ φ
    exact mixedSecondLeviEvaluation_alphabetPowerSum_tail ρ w 1 B (h + 1) ht hW ![a₀, n, c₀]
      e₁ e₂ hv i s (by omega) (by omega) φ
  have hmode (i : Fin 5)
      (h₀ : mixedSecondLeviEvaluation ρ w 1 B hW ![a₀, n, c₀] e₁ e₂ hv
        (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B ![a₀, n, c₀] e₁ e₂))
          i (mixedLengths (mixedLabelBlockParams 1 B ![a₀, n, c₀] e₁ e₂) i) h) = 0) :
      mixedAlphabetModeTailIdeal (mixedLabelBlockParams 1 B ![a₀, n, c₀] e₁ e₂) i h ≤
        evaluationAnnihilator (mixedSecondLeviEvaluation ρ w 1 B hW ![a₀, n, c₀] e₁ e₂ hv) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩ φ
    rcases eq_or_lt_of_le hs with rfl | hs'
    · rw [mul_comm]
      exact adjointSite_evaluation_mul_eq_zero ρ w B hW ![a₀, n, c₀] e₁ e₂ hv _ h₀ φ
    · exact mixedSecondLeviEvaluation_alphabetPowerSum_tail ρ w 1 B (h + 1) ht hW ![a₀, n, c₀]
        e₁ e₂ hv i s hs' (by omega) φ
  have hann : adjointSiteKernelIdeal (mixedLabelBlockParams 1 B ![a₀, n, c₀] e₁ e₂) h ≤
      evaluationAnnihilator (mixedSecondLeviEvaluation ρ w 1 B hW ![a₀, n, c₀] e₁ e₂ hv) := by
    unfold adjointSiteKernelIdeal
    refine sup_le (sup_le (sup_le (sup_le (sup_le (htail 1 _ le_rfl) (htail 3 _ le_rfl))
      (htail 4 _ le_rfl)) (hmode 1 (adjointSite_middleRadical_mode_zero ρ w B hW h hh hg
        ![a₀, n, c₀] e₁ e₂ hv))) ?_) ?_
    · split_ifs with h₁
      · apply hmode 3
        have ha : a₀ = 0 := by simpa [mixedLabelBlockParams] using h₁
        subst ha
        simpa using adjointSite_middleAlphabet_mode_zero ρ w B h hh hW ht hg ![0, n, c₀] rfl
          e₁ e₂ hv 1
      · exact bot_le
    · split_ifs with h₃
      · apply hmode 4
        have hc : c₀ = 1 := by simpa [mixedLabelBlockParams] using h₃
        subst hc
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd.1 with rfl | rfl
        · exact adjointSite_compoundAlphabet_unmarked_zero ρ w B hW h hh hg n e₁ e₂ hv
        · exact adjointSite_compoundAlphabet_marked_zero ρ w B hW h hh hg n e₁ e₂ hv
      · exact bot_le
  exact fun x hx => evaluationAnnihilator_le_kernel _ (hann hx)

end

end VOA.DeligneAudit.SL4T
