import VOA.DeligneAudit.SL4TAdjointSiteSecondLeviMoves

/-!
# The ring kernel at one adjoint site (Corollary K)

Let `v` satisfy the local Weyl relations of weight `(1, B, 1)`, `f₂(h) v = 0` with `h ≥ 1`, and
let every current of mode at least `h + 1` vanish. By Lemma CI(i) the kernel of the second Levi
multiplicity evaluation `π` is an ideal, so each relation below is checked on the single vector
`π(p_h(α))`. Two explicit Cartan operators realize the needed power sums at mode `h`:

* `compoundAlphabetOperator h = E₁₁(h) - h₂(h) - h₃(h)` acts as `p_h(x₃) + p_h(g₂)`; it
  commutes with every `g`-letter and shifts every `q`-letter by `h`;
* `middleRadicalOperator h = 3 E₁₁(h) - 2 h₂(h) - h₃(h)` acts as `p_h(x₁) + p_h(x₂) + p_h(x₃)`;
  it commutes with every `g`- and `q`-letter.

Applied to the zero-mode representative `g^{e₁} q^{e₂} x^{d₁} y^{d₂} z^{d₃} v` of `π(1)`:

* **Theorem J₃¹(h)** (`adjointSite_compoundAlphabet_marked_zero`): on blocks over
  `d = (1, d₂, 1)` the result is `e₂ q^{e₂-1} q(h) g^{e₁} x y^{d₂} z v`, which lies in the higher
  second Levi subspace by Proposition J and Lemma M(ii).
* **Lemma J₃⁰** (`adjointSite_compoundAlphabet_unmarked_zero`): on blocks over `d = (0, d₂, 1)`
  already `q(h) y^{d₂} z v ∈ M_{>d}` (`adjointSite_compoundHighMode_mem_higherRadical`), by
  `z = [F, y]`, `q(h) F v = 0` and the higher key `(0, d₂ + 1, 0)`.
* **Lemma J₂** (`adjointSite_middleRadicalShift_mem_higherRadical`): `p_h(x₂)` shifts one
  `y`-letter to mode `h`, and `y(h) = [g(h), x]` either raises the key (no `x`-letter) or, with
  `x² v = 0`, gives `x y(h) W = 0`.

Together with the existing `[d₁ = 0] J_h(g₁)` term and the global truncation this gives
**Corollary K** (`adjointSite_kernelIdeal_le_kernel`): `I_J(h) ⊆ ker π` on every block.
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- `[q, F] = 0`. -/
theorem bracket_lastPair_last (e : Fin 15) : bracketInt 10 11 e = 0 := by
  fin_cases e <;> decide

/-- `[q, y] = 0`. -/
theorem bracket_lastPair_compound (e : Fin 15) : bracketInt 10 7 e = 0 := by
  fin_cases e <;> decide

/-- `[y, z] = 0`. -/
theorem bracket_compound_highest (e : Fin 15) : bracketInt 7 8 e = 0 := by
  fin_cases e <;> decide

/-- A derivation-type commutation `D Y = Y D + Z`, with `Z` commuting with `Y`, on powers. -/
theorem endomorphism_derivation_pow {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D Y Z : Module.End ℂ W) (hDY : ∀ u, D (Y u) = Y (D u) + Z u)
    (hYZ : ∀ u, Z (Y u) = Y (Z u)) (m : ℕ) (u : W) :
    D ((Y ^ (m + 1)) u) = (Y ^ (m + 1)) (D u) + ((m + 1 : ℕ) : ℂ) • (Y ^ m) (Z u) := by
  have hY (k : ℕ) (v : W) : (Y ^ (k + 1)) v = Y ((Y ^ k) v) := by
    rw [pow_succ', Module.End.mul_apply]
  have hpow (k : ℕ) (v : W) : Z ((Y ^ k) v) = (Y ^ k) (Z v) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [hY, hYZ, ih, ← hY]
  induction m with
  | zero => simp [hDY]
  | succ m ih =>
    rw [hY (m + 1), hDY, ih, map_add, map_smul, hpow, ← hY, ← hY]
    push_cast
    module

/-- An operator commuting with `Y` commutes with its powers. -/
theorem endomorphism_commute_pow {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D Y : Module.End ℂ W) (hDY : ∀ u, D (Y u) = Y (D u)) (m : ℕ) (u : W) :
    D ((Y ^ m) u) = (Y ^ m) (D u) := by
  have hc : Commute D Y := LinearMap.ext hDY
  exact congrArg (fun T : Module.End ℂ W => T u) (hc.pow_right m).eq

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-! ### Zero-mode words -/

/-- The zero-mode word `x^p y^n z^m v` lies in its key layer of degree zero. -/
theorem zeroModeWord_mem_keyLayer (p n m : ℕ) :
    (ρ.op 6 0 ^ p) ((ρ.op 7 0 ^ n) ((ρ.op 8 0 ^ m) w)) ∈ a3KeyLayer ρ w ⟨p, n, m, 0⟩ := by
  have hm := a3_three_mode_mem_key ρ w (List.replicate p 0) (List.replicate n 0)
    (List.replicate m 0)
  simp only [List.length_replicate, List.sum_replicate, smul_zero, add_zero] at hm
  convert hm using 1
  simp [aWord, List.map_replicate, List.prod_replicate, F, Module.End.mul_apply]

/-- A zero-mode word of a strictly higher key lies in the higher first Levi closure. -/
theorem zeroModeWord_mem_higherRadical (d : Fin 3 → ℕ) (p n m : ℕ)
    (hk : higherRadicalCounts d ⟨p, n, m, 0⟩) :
    (ρ.op 6 0 ^ p) ((ρ.op 7 0 ^ n) ((ρ.op 8 0 ^ m) w)) ∈ higherRadicalCountClosure ρ w d :=
  a3LeviClosure_contains ρ _ (Submodule.mem_iSup_of_mem ⟨p, n, m, 0⟩
    (Submodule.mem_iSup_of_mem hk (zeroModeWord_mem_keyLayer ρ w p n m)))

/-- The zero-mode word lies in its merged radical count layer. -/
theorem zeroModeWord_mem_radicalCountLayer (d : Fin 3 → ℕ) :
    (ρ.op 6 0 ^ d 0) ((ρ.op 7 0 ^ d 1) ((ρ.op 8 0 ^ d 2) w)) ∈ radicalCountLayer ρ w d :=
  Submodule.mem_iSup_of_mem 0 (zeroModeWord_mem_keyLayer ρ w (d 0) (d 1) (d 2))

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget.
/-- The unit of the Grassmannian source evaluates to the zero-mode word. -/
theorem radicalGrassmannianAmbientEvaluation_one (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ) :
    radicalGrassmannianAmbientEvaluation ρ w a b c h d 1 =
      (higherRadicalCountClosure ρ w d).mkQ
        ((ρ.op 6 0 ^ d 0) ((ρ.op 7 0 ^ d 1) ((ρ.op 8 0 ^ d 2) w))) := by
  change (radicalRelationQuotientEvaluation ρ w a b c h d
    (radicalGrassmannianQuotientMap ρ w a b c h d 1)).val = _
  rw [map_one, ← map_one (Ideal.Quotient.mk (radicalMultiplicityRelationIdeal ρ w a b c h d)),
    radicalRelationQuotientEvaluation_mk]
  change (higherRadicalCountClosure ρ w d).mkQ (radicalModeEvaluation ρ w d
    ((1 : radicalPowerSumAlgebra d) : RadicalModePolynomial d)) = _
  rw [OneMemClass.coe_one, ← MvPolynomial.C_1, MvPolynomial.C_apply,
    radicalModeEvaluation_monomial, one_smul]
  congr 1
  simp [radicalModeWord, aWord, List.map_replicate, List.prod_replicate, F,
    Module.End.mul_apply]

/-! ### The second Levi representative of `π(1)` -/

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- A source representative computes the second Levi multiplicity evaluation. -/
theorem mixedSecondLeviEvaluation_val_of_source (a b : ℕ)
    (hW : LocalWeylRel ρ w (weightABC a b a)) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂))
    (φ : MixedRing (mixedLabelBlockParams a b d e₁ e₂))
    (P : secondLeviSymmetricModes (B := RadicalGrassmannianRing a b a d) e₁ e₂)
    (hP : Ideal.Quotient.mk _ P = mixedToRadicalRelative a b d e₁ e₂ hv φ) :
    (mixedSecondLeviEvaluation ρ w a b hW d e₁ e₂ hv φ).val =
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b a hW d) e₁ e₂).mkQ
        (secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b a hW d) e₁ e₂ P.val) := by
  change (radicalSecondLeviRelativeEvaluation ρ w a b a hW d e₁ e₂
    (mixedLabelBlockParams_dominant a b d e₁ e₂ hv)
    (mixedToRadicalRelative a b d e₁ e₂ hv φ)).val = _
  rw [← hP]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- `π(1)` is represented by the zero-mode word `g^{e₁} q^{e₂} β(1)`. -/
theorem mixedSecondLeviEvaluation_one_val (a b : ℕ)
    (hW : LocalWeylRel ρ w (weightABC a b a)) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) :
    (mixedSecondLeviEvaluation ρ w a b hW d e₁ e₂ hv 1).val =
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b a hW d) e₁ e₂).mkQ
        (((radicalCountQuotCurrent ρ w d).op 3 0 ^ e₁)
          (((radicalCountQuotCurrent ρ w d).op 5 0 ^ e₂)
            (radicalGrassmannianAmbientEvaluation ρ w a b a hW d 1))) := by
  rw [mixedSecondLeviEvaluation_val_of_source ρ w a b hW d e₁ e₂ hv 1 1
    (by rw [map_one, map_one])]
  congr 1
  rw [OneMemClass.coe_one, ← MvPolynomial.C_1, MvPolynomial.C_apply, secondLeviModeEvaluation,
    positionModeEvaluation_monomial, secondLeviPositionProduct]
  simp [List.map_replicate, List.prod_replicate, Module.End.mul_apply]

/-! ### Two explicit Cartan operators -/

/-- `[y, y] = 0`. -/
theorem bracket_compound_compound (e : Fin 15) : bracketInt 7 7 e = 0 := by
  fin_cases e <;> decide

variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ)

/-- The Cartan operator `E₁₁(s) - h₂(s) - h₃(s)`; it acts as `p_s(x₃) + p_s(g₂)`. -/
def compoundAlphabetOperator (s : ℕ) : Module.End ℂ (V ⧸ higherRadicalCountClosure ρ w d) :=
  radicalAlphabetQuotCurrent ρ w a b c h d 0 s - (radicalCountQuotCurrent ρ w d).op 6 s -
    (radicalCountQuotCurrent ρ w d).op 7 s

/-- The Cartan operator `3 E₁₁(s) - 2 h₂(s) - h₃(s)`; it acts as `p_s(x₁) + p_s(x₂) + p_s(x₃)`. -/
def middleRadicalOperator (s : ℕ) : Module.End ℂ (V ⧸ higherRadicalCountClosure ρ w d) :=
  (3 : ℂ) • radicalAlphabetQuotCurrent ρ w a b c h d 0 s -
    (2 : ℂ) • (radicalCountQuotCurrent ρ w d).op 6 s - (radicalCountQuotCurrent ρ w d).op 7 s

/-- The weights of the two Levi Cartan currents on `g` and on `q`. -/
theorem leviCartan_secondLowering_comm {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (s n : ℕ) (x : W) :
    Q.op 6 s (Q.op 3 n x) = (-2 : ℂ) • Q.op 3 (s + n) x + Q.op 3 n (Q.op 6 s x) ∧
      Q.op 7 s (Q.op 3 n x) = (1 : ℂ) • Q.op 3 (s + n) x + Q.op 3 n (Q.op 7 s x) ∧
        Q.op 6 s (Q.op 5 n x) = (-1 : ℂ) • Q.op 5 (s + n) x + Q.op 5 n (Q.op 6 s x) ∧
          Q.op 7 s (Q.op 5 n x) = (-1 : ℂ) • Q.op 5 (s + n) x + Q.op 5 n (Q.op 7 s x) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← sub_eq_iff_eq_add, Q.comm] <;>
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]

theorem outerAlphabetLeviWeight_middle : (outerAlphabetLeviWeight 3 : ℂ) = -1 := by
  simp [outerAlphabetLeviWeight]

theorem outerAlphabetLeviWeight_compound : (outerAlphabetLeviWeight 5 : ℂ) = -1 := by
  simp [outerAlphabetLeviWeight]

/-- `E₁₁ - h₂ - h₃` commutes with every `g`-letter. -/
theorem compoundAlphabetOperator_middle (s n : ℕ) (x : V ⧸ higherRadicalCountClosure ρ w d) :
    compoundAlphabetOperator ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 3 n x) =
      (radicalCountQuotCurrent ρ w d).op 3 n (compoundAlphabetOperator ρ w a b c h d s x) := by
  obtain ⟨h₆, h₇, -, -⟩ := leviCartan_secondLowering_comm (radicalCountQuotCurrent ρ w d) s n x
  simp only [compoundAlphabetOperator, LinearMap.sub_apply, map_sub]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h₆, h₇, outerAlphabetLeviWeight_middle]
  module

/-- `E₁₁ - h₂ - h₃` shifts every `q`-letter: `[H(s), q(n)] = q(s + n)`. -/
theorem compoundAlphabetOperator_compound (s n : ℕ) (x : V ⧸ higherRadicalCountClosure ρ w d) :
    compoundAlphabetOperator ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 5 n x) =
      (radicalCountQuotCurrent ρ w d).op 5 n (compoundAlphabetOperator ρ w a b c h d s x) +
        (radicalCountQuotCurrent ρ w d).op 5 (s + n) x := by
  obtain ⟨-, -, h₆, h₇⟩ := leviCartan_secondLowering_comm (radicalCountQuotCurrent ρ w d) s n x
  simp only [compoundAlphabetOperator, LinearMap.sub_apply, map_sub]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h₆, h₇, outerAlphabetLeviWeight_compound]
  module

/-- `3 E₁₁ - 2 h₂ - h₃` commutes with every `g`-letter. -/
theorem middleRadicalOperator_middle (s n : ℕ) (x : V ⧸ higherRadicalCountClosure ρ w d) :
    middleRadicalOperator ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 3 n x) =
      (radicalCountQuotCurrent ρ w d).op 3 n (middleRadicalOperator ρ w a b c h d s x) := by
  obtain ⟨h₆, h₇, -, -⟩ := leviCartan_secondLowering_comm (radicalCountQuotCurrent ρ w d) s n x
  simp only [middleRadicalOperator, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h₆, h₇, outerAlphabetLeviWeight_middle]
  module

/-- `3 E₁₁ - 2 h₂ - h₃` commutes with every `q`-letter. -/
theorem middleRadicalOperator_compound (s n : ℕ) (x : V ⧸ higherRadicalCountClosure ρ w d) :
    middleRadicalOperator ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 5 n x) =
      (radicalCountQuotCurrent ρ w d).op 5 n (middleRadicalOperator ρ w a b c h d s x) := by
  obtain ⟨-, -, h₆, h₇⟩ := leviCartan_secondLowering_comm (radicalCountQuotCurrent ρ w d) s n x
  simp only [middleRadicalOperator, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h₆, h₇, outerAlphabetLeviWeight_compound]
  module

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget.
/-- On the first Levi multiplicity, `E₁₁ - h₂ - h₃` is multiplication by `p_s(x₃)`. -/
theorem compoundAlphabetOperator_ambient (s : ℕ) (hs : 0 < s)
    (φ : RadicalGrassmannianRing a b c d) :
    compoundAlphabetOperator ρ w a b c h d s
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) =
      radicalGrassmannianAmbientEvaluation ρ w a b c h d
        (radicalGrassmannianPowerSum a b c d 2 s * φ) := by
  have h₆ := radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0 s hs φ
  have h₇ := radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1 s hs φ
  simp only [↓reduceIte] at h₆
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at h₇
  simp only [compoundAlphabetOperator, LinearMap.sub_apply]
  rw [radicalAlphabetQuotCurrent_outer_ambient ρ w a b c h d s hs, h₆, h₇, ← map_sub, ← map_sub]
  congr 1
  simp only [radicalLeviPowerSum, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  ring

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget.
/-- On the first Levi multiplicity, `3 E₁₁ - 2 h₂ - h₃` is multiplication by
`p_s(x₁) + p_s(x₂) + p_s(x₃)`. -/
theorem middleRadicalOperator_ambient (s : ℕ) (hs : 0 < s)
    (φ : RadicalGrassmannianRing a b c d) :
    middleRadicalOperator ρ w a b c h d s (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) =
      radicalGrassmannianAmbientEvaluation ρ w a b c h d
        ((radicalGrassmannianPowerSum a b c d 0 s + radicalGrassmannianPowerSum a b c d 1 s +
          radicalGrassmannianPowerSum a b c d 2 s) * φ) := by
  have h₆ := radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0 s hs φ
  have h₇ := radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1 s hs φ
  simp only [↓reduceIte] at h₆
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at h₇
  simp only [middleRadicalOperator, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [radicalAlphabetQuotCurrent_outer_ambient ρ w a b c h d s hs, h₆, h₇, ← map_smul,
    ← map_smul, ← map_sub, ← map_sub]
  congr 1
  simp only [radicalLeviPowerSum, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, sub_mul,
    add_mul]
  module

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The middle Levi Cartan current on labelled-mode words. -/
theorem secondLeviModeEvaluation_middleCartan (e₁ e₂ s : ℕ) (hs : 0 < s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d)) :
    (radicalCountQuotCurrent ρ w d).op 6 s
        (secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P) =
      secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
        ((MvPolynomial.C (radicalGrassmannianPowerSum a b c d 0 s) -
          MvPolynomial.C (radicalGrassmannianPowerSum a b c d 1 s) -
            (2 : ℂ) • secondLeviModePowerSum e₁ e₂ 0 s -
              secondLeviModePowerSum e₁ e₂ 1 s) * P) := by
  have hc := secondLeviModeEvaluation_cartan (radicalCountQuotCurrent ρ w d)
    (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ 0 s _
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0 s hs) P
  simp only [↓reduceIte] at hc
  rw [hc]
  congr 2
  simp only [radicalLeviPowerSum, ↓reduceIte, map_sub]
  module

set_option synthInstance.maxHeartbeats 100000 in
-- The coefficient algebra is a tensor product of three Grassmannian quotient rings.
/-- The last Levi Cartan current on labelled-mode words. -/
theorem secondLeviModeEvaluation_lastCartan (e₁ e₂ s : ℕ) (hs : 0 < s)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing a b c d)) :
    (radicalCountQuotCurrent ρ w d).op 7 s
        (secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ P) =
      secondLeviModeEvaluation (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂
        ((MvPolynomial.C (radicalGrassmannianPowerSum a b c d 1 s) -
          MvPolynomial.C (radicalGrassmannianPowerSum a b c d 2 s) +
            secondLeviModePowerSum e₁ e₂ 0 s - secondLeviModePowerSum e₁ e₂ 1 s) * P) := by
  have hc := secondLeviModeEvaluation_cartan (radicalCountQuotCurrent ρ w d)
    (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ 1 s _
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1 s hs) P
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at hc
  rw [hc]
  congr 2
  simp only [radicalLeviPowerSum, show (1 : Fin 2) ≠ 0 by decide, if_false, map_sub]
  module

/-- `[q(r), q(s)] = 0` in the rank-two Levi. -/
theorem leviCompound_compound_commute {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (r s : ℕ) :
    Commute (Q.op 5 r) (Q.op 5 s) := by
  apply LinearMap.ext
  intro X
  have hc : Q.op 5 r (Q.op 5 s X) - Q.op 5 s (Q.op 5 r X) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 5 5 r s X
  exact sub_eq_zero.mp hc

/-! ### Realization at one adjoint site -/

variable (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- `E₁₁(s) - h₂(s) - h₃(s)` realizes multiplication by `p_s(g₂)` at outer labels one. -/
theorem compoundAlphabetOperator_realizes (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) (s : ℕ)
    (φ : MixedRing (mixedLabelBlockParams 1 B d e₁ e₂))
    (x : V ⧸ higherRadicalCountClosure ρ w d)
    (hx : (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ x =
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ).val) :
    (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ
        (compoundAlphabetOperator ρ w 1 B 1 hW d (s + 1) x) =
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
        (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 4
          (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 4) (s + 1) * φ)).val := by
  refine (mixedSecondLeviEvaluation_alphabetCombination ρ w 1 B hW d e₁ e₂ hv
    ![0, 0, 1, 0, 1] s _ ?_ ?_ φ x hx).trans ?_
  · intro P
    simp only [compoundAlphabetOperator, LinearMap.sub_apply]
    rw [radicalAlphabetQuotCurrent_outer_secondLeviModeEvaluation ρ w 1 B 1 hW d e₁ e₂ (s + 1)
      (by omega), secondLeviModeEvaluation_middleCartan ρ w 1 B 1 hW d e₁ e₂ (s + 1) (by omega),
      secondLeviModeEvaluation_lastCartan ρ w 1 B 1 hW d e₁ e₂ (s + 1) (by omega),
      ← map_sub, ← map_sub, ← sub_mul, ← sub_mul]
    congr 2
    simp [secondLeviAlphabetSourceCombination, Fin.sum_univ_five, secondLeviAlphabetSource]
    module
  · intro y hy
    rw [Submodule.mem_comap]
    simp only [compoundAlphabetOperator, LinearMap.sub_apply]
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · exact higherSecondLeviCountClosure_outerAlphabet ρ w 1 B 1 hW d e₁ e₂ (s + 1)
          (by omega) hy
      · exact a2LeviClosure_inv _ _ 6 (s + 1) (by simp [a2Levi]) hy
    · exact a2LeviClosure_inv _ _ 7 (s + 1) (by simp [a2Levi]) hy
  · have hx₃ := mixedAlphabetPowerSum_outer_label_one B d e₁ e₂ hv 2 (Or.inr rfl) (s + 1)
      (by omega)
    simp [mixedAlphabetCombination, Fin.sum_univ_five, hx₃]

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- `3 E₁₁(s) - 2 h₂(s) - h₃(s)` realizes multiplication by `p_s(x₂)` at outer labels one. -/
theorem middleRadicalOperator_realizes (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) (s : ℕ)
    (φ : MixedRing (mixedLabelBlockParams 1 B d e₁ e₂))
    (x : V ⧸ higherRadicalCountClosure ρ w d)
    (hx : (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ x =
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv φ).val) :
    (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ
        (middleRadicalOperator ρ w 1 B 1 hW d (s + 1) x) =
      (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
        (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 1
          (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 1) (s + 1) * φ)).val := by
  refine (mixedSecondLeviEvaluation_alphabetCombination ρ w 1 B hW d e₁ e₂ hv
    ![1, 1, 1, 0, 0] s _ ?_ ?_ φ x hx).trans ?_
  · intro P
    simp only [middleRadicalOperator, LinearMap.sub_apply, LinearMap.smul_apply]
    rw [radicalAlphabetQuotCurrent_outer_secondLeviModeEvaluation ρ w 1 B 1 hW d e₁ e₂ (s + 1)
      (by omega), secondLeviModeEvaluation_middleCartan ρ w 1 B 1 hW d e₁ e₂ (s + 1) (by omega),
      secondLeviModeEvaluation_lastCartan ρ w 1 B 1 hW d e₁ e₂ (s + 1) (by omega),
      ← map_smul, ← map_smul, ← map_sub, ← map_sub, ← smul_mul_assoc, ← smul_mul_assoc,
      ← sub_mul, ← sub_mul]
    congr 2
    simp [secondLeviAlphabetSourceCombination, Fin.sum_univ_five, secondLeviAlphabetSource]
    module
  · intro y hy
    rw [Submodule.mem_comap]
    simp only [middleRadicalOperator, LinearMap.sub_apply, LinearMap.smul_apply]
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (higherSecondLeviCountClosure_outerAlphabet ρ w 1 B 1 hW
          d e₁ e₂ (s + 1) (by omega) hy)
      · exact Submodule.smul_mem _ _ (a2LeviClosure_inv _ _ 6 (s + 1) (by simp [a2Levi]) hy)
    · exact a2LeviClosure_inv _ _ 7 (s + 1) (by simp [a2Levi]) hy
  · have hx₁ := mixedAlphabetPowerSum_outer_label_one B d e₁ e₂ hv 0 (Or.inl rfl) (s + 1)
      (by omega)
    have hx₃ := mixedAlphabetPowerSum_outer_label_one B d e₁ e₂ hv 2 (Or.inr rfl) (s + 1)
      (by omega)
    simp [mixedAlphabetCombination, Fin.sum_univ_five, hx₁, hx₃]

end

end VOA.DeligneAudit.SL4T
