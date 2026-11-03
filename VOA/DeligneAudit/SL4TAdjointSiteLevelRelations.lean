import VOA.DeligneAudit.SL4TAdjointSiteKernelIdeal

/-!
# The mode-`h` level relations at one adjoint site

Let `v` satisfy the local Weyl relations of weight `(1, B, 1)`, `f₂(h) v = 0` with `h ≥ 1`, and
let every current of mode at least `h + 1` vanish. Write `F = f₃` and `Φ̄(φ t^h) = F(h) π(φ)`.

**Theorem L₃(h)** (`adjointSite_markedSymbol_lowering_zero`). On every block over `(1, d₂, 1)`,
`F(h) π(a₀ φ) = 0` for all `φ`, where `a₀ = e_{e₁}(g₁)` is the top elementary class of `g₁`.
The representative of `π(a₀)` is `g(1)^{e₁} q^{e₂} x y^{d₂} z v`; `F(h)` commutes with `g(1)`
(the bracket is `q(h + 1) = 0`) and with `q`, and kills the zero-mode top word of the first Levi
quotient by Lemma E.

**Proposition Σ₁(h)** (`adjointSite_unmarked_lowering_zero`). On every block over `(0, d₂, 1)`,
`F(h) π(φ) = 0` for all `φ`. The proof here is elementary and replaces the Weyl-group transport
of Lemma TK: by Lemma T, `F(h) g^m F v = 0` for every `m`; expanding `x^{n+1} g^{m+n+1} F v`
(`x` acts on `g` as a derivation with value `-y`, and `x² v = 0`) gives a nonzero multiple of
`g^m y^n z v` modulo vectors of strictly higher first Levi keys
(`adjointSite_lastHighMode_unmarked_mem`). Since `F(h)` commutes with `x` and `q`, it sends the
zero-mode representative `g^{e₁} q^{e₂} y^{d₂} z v` of `π(1)` into `M_{>d}`.
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- `[F, F] = 0`. -/
theorem bracket_last_last (e : Fin 15) : bracketInt 11 11 e = 0 := by
  fin_cases e <;> decide

/-- `[q, g] = 0`. -/
theorem bracket_lastPair_middle (e : Fin 15) : bracketInt 10 9 e = 0 := by
  fin_cases e <;> decide

/-- `[g, y] = 0`, in the order `(9, 7)` already exists; `[y, g] = 0` here. -/
theorem bracket_compound_middle (e : Fin 15) : bracketInt 7 9 e = 0 := by
  fin_cases e <;> decide

/-- `[F(r), q(s)] = 0` in the rank-two Levi. -/
theorem leviLast_compound_commute {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (r s : ℕ) :
    Commute (Q.op 4 r) (Q.op 5 s) := by
  apply LinearMap.ext
  intro X
  have hc : Q.op 4 r (Q.op 5 s X) - Q.op 5 s (Q.op 4 r X) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 4 5 r s X
  exact sub_eq_zero.mp hc

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Powers of a Levi current on the first Levi quotient lift to the module. -/
theorem radicalCountQuotCurrent_pow_mk (d : Fin 3 → ℕ) (j : Fin 8) (r k : ℕ) (v : V) :
    ((radicalCountQuotCurrent ρ w d).op j r ^ k) ((higherRadicalCountClosure ρ w d).mkQ v) =
      (higherRadicalCountClosure ρ w d).mkQ ((ρ.op (a3LeviColour j) r ^ k) v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    rfl

/-! ### Proposition Σ₁ at level one -/

/-- By Lemma T, `F(h) g^m F v = 0` for every `m`. -/
theorem adjointSite_lastHighMode_middlePower_last_zero (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0) (m : ℕ) :
    ρ.op 11 h ((ρ.op 9 0 ^ m) (ρ.op 11 0 w)) = 0 := by
  have hqF : ρ.op 10 h (ρ.op 11 0 w) = 0 := (adjointSite_transported_relations ρ w B h hW hg).1
  have hFw : ρ.op 11 h w = 0 :=
    simple_mode_zero ρ w (weightABC 1 B 1) hW 2 h (by change 1 ≤ h; omega)
  have hFF : ρ.op 11 h (ρ.op 11 0 w) = 0 := by
    rw [op_comm_of_zero_bracket ρ bracket_last_last h 0, hFw, map_zero]
  cases m with
  | zero => simpa using hFF
  | succ m =>
    rw [endomorphism_derivation_pow (ρ.op 11 h) (ρ.op 9 0) (ρ.op 10 h)
      (fun u => by
        rw [op_comm_of_single_bracket ρ bracket_last_middle h 0 u]
        simp)
      (fun u => op_comm_of_zero_bracket ρ bracket_lastPair_middle h 0 u) m,
      hFF, hqF, map_zero, map_zero, smul_zero, add_zero]

/-- The expansion of `x^{i+1} g^{m+i+1} F v` into `g^m y^{i+1} F v` (with a nonzero
coefficient) and `g^{m+1} y^i x F v`. -/
theorem first_middlePower_last_expansion (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (i : ℕ) : ∀ m : ℕ, ∃ a c : ℂ, a ≠ 0 ∧
      (ρ.op 6 0 ^ (i + 1)) ((ρ.op 9 0 ^ (m + i + 1)) (ρ.op 11 0 w)) =
        a • (ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ (i + 1)) (ρ.op 11 0 w)) +
          c • (ρ.op 9 0 ^ (m + 1)) ((ρ.op 7 0 ^ i) (ρ.op 6 0 (ρ.op 11 0 w))) := by
  have hxg (k : ℕ) (u : V) : ρ.op 6 0 ((ρ.op 9 0 ^ (k + 1)) u) =
      (ρ.op 9 0 ^ (k + 1)) (ρ.op 6 0 u) +
        ((k + 1 : ℕ) : ℂ) • (ρ.op 9 0 ^ k) ((-ρ.op 7 0) u) := by
    apply endomorphism_derivation_pow (ρ.op 6 0) (ρ.op 9 0) (-ρ.op 7 0)
    · intro u
      have hc := op_comm_of_single_bracket ρ bracket_middle_first 0 0 u
      rw [LinearMap.neg_apply, ← sub_eq_add_neg, eq_sub_iff_add_eq, hc]
      simp
    · intro u
      rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg,
        op_comm_of_zero_bracket ρ bracket_compound_middle 0 0 u]
  have hxy (k : ℕ) (u : V) : ρ.op 6 0 ((ρ.op 7 0 ^ k) u) = (ρ.op 7 0 ^ k) (ρ.op 6 0 u) :=
    op_pow_comm_of_zero_bracket ρ bracket_first_compound 0 0 k u
  have hx2 : ρ.op 6 0 (ρ.op 6 0 w) = 0 := lowering_square_of_label_one ρ w _ hW 0 rfl
  have hxxF : ρ.op 6 0 (ρ.op 6 0 (ρ.op 11 0 w)) = 0 := by
    rw [op_comm_of_zero_bracket ρ bracket_first_last 0 0,
      op_comm_of_zero_bracket ρ bracket_first_last 0 0, hx2, map_zero]
  have hy (k : ℕ) (u : V) : ρ.op 7 0 ((ρ.op 7 0 ^ k) u) = (ρ.op 7 0 ^ (k + 1)) u := by
    rw [pow_succ', Module.End.mul_apply]
  induction i with
  | zero =>
    intro m
    refine ⟨-((m + 1 : ℕ) : ℂ), 1, neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero m), ?_⟩
    simp only [zero_add, add_zero, pow_one, pow_zero, Module.End.one_apply]
    rw [hxg]
    simp only [LinearMap.neg_apply, map_neg, smul_neg, one_smul, neg_smul]
    abel
  | succ i ih =>
    intro m
    obtain ⟨a, c, ha, hac⟩ := ih (m + 1)
    refine ⟨-(a * ((m + 1 : ℕ) : ℂ)), a - c * ((m + 2 : ℕ) : ℂ),
      neg_ne_zero.mpr (mul_ne_zero ha (by exact_mod_cast Nat.succ_ne_zero m)), ?_⟩
    have hidx : m + (i + 1) + 1 = m + 1 + i + 1 := by omega
    rw [show ρ.op 6 0 ^ (i + 1 + 1) = ρ.op 6 0 * ρ.op 6 0 ^ (i + 1) from pow_succ' _ _,
      Module.End.mul_apply, hidx, hac, map_add, map_smul, map_smul, hxg, hxg,
      hxy, hxy, hxxF, map_zero, map_zero, zero_add]
    simp only [LinearMap.neg_apply, map_neg, hy, smul_neg, smul_add, smul_smul]
    push_cast
    module

/-- `[z, x] = 0`. -/
theorem bracket_highest_first (e : Fin 15) : bracketInt 8 6 e = 0 := by
  fin_cases e <;> decide

/-- `g(0)`-powers preserve the higher first Levi closure. -/
theorem middlePower_mem_higherRadical (d : Fin 3 → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ higherRadicalCountClosure ρ w d) :
    (ρ.op 9 0 ^ k) x ∈ higherRadicalCountClosure ρ w d := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact a3LeviClosure_inv ρ _ 3 0 ih

/-- `q(0)`-powers preserve the higher first Levi closure. -/
theorem compoundPower_mem_higherRadical (d : Fin 3 → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ higherRadicalCountClosure ρ w d) :
    (ρ.op 10 0 ^ k) x ∈ higherRadicalCountClosure ρ w d := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact a3LeviClosure_inv ρ _ 5 0 ih

/-- `F(h) g(0)^k F(0)` preserves the higher first Levi closure. -/
theorem lastHighMode_middlePower_last_mem (h : ℕ) (d : Fin 3 → ℕ) (u : V)
    (hu : u ∈ higherRadicalCountClosure ρ w d) (k : ℕ) :
    ρ.op 11 h ((ρ.op 9 0 ^ k) (ρ.op 11 0 u)) ∈ higherRadicalCountClosure ρ w d :=
  a3LeviClosure_inv ρ _ 4 h
    (middlePower_mem_higherRadical ρ w d k _ (a3LeviClosure_inv ρ _ 4 0 hu))

/-- The `x`-piece of the expansion lies in the higher first Levi closure at `(0, n, 1)`. -/
theorem lastHighMode_unmarked_firstPiece_mem (h n m : ℕ) :
    ρ.op 11 h ((ρ.op 9 0 ^ (m + 1)) ((ρ.op 7 0 ^ n) (ρ.op 6 0 (ρ.op 11 0 w)))) ∈
      higherRadicalCountClosure ρ w ![0, n, 1] := by
  rw [op_comm_of_zero_bracket ρ bracket_first_last 0 0]
  have hxyw : (ρ.op 7 0 ^ n) (ρ.op 6 0 w) ∈ higherRadicalCountClosure ρ w ![0, n, 1] := by
    have hk : higherRadicalCounts ![0, n, 1] ⟨1, n, 0, 0⟩ := by
      simp [higherRadicalCounts, add_comm]
    have hm := zeroModeWord_mem_higherRadical ρ w ![0, n, 1] 1 n 0 hk
    rw [pow_one, pow_zero, Module.End.one_apply,
      op_pow_comm_of_zero_bracket ρ bracket_first_compound 0 0 n] at hm
    exact hm
  cases n with
  | zero =>
    simpa using lastHighMode_middlePower_last_mem ρ w h _ _ hxyw (m + 1)
  | succ n' =>
    have hxz : (ρ.op 7 0 ^ n') (ρ.op 8 0 (ρ.op 6 0 w)) ∈
        higherRadicalCountClosure ρ w ![0, n' + 1, 1] := by
      have hk : higherRadicalCounts ![0, n' + 1, 1] ⟨1, n', 1, 0⟩ := by
        simp [higherRadicalCounts, add_comm]
      have hm := zeroModeWord_mem_higherRadical ρ w ![0, n' + 1, 1] 1 n' 1 hk
      rw [pow_one, pow_one, op_pow_comm_of_zero_bracket ρ bracket_first_compound 0 0 n',
        op_comm_of_zero_bracket ρ bracket_first_highest 0 0] at hm
      exact hm
    have hx : (ρ.op 7 0 ^ (n' + 1)) (ρ.op 11 0 (ρ.op 6 0 w)) =
        ρ.op 11 0 ((ρ.op 7 0 ^ (n' + 1)) (ρ.op 6 0 w)) -
          ((n' + 1 : ℕ) : ℂ) • (ρ.op 7 0 ^ n') (ρ.op 8 0 (ρ.op 6 0 w)) := by
      rw [last_compoundPower_comm ρ 0 n' (ρ.op 6 0 w)]
      abel
    rw [hx, map_sub, map_sub]
    apply Submodule.sub_mem
    · exact lastHighMode_middlePower_last_mem ρ w h _ _ hxyw (m + 1)
    · rw [map_smul, map_smul]
      exact Submodule.smul_mem _ _ (a3LeviClosure_inv ρ _ 4 h
        (middlePower_mem_higherRadical ρ w _ (m + 1) _ hxz))

/-- **Proposition Σ₁ at level one.** At the key `(0, n, 1)`, `F(h) g^m y^n z v ∈ M_{>(0,n,1)}`
for every `m`. -/
theorem adjointSite_lastHighMode_unmarked_mem (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0) (n m : ℕ) :
    ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) ∈
      higherRadicalCountClosure ρ w ![0, n, 1] := by
  obtain ⟨a, c, ha, hexp⟩ := first_middlePower_last_expansion ρ w B hW n m
  have hzero : ρ.op 11 h ((ρ.op 6 0 ^ (n + 1)) ((ρ.op 9 0 ^ (m + n + 1)) (ρ.op 11 0 w))) = 0 := by
    rw [op_pow_comm_of_zero_bracket ρ bracket_last_first,
      adjointSite_lastHighMode_middlePower_last_zero ρ w B h hh hW hg, map_zero]
  rw [hexp, map_add, map_smul, map_smul] at hzero
  have hyw : (ρ.op 7 0 ^ (n + 1)) w ∈ higherRadicalCountClosure ρ w ![0, n, 1] := by
    have hk : higherRadicalCounts ![0, n, 1] ⟨0, n + 1, 0, 0⟩ := by
      simp [higherRadicalCounts]
    simpa using zeroModeWord_mem_higherRadical ρ w ![0, n, 1] 0 (n + 1) 0 hk
  have hAeq : ρ.op 11 h ((ρ.op 9 0 ^ m) (ρ.op 11 0 ((ρ.op 7 0 ^ (n + 1)) w))) =
      ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ (n + 1)) (ρ.op 11 0 w))) +
        ((n + 1 : ℕ) : ℂ) • ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) := by
    rw [last_compoundPower_comm ρ 0 n w, map_add, map_add, map_smul, map_smul]
  have hA := lastHighMode_middlePower_last_mem ρ w h _ _ hyw m
  rw [hAeq] at hA
  have hC := lastHighMode_unmarked_firstPiece_mem ρ w h n m
  have hsum : (a * ((n + 1 : ℕ) : ℂ)) •
      ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) ∈
        higherRadicalCountClosure ρ w ![0, n, 1] := by
    have he : (a * ((n + 1 : ℕ) : ℂ)) •
        ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) =
        a • (ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ (n + 1)) (ρ.op 11 0 w))) +
          ((n + 1 : ℕ) : ℂ) • ρ.op 11 h ((ρ.op 9 0 ^ m) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w)))) +
        c • ρ.op 11 h ((ρ.op 9 0 ^ (m + 1)) ((ρ.op 7 0 ^ n) (ρ.op 6 0 (ρ.op 11 0 w)))) := by
      rw [smul_add, add_assoc, add_comm _ (c • _), ← add_assoc, hzero, zero_add, smul_smul]
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hA) (Submodule.smul_mem _ _ hC)
  have hne : a * ((n + 1 : ℕ) : ℂ) ≠ 0 := mul_ne_zero ha (by exact_mod_cast Nat.succ_ne_zero n)
  have hs := Submodule.smul_mem _ (a * ((n + 1 : ℕ) : ℂ))⁻¹ hsum
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hs

/-! ### The ring statements -/

/-- `[g, q] = 0`. -/
theorem bracket_middle_lastPair (e : Fin 15) : bracketInt 9 10 e = 0 := by
  fin_cases e <;> decide

/-- The top elementary class of the first lowering alphabet evaluates to the word with every
`g`-letter at mode one. -/
theorem secondLeviModeEvaluation_middleTopElementary {B W : Type} [CommRing B] [Algebra ℂ B]
    [AddCommGroup W] [Module ℂ W] (Q : CurrentModule VOA.AffineSl3.bracketTable W)
    (β : B →ₗ[ℂ] W) (e₁ e₂ : ℕ) :
    secondLeviModeEvaluation Q β e₁ e₂ (rename Sum.inl (esymm (Fin e₁) B e₁)) =
      (Q.op 3 1 ^ e₁) ((Q.op 5 0 ^ e₂) (β 1)) := by
  classical
  have hes : esymm (Fin e₁) B e₁ = monomial (∑ i : Fin e₁, Finsupp.single i 1) 1 := by
    rw [esymm_eq_sum_monomial]
    have hp : (Finset.univ : Finset (Fin e₁)).powersetCard e₁ = {Finset.univ} := by
      have := Finset.powersetCard_self (Finset.univ : Finset (Fin e₁))
      rwa [Finset.card_univ, Fintype.card_fin] at this
    rw [hp, Finset.sum_singleton]
  have h₁ (i : Fin e₁) : (Finsupp.mapDomain Sum.inl (∑ j : Fin e₁, Finsupp.single j 1) :
      SecondLeviModeSlot e₁ e₂ →₀ ℕ) (Sum.inl i) = 1 := by
    rw [Finsupp.mapDomain_apply Sum.inl_injective]
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  have h₂ (j : Fin e₂) : (Finsupp.mapDomain Sum.inl (∑ i : Fin e₁, Finsupp.single i 1) :
      SecondLeviModeSlot e₁ e₂ →₀ ℕ) (Sum.inr j) = 0 := by
    apply Finsupp.mapDomain_notin_range
    simp
  rw [hes, rename_monomial, secondLeviModeEvaluation, positionModeEvaluation_monomial,
    secondLeviPositionProduct]
  simp only [h₁, h₂, List.ofFn_const, List.map_replicate, List.prod_replicate,
    Module.End.mul_apply]

variable (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **Proposition Σ₁(h).** On every block over `(0, n, 1)`, `F(h) π(φ) = 0` for all `φ`. -/
theorem adjointSite_unmarked_lowering_zero (h : ℕ) (hh : 0 < h)
    (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0) (hg : ρ.op 9 h w = 0) (n e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂))
    (φ : MixedRing (mixedLabelBlockParams 1 B ![0, n, 1] e₁ e₂)) :
    secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, n, 1])
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, n, 1]) e₁ e₂ h
        (mixedSecondLeviEvaluation ρ w 1 B hW ![0, n, 1] e₁ e₂ hv φ).val = 0 := by
  suffices h₁ : secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, n, 1])
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, n, 1]) e₁ e₂ h
        (mixedSecondLeviEvaluation ρ w 1 B hW ![0, n, 1] e₁ e₂ hv 1).val = 0 by
    have := adjointSite_lowering_mul_eq_zero ρ w B hW ![0, n, 1] e₁ e₂ hv h ht 1 h₁ φ
    rwa [mul_one] at this
  rw [mixedSecondLeviEvaluation_one_val, radicalGrassmannianAmbientEvaluation_one]
  have hw : (ρ.op 6 0 ^ (![0, n, 1] : Fin 3 → ℕ) 0)
      ((ρ.op 7 0 ^ (![0, n, 1] : Fin 3 → ℕ) 1) ((ρ.op 8 0 ^ (![0, n, 1] : Fin 3 → ℕ) 2) w)) =
      (ρ.op 7 0 ^ n) (ρ.op 8 0 w) := by
    simp
  rw [hw, radicalCountQuotCurrent_pow_mk, radicalCountQuotCurrent_pow_mk]
  change (higherSecondLeviCountClosure _ _ e₁ e₂).mkQ
    ((higherRadicalCountClosure ρ w ![0, n, 1]).mkQ
      (ρ.op 11 h ((ρ.op 9 0 ^ e₁) ((ρ.op 10 0 ^ e₂) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w)))))) = 0
  have hc : Commute (ρ.op 9 0) (ρ.op 10 0) :=
    LinearMap.ext fun u => op_comm_of_zero_bracket ρ bracket_middle_lastPair 0 0 u
  rw [← Module.End.mul_apply (ρ.op 9 0 ^ e₁), (hc.pow_pow e₁ e₂).eq, Module.End.mul_apply,
    op_pow_comm_of_zero_bracket ρ bracket_last_lastPair]
  have hmem : (higherRadicalCountClosure ρ w ![0, n, 1]).mkQ ((ρ.op 10 0 ^ e₂)
      (ρ.op 11 h ((ρ.op 9 0 ^ e₁) ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (compoundPower_mem_higherRadical ρ w _ e₂ _
      (adjointSite_lastHighMode_unmarked_mem ρ w B h hh hW hg n e₁))
  rw [hmem, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **Theorem L₃(h).** On every block over `(1, n, 1)`, `F(h) π(a₀ φ) = 0` for all `φ`, where
`a₀ = e_{e₁}(g₁)`. -/
theorem adjointSite_markedSymbol_lowering_zero (h : ℕ) (hh : 0 < h)
    (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0) (hg : ρ.op 9 h w = 0) (n e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂))
    (φ : MixedRing (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂)) :
    secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![1, n, 1])
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1]) e₁ e₂ h
        (mixedSecondLeviEvaluation ρ w 1 B hW ![1, n, 1] e₁ e₂ hv
          (adjointSiteMarkedSymbol (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂) * φ)).val =
      0 := by
  suffices h₁ : secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![1, n, 1])
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1]) e₁ e₂ h
        (mixedSecondLeviEvaluation ρ w 1 B hW ![1, n, 1] e₁ e₂ hv
          (adjointSiteMarkedSymbol (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂))).val = 0 by
    rw [mul_comm]
    exact adjointSite_lowering_mul_eq_zero ρ w B hW ![1, n, 1] e₁ e₂ hv h ht _ h₁ φ
  have hP : Ideal.Quotient.mk _ (mixedElementaryAlphabet 1 B 1 ![1, n, 1] e₁ e₂ 3
      (elementary e₁)) = mixedToRadicalRelative 1 B ![1, n, 1] e₁ e₂ hv
        (adjointSiteMarkedSymbol (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂)) := by
    have he : (mixedLabelBlockParams 1 B ![1, n, 1] e₁ e₂).e1.toNat = e₁ := by
      simp [mixedLabelBlockParams]
    simp only [adjointSiteMarkedSymbol, he]
    change _ = mixedToRadicalRelative 1 B ![1, n, 1] e₁ e₂ hv (Ideal.Quotient.mk _ _)
    rw [mixedToRadicalRelative_mk, mixedE, mixedElementarySource_alphabet]
  rw [mixedSecondLeviEvaluation_val_of_source ρ w 1 B hW ![1, n, 1] e₁ e₂ hv _ _ hP]
  have hval : (mixedElementaryAlphabet 1 B 1 ![1, n, 1] e₁ e₂ 3 (elementary e₁)).val =
      rename Sum.inl (esymm (Fin e₁) (RadicalGrassmannianRing 1 B 1 ![1, n, 1]) e₁) := by
    change (secondLeviElementaryAlphabet e₁ e₂ 0 (elementary e₁)).val = _
    rw [secondLeviElementaryAlphabet_elementary]
    rfl
  rw [hval, secondLeviModeEvaluation_middleTopElementary]
  change (higherSecondLeviCountClosure _ _ e₁ e₂).mkQ
    ((radicalCountQuotCurrent ρ w ![1, n, 1]).op 4 h
      (((radicalCountQuotCurrent ρ w ![1, n, 1]).op 3 1 ^ e₁)
        (((radicalCountQuotCurrent ρ w ![1, n, 1]).op 5 0 ^ e₂)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1] 1)))) = 0
  have hFg (u : V ⧸ higherRadicalCountClosure ρ w ![1, n, 1]) :
      (radicalCountQuotCurrent ρ w ![1, n, 1]).op 4 h
          ((radicalCountQuotCurrent ρ w ![1, n, 1]).op 3 1 u) =
        (radicalCountQuotCurrent ρ w ![1, n, 1]).op 3 1
          ((radicalCountQuotCurrent ρ w ![1, n, 1]).op 4 h u) := by
    rw [leviLast_middle_comm, radicalCountQuot_truncated ρ w (h + 1) ht _ 5 (h + 1) le_rfl,
      add_zero]
  rw [endomorphism_commute_pow _ _ hFg, endomorphism_commute_pow _ _
    (fun u => LinearMap.congr_fun (leviLast_compound_commute _ h 0).eq u)]
  have hF : (radicalCountQuotCurrent ρ w ![1, n, 1]).op 4 h
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n, 1] 1) = 0 := by
    cases n with
    | zero =>
      rw [radicalGrassmannianAmbientEvaluation_one]
      have hw : (ρ.op 6 0 ^ (![1, 0, 1] : Fin 3 → ℕ) 0)
          ((ρ.op 7 0 ^ (![1, 0, 1] : Fin 3 → ℕ) 1) ((ρ.op 8 0 ^ (![1, 0, 1] : Fin 3 → ℕ) 2) w)) =
          ρ.op 6 0 (ρ.op 8 0 w) := by
        simp
      have hFw : ρ.op 11 h w = 0 :=
        simple_mode_zero ρ w (weightABC 1 B 1) hW 2 h (by change 1 ≤ h; omega)
      rw [hw]
      change (higherRadicalCountClosure ρ w ![1, 0, 1]).mkQ
        (ρ.op 11 h (ρ.op 6 0 (ρ.op 8 0 w))) = 0
      rw [op_comm_of_zero_bracket ρ bracket_last_first, op_comm_of_zero_bracket ρ
        bracket_last_highest, hFw, map_zero, map_zero, map_zero]
    | succ n' =>
      have hβ : radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![1, n' + 1, 1] 1 =
          (higherRadicalCountClosure ρ w ![1, n' + 1, 1]).mkQ
            (ρ.op 6 0 ((ρ.op 7 0 ^ (n' + 1)) (ρ.op 8 0 w))) := by
        rw [radicalGrassmannianAmbientEvaluation_one]
        simp
      rw [hβ]
      exact adjointSite_topWord_lastLowering_zero ρ w B h hW hh hg n'
  rw [hF, map_zero, map_zero, map_zero]

end

end VOA.DeligneAudit.SL4T
