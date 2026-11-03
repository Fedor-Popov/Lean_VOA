/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.AdamovicSymbolDescent

/-!
# Well-definedness of the Adamović word symbols in corrected degree one

The first nontrivial case of `WordSymbolDescends`. The corrected degree-one piece of
`L_{-4/3}(sl₂)` is spanned by the vacuum and the one-letter words `a_{-n-1}|0⟩`, `L_{-n-2}|0⟩`.
Using the canonical invariant form, each one-letter word `ℓ` has a dual partner `ℓ*`
(`e ↔ f`, `h ↔ h`, `T ↔ T`) whose pairing with the one-letter words is diagonal:

* `(a*_{-d}|0⟩ | b_{-d}|0⟩) = -d k κ(a*, b)`;
* `(L_{-d}|0⟩ | L_{-d}|0⟩) = (d³ - d) c / 12`, with `c = -6` at `k = -4/3`;
* mixed current/stress pairings vanish (`[J_d, L_{-d}] = d J_0` kills the vacuum).

At `k = -4/3` all diagonal values are nonzero, so the vacuum and the one-letter classes are
linearly independent in the *simple* quotient (the form descends to it), and the symbol map is
defined on a basis.

* `letterPair` — the pairing table, at every noncritical level;
* `degreeOne_linearIndependent` — independence in `L_{-4/3}(sl₂)`;
* `wordSymbolDescends_one : WordSymbolDescends 1` — **proved outright**;
* `jetLeadingSymbol_one : JetLeadingSymbol 1` — the degree-one leading-symbol map, proved;
* `leeYang_gradedUnitary_of_affine_wordSymbols_two` — the endpoint with well-definedness
  assumed only in corrected degrees `r ≥ 2`.

Everything is proved outright.
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge VOA.LeeYangTransferAssembly Sl2CosetConcrete
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity MvPolynomial

noncomputable section

section Pairing

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The dual colour: `e ↔ f`, `h ↔ h`. -/
def dualIdx : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 0
  | 2 => 2

/-- The dual letter. -/
def dualLetter : Generator × ℕ → Generator × ℕ
  | (.current a, n) => (.current (dualIdx a), n)
  | (.sugawara, n) => (.sugawara, n)

theorem letterWt_dualLetter (l : Generator × ℕ) : letterWt (dualLetter l) = letterWt l := by
  obtain ⟨g, n⟩ := l
  cases g <;> rfl

/-- The diagonal pairing values. -/
def pairVal : Generator × ℕ → ℂ
  | (.current a, n) => -((n : ℂ) + 1) * k * kappa (dualIdx a) a
  | (.sugawara, n) => (((n : ℂ) + 2) ^ 3 - ((n : ℂ) + 2)) / 12 *
      (affineSl2VOA_closed k hk).centralCharge

theorem ws_current (a : Fin 3) (n : ℕ) :
    correctedWordState k hk [(.current a, n)] = J k a (-(n : ℤ) - 1) (vacuumA k) := by
  rw [correctedWordState_cons]
  exact smul_currentState_eq_J k hk a _ _

theorem ws_sugawara (n : ℕ) :
    correctedWordState k hk [(.sugawara, n)] =
      (affineSl2VOA_closed k hk).L (-(n : ℤ) - 2) (vacuumA k) := by
  rw [correctedWordState_cons, L_def, show (-(n : ℤ) - 2 + 1) = -(n : ℤ) - 1 by ring]
  rfl

theorem L_vacuum_eq_zero {d : ℤ} (hd : -1 ≤ d) :
    (affineSl2VOA_closed k hk).L d (vacuumA k) = 0 := by
  rw [L_def]
  exact (affineSl2VOA_closed k hk).toPreVertexAlgebra.smul_vacuum_nonneg _ (by omega)

/-- `L_m J^a_ν = J^a_ν L_m - ν J^a_{m+ν}` on the universal algebra. -/
theorem L_J (m : ℤ) (a : Fin 3) (ν : ℤ) (y : WakModule k) :
    (affineSl2VOA_closed k hk).L m (J k a ν y) =
      J k a ν ((affineSl2VOA_closed k hk).L m y) + ((-ν : ℤ) : ℂ) • J k a (m + ν) y :=
  Vir.Lcomm_J_apply k hk m a ν y

theorem J_vac (a : Fin 3) {m : ℤ} (hm : 0 ≤ m) : J k a m (vacuumA k) = 0 :=
  J_vacuum_nonneg k a hm

/-- **The pairing table** of dual one-letter words. -/
theorem letterPair (l l' : Generator × ℕ) :
    (universalForm k hk).form (correctedWordState k hk [dualLetter l])
        (correctedWordState k hk [l']) =
      if l' = l then pairVal k hk l else 0 := by
  have hvac : (universalForm k hk).form (vacuumA k) (vacuumA k) = 1 :=
    universalForm_normalized k hk
  by_cases hw : letterWt l = letterWt l'
  · obtain ⟨g, n⟩ := l
    obtain ⟨g', n'⟩ := l'
    cases g with
    | current a =>
      cases g' with
      | current b =>
        have hn : n' = n := by simp [letterWt] at hw; omega
        subst n'
        rw [dualLetter, ws_current, ws_current, AffineSl2BelowCritical.universalForm_current_adj hk]
        have hc := LinearMap.congr_fun (current_comm k (dualIdx a) b (-(-(n : ℤ) - 1))
          (-(n : ℤ) - 1)) (vacuumA k)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
          LinearMap.sum_apply, LinearMap.smul_apply] at hc
        rw [sub_eq_iff_eq_add] at hc
        rw [hc, J_vac k _ (by omega), map_zero, add_zero,
          show -(-(n : ℤ) - 1) + (-(n : ℤ) - 1) = 0 by ring, if_pos rfl]
        simp only [J_vac k _ (le_refl 0), smul_zero, Finset.sum_const_zero, zero_add,
          LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul, hvac, mul_one]
        match a, b with
        | 0, 0 => simp [dualIdx, kappa, pairVal]; ring
        | 0, 1 => simp [dualIdx, kappa]
        | 0, 2 => simp [dualIdx, kappa]
        | 1, 0 => simp [dualIdx, kappa]
        | 1, 1 => simp [dualIdx, kappa, pairVal]; ring
        | 1, 2 => simp [dualIdx, kappa]
        | 2, 0 => simp [dualIdx, kappa]
        | 2, 1 => simp [dualIdx, kappa]
        | 2, 2 => simp [dualIdx, kappa, pairVal]; ring
      | sugawara =>
        have hn : (n' : ℤ) + 1 = n := by simp [letterWt] at hw; omega
        rw [if_neg (by simp), dualLetter, ws_current, ws_sugawara,
          AffineSl2BelowCritical.universalForm_current_adj hk]
        have h := L_J k hk (-(n' : ℤ) - 2) (dualIdx a) (-(-(n : ℤ) - 1)) (vacuumA k)
        rw [J_vac k _ (by omega), map_zero,
          show -(n' : ℤ) - 2 + -(-(n : ℤ) - 1) = 0 by omega, J_vac k _ le_rfl, smul_zero,
          add_zero] at h
        rw [← h, map_zero, neg_zero]
    | sugawara =>
      cases g' with
      | current b =>
        have hn : (n' : ℤ) = n + 1 := by simp [letterWt] at hw; omega
        rw [if_neg (by simp), dualLetter, ws_current, ws_sugawara,
          (universalForm k hk).virasoro_adj, L_J, L_vacuum_eq_zero k hk (by omega), map_zero,
          zero_add, show -(-(n : ℤ) - 2) + (-(n' : ℤ) - 1) = 0 by omega, J_vac k _ le_rfl,
          smul_zero, map_zero]
      | sugawara =>
        have hn : n' = n := by simp [letterWt] at hw; omega
        subst n'
        rw [if_pos rfl, dualLetter, ws_sugawara, (universalForm k hk).virasoro_adj]
        have hv := (affineSl2VOA_closed k hk).L_virasoro (-(-(n : ℤ) - 2)) (-(n : ℤ) - 2)
        rw [LieRing.of_associative_ring_bracket] at hv
        have happ := congrArg (fun T : Module.End ℂ (WakModule k) => T (vacuumA k)) hv
        simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
          LinearMap.smul_apply] at happ
        rw [L_vacuum_eq_zero k hk (d := -(-(n : ℤ) - 2)) (by omega), map_zero, sub_zero,
          show -(-(n : ℤ) - 2) + (-(n : ℤ) - 2) = 0 by ring,
          L_vacuum_eq_zero k hk (d := 0) (by omega), smul_zero, zero_add, if_pos rfl] at happ
        rw [happ, LinearMap.smul_apply, Module.End.one_apply, map_smul, hvac,
          smul_eq_mul, mul_one, pairVal]
        push_cast
        ring
  · rw [if_neg (fun h => hw (by rw [h]))]
    apply (universalForm k hk).orthogonal_of_ne (m := letterWt l) (n := letterWt l') hw
    · have h := correctedWordState_mem_grading k hk [dualLetter l]
      simpa [wordWt, letterWt_dualLetter] using h
    · simpa [wordWt] using correctedWordState_mem_grading k hk [l']

end Pairing

/-! ### Independence in the simple quotient -/

theorem pairVal_ne_zero (l : Generator × ℕ) : pairVal ALevel aNoncritical l ≠ 0 := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    rw [pairVal, aLevel_eq]
    have hn : (n : ℂ) + 1 ≠ 0 := by norm_cast
    have hκ : kappa (dualIdx a) a ≠ 0 := by
      match a with
      | 0 => simp [dualIdx, kappa]
      | 1 => simp [dualIdx, kappa]
      | 2 => simp [dualIdx, kappa]
    have h43 : (-4 / 3 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn) h43) hκ
  | sugawara =>
    rw [pairVal, closed_centralCharge, aLevel_eq]
    have hc : (3 * (-4 / 3 : ℂ) / (-4 / 3 + 2)) ≠ 0 := by norm_num
    refine mul_ne_zero (div_ne_zero ?_ (by norm_num)) hc
    have h : ((n : ℂ) + 2) ^ 3 - ((n : ℂ) + 2) = (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℂ) := by
      push_cast; ring
    rw [h, Nat.cast_ne_zero]
    positivity

/-- The universal states of the degree-one spanning family: the vacuum and the one-letter
words. -/
def degOneWord : Option (Generator × ℕ) → List (Generator × ℕ)
  | none => []
  | some l => [l]

/-- Their dual partners. -/
def degOnePartner : Option (Generator × ℕ) → List (Generator × ℕ)
  | none => []
  | some l => [dualLetter l]

/-- The diagonal values, with `1` for the vacuum. -/
def degOneVal : Option (Generator × ℕ) → ℂ
  | none => 1
  | some l => pairVal ALevel aNoncritical l

theorem degOneVal_ne_zero (i : Option (Generator × ℕ)) : degOneVal i ≠ 0 := by
  cases i with
  | none => exact one_ne_zero
  | some l => exact pairVal_ne_zero l

theorem letterWt_pos (l : Generator × ℕ) : 0 < letterWt l := by
  obtain ⟨g, n⟩ := l
  cases g <;> simp [letterWt]; omega

theorem degOnePair (i j : Option (Generator × ℕ)) :
    (universalForm ALevel aNoncritical).form
        (correctedWordState ALevel aNoncritical (degOnePartner i))
        (correctedWordState ALevel aNoncritical (degOneWord j)) =
      if j = i then degOneVal i else 0 := by
  have hvac : (universalForm ALevel aNoncritical).form (vacuumA ALevel) (vacuumA ALevel) = 1 :=
    universalForm_normalized ALevel aNoncritical
  cases i with
  | none =>
    cases j with
    | none => simpa [degOnePartner, degOneWord, degOneVal] using hvac
    | some l =>
      rw [if_neg (by simp)]
      apply (universalForm ALevel aNoncritical).orthogonal_of_ne (m := 0) (n := letterWt l)
        (letterWt_pos l).ne
      · simpa [wordWt] using correctedWordState_mem_grading ALevel aNoncritical []
      · simpa [wordWt] using correctedWordState_mem_grading ALevel aNoncritical [l]
  | some l =>
    cases j with
    | none =>
      rw [if_neg (by simp)]
      apply (universalForm ALevel aNoncritical).orthogonal_of_ne (m := letterWt l) (n := 0)
        (letterWt_pos l).ne'
      · simpa [wordWt, letterWt_dualLetter] using
          correctedWordState_mem_grading ALevel aNoncritical [dualLetter l]
      · simpa [wordWt] using correctedWordState_mem_grading ALevel aNoncritical []
    | some l' =>
      rw [degOnePartner, degOneWord, letterPair]
      simp [degOneVal]

/-- The degree-one family in the simple quotient. -/
def degOneVec (i : Option (Generator × ℕ)) : ASpace :=
  Imax.mkQ (correctedWordState ALevel aNoncritical (degOneWord i))

/-- **The vacuum and the one-letter classes are linearly independent in `L_{-4/3}(sl₂)`.** -/
theorem degreeOne_linearIndependent : LinearIndependent ℂ degOneVec := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  set z := ∑ j ∈ s, g j • correctedWordState ALevel aNoncritical (degOneWord j) with hz
  have hz0 : Imax.mkQ z = 0 := by
    rw [hz, map_sum]
    simpa [degOneVec] using hsum
  have hpair : (universalForm ALevel aNoncritical).form
      (correctedWordState ALevel aNoncritical (degOnePartner i)) z = 0 := by
    rw [← simpleForm_mkQ ALevel aNoncritical, hz0, map_zero]
  rw [hz, map_sum] at hpair
  simp only [map_smul, degOnePair, smul_eq_mul, mul_ite, mul_zero] at hpair
  rw [Finset.sum_ite_eq' s i, if_pos hi] at hpair
  exact (mul_eq_zero.mp hpair).resolve_right (degOneVal_ne_zero i)

/-- `F_1 L` is spanned by the degree-one family. -/
theorem aFil_one_eq_span : aFil 1 = Submodule.span ℂ (Set.range degOneVec) := by
  rw [aFil_eq_map, UP, correctedAffineRPiece, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
    match w, hw with
    | [], _ => exact ⟨none, rfl⟩
    | [l], _ => exact ⟨some l, rfl⟩
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact ⟨_, ⟨⟨[], by simp⟩, rfl⟩, rfl⟩
    | some l => exact ⟨_, ⟨⟨[l], by simp⟩, rfl⟩, rfl⟩

/-- The symbol of a member of the degree-one family. -/
def degOneSym : Option (Generator × ℕ) → JetPoly
  | none => 0
  | some l => letterSym l

/-- The degree-one symbol map, defined on the basis. -/
def σOne : aFil 1 →ₗ[ℂ] JetPoly :=
  Finsupp.linearCombination ℂ degOneSym ∘ₗ degreeOne_linearIndependent.repr ∘ₗ
    (LinearEquiv.ofEq _ _ aFil_one_eq_span).toLinearMap

theorem σOne_apply_vec (i : Option (Generator × ℕ)) (h : degOneVec i ∈ aFil 1) :
    σOne ⟨degOneVec i, h⟩ = degOneSym i := by
  rw [σOne, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    degreeOne_linearIndependent.repr_eq_single i _ rfl, Finsupp.linearCombination_single,
    one_smul]

/-- **The degree-one word symbols are well defined** (proved). -/
def wordSymbolDescends_one : WordSymbolDescends 1 where
  σ := σOne
  lower x hx := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (aFil_zero_le hx)
    have hx' : x = c • ⟨degOneVec none, aFil_one_eq_span ▸
        Submodule.subset_span ⟨none, rfl⟩⟩ := Subtype.ext hc.symm
    rw [hx', map_smul, σOne_apply_vec, degOneSym, smul_zero]
  word w hw := by
    match w, hw with
    | [l], _ =>
      have h := σOne_apply_vec (some l) (wordClass_mem_aFil [l] le_rfl)
      rw [degOneSym] at h
      rw [wordSym_cons, wordSym_nil, mul_one, ← h]
      rfl

/-- **The degree-one leading-symbol map** (proved outright). -/
def jetLeadingSymbol_one : JetLeadingSymbol 1 := wordSymbolDescends_one.toJetLeadingSymbol

/-- The leading-symbol maps for `r ≥ 1`, the `r = 1` one being proved. -/
def jetLeadingSymbols_of_descends (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) :
    ∀ r : ℕ, JetLeadingSymbol (r + 1)
  | 0 => jetLeadingSymbol_one
  | r + 1 => (desc r).toJetLeadingSymbol

/-- **Affine GU ⇒ Lee–Yang GU**, with the leading-symbol maps reduced to well-definedness of
the Adamović word symbols in corrected degrees `r ≥ 2` (degrees `0` and `1` proved).
`#print axioms`-clean, conditional on `hA` (the hypothesis), `desc` (`WordSymbolDescends (r+2)`;
constructed: `Desc.wordSymbolDescends`), `chi` (`JetProductBound`; proved:
`JetProduct.jetProductBound_of_lower JetFermionic.jetFermionicLower`), `lower` (classical
Rogers–Ramanujan; proved: `RRLower.leeYangRRLowerBound_holds`). -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols_two
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) (chi : JetProductBound)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  VOA.KoszulResidual.leeYang_gradedUnitary_of_affine_leadingSymbol hA
    (jetLeadingSymbols_of_descends desc) chi lower

end

end VOA.AdamovicSymbol
