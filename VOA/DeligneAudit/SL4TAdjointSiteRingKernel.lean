import VOA.DeligneAudit.SL4TAdjointSiteResiduals

/-!
# A component of the ring kernel at one adjoint site

The component is the term `[d₁ = 0] J_h(g₁)`.

On a block whose first Levi key has no `x = f₁` letter (`d₁ = 0`), the current `g(h) = f₂(h)`
commutes with the remaining radical letters `y = f₁₂` and `z = f_θ` and kills `v`, so it kills the
whole first Levi layer (`middleLowering_kills_radicalLayer`). In the rank-two Levi it commutes
with every `g`- and `q`-letter, so every second Levi word containing a `g`-letter of mode `h`
vanishes; letters of mode at least `h + 1` vanish by the current cutoff
(`adjointSite_secondLevi_middlePower_zero`). Hence the power sums `p_s(g₁)`, `s ≥ h`, annihilate
the actual second Levi multiplicity evaluation (`adjointSite_middleAlphabetTail_le_kernel`):

    [d₁ = 0] J_h(g₁) ⊆ ker π̄.

The remaining terms of Corollary K (`J_h(x₂)` on every block and `J_h(g₂)` on the blocks with
`d₃ = 1`, the latter via `J₃⁰` and `J₃¹`) are not formalized in this file.
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

noncomputable section

/-- `[g, y] = 0`. -/
theorem bracket_middle_compound (e : Fin 15) : bracketInt 9 7 e = 0 := by
  fin_cases e <;> decide

/-- `[g, z] = 0`. -/
theorem bracket_middle_highest (e : Fin 15) : bracketInt 9 8 e = 0 := by
  fin_cases e <;> decide

section Position

variable {σ W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A labelled mode product vanishes on a vector killed by one of its factors, when that factor
commutes with every position operator. -/
theorem positionModeProduct_apply_eq_zero (F : σ → ℕ → Module.End ℂ W) (is : List σ)
    (u : σ → ℕ) (x : W) (i : σ) (hi : i ∈ is)
    (hcomm : ∀ j s, Commute (F i (u i)) (F j s)) (hx : F i (u i) x = 0) :
    positionModeProduct F is u x = 0 := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    change (F j (u j) * positionModeProduct F js u) x = 0
    rw [Module.End.mul_apply]
    by_cases hij : i = j
    · subst hij
      have hc : Commute (F i (u i)) (positionModeProduct F js u) := by
        unfold positionModeProduct
        apply Commute.list_prod_right
        intro T hT
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hT
        exact hcomm k (u k)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hx, map_zero]
    · rw [ih (List.mem_of_ne_of_mem hij hi), map_zero]

end Position

section Levi

variable {W : Type} [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W)

/-- `[g(r), g(s)] = 0` in the rank-two Levi. -/
theorem leviMiddle_middle_commute (r s : ℕ) : Commute (Q.op 3 r) (Q.op 3 s) := by
  apply LinearMap.ext
  intro X
  have h : Q.op 3 r (Q.op 3 s X) - Q.op 3 s (Q.op 3 r X) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 3 3 r s X
  exact sub_eq_zero.mp h

/-- `[g(r), q(s)] = 0` in the rank-two Levi. -/
theorem leviMiddle_compound_commute (r s : ℕ) : Commute (Q.op 3 r) (Q.op 5 s) := by
  apply LinearMap.ext
  intro X
  have h : Q.op 3 r (Q.op 5 s X) - Q.op 5 s (Q.op 3 r X) = 0 := by
    simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using Q.comm 3 5 r s X
  exact sub_eq_zero.mp h

end Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Without `x`-letters, `g(h)` kills the whole first Levi layer when it kills `v`. -/
theorem middleLowering_kills_radicalLayer (h : ℕ) (hg : ρ.op 9 h w = 0) (D : Fin 3 → ℕ)
    (hD : D 0 = 0) (u : V) (hu : u ∈ radicalCountLayer ρ w D) : ρ.op 9 h u = 0 := by
  rw [← radicalModeEvaluation_range] at hu
  obtain ⟨P, rfl⟩ := hu
  induction P using MvPolynomial.induction_on' with
  | monomial m z =>
    rw [radicalModeEvaluation_monomial, map_smul]
    have hxs : (List.ofFn fun i : Fin (D 0) => m (.inl i)) = [] :=
      List.ofFn_eq_nil_iff.mpr hD
    simp only [radicalModeWord, hxs, aWord, List.map_nil, List.prod_nil, one_mul]
    have hc : Commute (ρ.op 9 h)
        (((List.ofFn fun i => m (.inr (.inl i))).map fun s => ρ.op (F 1) s).prod *
          ((List.ofFn fun i => m (.inr (.inr i))).map fun s => ρ.op (F 2) s).prod) := by
      apply Commute.mul_right
      · apply Commute.list_prod_right
        intro T hT
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hT
        exact LinearMap.ext fun v => op_comm_of_zero_bracket ρ bracket_middle_compound h s v
      · apply Commute.list_prod_right
        intro T hT
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hT
        exact LinearMap.ext fun v => op_comm_of_zero_bracket ρ bracket_middle_highest h s v
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hg, map_zero, smul_zero]
  | add P R hP hR => rw [map_add, map_add, hP, hR, add_zero]

/-- Without `x`-letters, `g(h)` kills every first Levi multiplicity vector in the quotient. -/
theorem adjointSite_middleLowering_kills_image (B h : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0) (D : Fin 3 → ℕ)
    (hD : D 0 = 0) (b : RadicalGrassmannianRing 1 B 1 D) :
    (radicalCountQuotCurrent ρ w D).op 3 h
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW D b) = 0 := by
  obtain ⟨u, hu, he⟩ := (radicalGrassmannianEvaluation ρ w 1 B 1 hW D b).property
  change (radicalCountQuotCurrent ρ w D).op 3 h
    (radicalGrassmannianEvaluation ρ w 1 B 1 hW D b).val = 0
  rw [← he]
  change (higherRadicalCountClosure ρ w D).mkQ (ρ.op 9 h u) = 0
  rw [middleLowering_kills_radicalLayer ρ w h hg D hD u hu, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi source has a tensor product of Grassmannian rings as coefficients.
/-- Without `x`-letters, the mode-`h` power sum of the `g`-alphabet kills every second Levi
mode polynomial in the first Levi quotient of `M(B, h)`. -/
theorem adjointSite_secondLevi_middlePower_zero (B h : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0)
    (hg : ρ.op 9 h w = 0) (D : Fin 3 → ℕ) (hD : D 0 = 0) (e₁ e₂ : ℕ)
    (P : MvPolynomial (SecondLeviModeSlot e₁ e₂) (RadicalGrassmannianRing 1 B 1 D)) :
    secondLeviModeEvaluation (radicalCountQuotCurrent ρ w D)
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW D) e₁ e₂
        (secondLeviModePowerSum e₁ e₂ 0 h * P) = 0 := by
  classical
  unfold secondLeviModePowerSum
  rw [if_pos rfl, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  induction P using MvPolynomial.induction_on' with
  | monomial m b =>
    rw [X_pow_eq_monomial, monomial_mul, one_mul]
    unfold secondLeviModeEvaluation
    rw [positionModeEvaluation_monomial]
    let Q := radicalCountQuotCurrent ρ w D
    have hmode : (Finsupp.single (Sum.inl i : SecondLeviModeSlot e₁ e₂) h + m) (.inl i) =
        h + m (.inl i) := by simp
    apply positionModeProduct_apply_eq_zero _ _ _ _ (.inl i)
      (by simp [secondLeviModePositions])
    · intro j s
      change Commute (Q.op 3 _) (secondLeviPositionOperator Q e₁ e₂ j s)
      rcases j with j | j
      · exact leviMiddle_middle_commute Q _ s
      · exact leviMiddle_compound_commute Q _ s
    · change Q.op 3 _ _ = 0
      rw [hmode]
      by_cases hm : m (.inl i) = 0
      · rw [hm, add_zero]
        exact adjointSite_middleLowering_kills_image ρ w B h hW hg D hD b
      · exact radicalCountQuot_truncated ρ w (h + 1) ht D 3 _ (by omega) _
  | add P R hP hR => rw [mul_add, map_add, hP, hR, add_zero]

set_option maxHeartbeats 800000 in
-- Descent expands two quotient maps over a tensor-product coefficient algebra.
set_option synthInstance.maxHeartbeats 100000 in
/-- On a block with `d₁ = 0`, the mode-`h` power sum of `g₁` lies in the evaluation kernel. -/
theorem adjointSite_middleAlphabet_mode_zero (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0)
    (hg : ρ.op 9 h w = 0) (d : Fin 3 → ℕ) (hd : d 0 = 0) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂))
    (φ : MixedRing (mixedLabelBlockParams 1 B d e₁ e₂)) :
    mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
      (mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂))
        3 (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 3) h * φ) = 0 := by
  unfold mixedSecondLeviEvaluation
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
    mixedToRadicalRelative_alphabetPowerSum]
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (mixedToRadicalRelative 1 B d e₁ e₂ hv φ)
  rw [← hP, ← map_mul, radicalSecondLeviRelativeEvaluation_mk]
  apply Subtype.ext
  change Submodule.mkQ _ (secondLeviModeEvaluation _ _ e₁ e₂ (_ * P.val)) = 0
  rw [show mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) =
    ![d 0, d 1, d 2, e₁, e₂] by simp [mixedLengths, mixedLabelBlockParams]]
  obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
  change Submodule.mkQ _ (secondLeviModeEvaluation _ _ e₁ e₂
    ((secondLeviElementaryAlphabet e₁ e₂ 0
      (powerSumOfCoeff (if (0 : Fin 2) = 0 then e₁ else e₂)
        (fun k => (-1) ^ k * elementary k) (s + 1))).val * P.val)) = 0
  rw [secondLeviElementaryAlphabet_powerSum,
    adjointSite_secondLevi_middlePower_zero ρ w B (s + 1) hW ht hg d hd e₁ e₂ P.val, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- The multiplicity target is built over nested tensor-product coefficient algebras.
/-- **The `[d₁ = 0] J_h(g₁)` part of the ring kernel.** On a block with `d₁ = 0`, every power
sum `p_s(g₁)` with `s ≥ h` annihilates the actual second Levi multiplicity evaluation of any
module with the relations of `M(B, h)`. -/
theorem adjointSite_middleAlphabetTail_le_kernel (B h : ℕ) (hh : 0 < h)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (ht : ∀ i s v, h + 1 ≤ s → ρ.op i s v = 0)
    (hg : ρ.op 9 h w = 0) (d : Fin 3 → ℕ) (hd : d 0 = 0) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) :
    (mixedAlphabetModeTailIdeal (mixedLabelBlockParams 1 B d e₁ e₂) 3 h).restrictScalars ℂ ≤
      LinearMap.ker (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv) := by
  have hle : mixedAlphabetModeTailIdeal (mixedLabelBlockParams 1 B d e₁ e₂) 3 h ≤
      evaluationAnnihilator (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩ φ
    rcases eq_or_lt_of_le hs with rfl | hs'
    · exact adjointSite_middleAlphabet_mode_zero ρ w B h hh hW ht hg d hd e₁ e₂ hv φ
    · exact mixedSecondLeviEvaluation_alphabetPowerSum_tail ρ w 1 B (h + 1) ht hW d e₁ e₂ hv
        3 s hs' (by omega) φ
  exact fun x hx => evaluationAnnihilator_le_kernel _ (hle hx)

end

end VOA.DeligneAudit.SL4T
