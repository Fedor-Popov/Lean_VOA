import VOA.DeligneAudit.SL4TAdjointSiteFlatKernel

/-!
# The flat mode-shift current and its Newton operators

The ingredients are the operator `H_s`, the Newton operator `D_f`, and the vanishing of the
`a = e` term.

The *flat shift current* is `H_s = 2 A₀(s) - (E₁₁ - E₂₂)(s) = ½ ((E₂₂ - E₃₃)(s) - (E₀₀ - E₁₁)(s))`,
where `A₀ = E₁₁ - ¼` is the outer alphabet current (`radicalAlphabetCurrent ρ 0`). It shifts
the modes of the letters `x`, `y` with sign `+1`, of `q`, `F` with sign `-1`, and commutes with
`z`, `g` and `η`. For `s ≥ 1` it kills the generator.

The Newton operator `D_f = newtonEnd H f` is the polynomial in the `H_s` that equals the signed
elementary symmetric function `(-1)^f e_f` when every `H_s` is replaced by a power sum `p_s`.

Generic results proved here, for any family of operators:
* `newtonEnd_le_comap`, `newtonEnd_commute`, `newtonEnd_intertwine`: a subspace, a commuting
  operator or an intertwining map that is compatible with every `H_s`, `s ≥ 1`, is compatible
  with every `D_f`;
* `newtonEnd_realizes`: if `H_s` realizes multiplication by `p_s` on representatives, then
  `D_f` realizes multiplication by the Newton coefficient of the `p_s`;
* `newtonEnd_shift_pow_eq_zero`: if `H_s` acts on a family `Y(n)` by `[H_s, Y(n)] = Y(s + n)`
  and kills `u`, then `D_f (Y(0)^k u) = 0` whenever `k < f` (the elementary symmetric function
  `e_f` of `k < f` commuting shifts is zero).
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-! ### Generic Newton operators -/

section Generic

variable {W M R : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
variable [CommRing R] [Algebra ℂ R]

/-- A subspace stable under every `H_s`, `s ≥ 1`, is stable under every Newton operator. -/
theorem newtonEnd_le_comap (H : ℕ → Module.End ℂ W) (N : Submodule ℂ W)
    (hN : ∀ s, 1 ≤ s → N ≤ N.comap (H s)) : ∀ n, N ≤ N.comap (newtonEnd H n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx
    cases n with
    | zero => simpa [newtonEnd] using hx
    | succ n =>
      simp only [Submodule.mem_comap, newtonEnd, LinearMap.smul_apply, LinearMap.sum_apply,
        Module.End.mul_apply]
      apply N.smul_mem
      apply N.sum_mem
      intro i _
      exact hN _ (by omega) (ih i.val i.isLt hx)

/-- An operator commuting with every `H_s`, `s ≥ 1`, commutes with every Newton operator. -/
theorem newtonEnd_commute (H : ℕ → Module.End ℂ W) (T : Module.End ℂ W)
    (hT : ∀ s, 1 ≤ s → Commute T (H s)) : ∀ n, Commute T (newtonEnd H n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [newtonEnd]
    | succ n =>
      rw [newtonEnd]
      apply Commute.smul_right
      apply Commute.sum_right
      intro i _
      exact (hT _ (by omega)).mul_right (ih i.val i.isLt)

/-- A linear map intertwining every `H_s`, `s ≥ 1`, intertwines every Newton operator. -/
theorem newtonEnd_intertwine (H : ℕ → Module.End ℂ W) (H' : ℕ → Module.End ℂ M)
    (qm : W →ₗ[ℂ] M) (hq : ∀ s, 1 ≤ s → ∀ x, qm (H s x) = H' s (qm x)) :
    ∀ n x, qm (newtonEnd H n x) = newtonEnd H' n (qm x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    cases n with
    | zero => simp [newtonEnd]
    | succ n =>
      simp only [newtonEnd, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply,
        map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hq _ (by omega), ih i.val i.isLt]

/-- If `H_s` realizes multiplication by `p_s` on representatives, the Newton operator realizes
multiplication by the Newton coefficient. -/
theorem newtonEnd_realizes (H : ℕ → Module.End ℂ W) (qm : W →ₗ[ℂ] M) (π : R →ₗ[ℂ] M)
    (p : ℕ → R) (hstep : ∀ s, 1 ≤ s → ∀ ψ y, qm y = π ψ → qm (H s y) = π (p s * ψ)) :
    ∀ n ψ y, qm y = π ψ → qm (newtonEnd H n y) = π (newtonCoeff p n * ψ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ψ y hy
    cases n with
    | zero => simpa only [newtonEnd, newtonCoeff, Module.End.one_apply, one_mul] using hy
    | succ n =>
      simp only [newtonEnd, newtonCoeff, LinearMap.smul_apply, LinearMap.sum_apply,
        Module.End.mul_apply, smul_mul_assoc, Finset.sum_mul, map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hstep _ (by omega) _ _ (ih i.val i.isLt ψ y hy), mul_assoc]

/-- The elementary symmetric polynomial of degree larger than the number of variables is zero. -/
theorem esymm_eq_zero_of_lt (k f : ℕ) (hkf : k < f) : MvPolynomial.esymm (Fin k) ℂ f = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr (by simpa using hkf),
    Finset.sum_empty]

/-- **The vanishing of `e_f` of fewer than `f` shifts.** If `[H_s, Y(n)] = Y(s + n)` and `H_s`
kills `u` for `s ≥ 1`, then `D_f (Y(0)^k u) = 0` whenever `k < f`. -/
theorem newtonEnd_shift_pow_eq_zero (H Y : ℕ → Module.End ℂ W)
    (hc : ∀ s, 1 ≤ s → ∀ n, H s * Y n - Y n * H s = Y (s + n))
    (u : W) (hu : ∀ s, 1 ≤ s → H s u = 0) (k f : ℕ) (hkf : k < f) :
    newtonEnd H f ((Y 0 ^ k) u) = 0 := by
  classical
  let β : ℂ →ₗ[ℂ] W := LinearMap.toSpanSingleton ℂ W u
  let E : MvPolynomial (Fin k) ℂ →ₗ[ℂ] W :=
    positionModeEvaluation (fun (_ : Fin k) n => Y n) (List.finRange k) β
  have hH : ∀ s, 1 ≤ s → ∀ a, H s (E a) = E (MvPolynomial.psum (Fin k) ℂ s * a) := by
    intro s hs a
    have he := positionModeEvaluation_cartan (fun (_ : Fin k) n => Y n) (List.finRange k)
      (List.nodup_finRange k) β (H s) 0 (fun _ => 1) s
      (fun i n => by simpa using hc s hs n)
      (fun b => by simp [β, hu s hs]) a
    rw [he]
    congr 2
    simp only [positionModePowerSum, MvPolynomial.psum, Fin.sum_univ_def, one_smul, map_zero,
      zero_add]
  have hE1 : E 1 = (Y 0 ^ k) u := by
    rw [← MvPolynomial.C_1, MvPolynomial.C_apply]
    change positionModeEvaluation (fun (_ : Fin k) n => Y n) (List.finRange k) β
      (monomial 0 1) = _
    rw [positionModeEvaluation_monomial]
    simp [positionModeProduct, β, List.map_const', List.prod_replicate]
  have hn := newtonEnd_pi H E (MvPolynomial.psum (Fin k) ℂ) hH f 1
  rw [hE1] at hn
  rw [hn, mul_one, newtonCoeff_psum, esymm_eq_zero_of_lt k f hkf, mul_zero, map_zero]

end Generic

/-! ### The flat shift current on the module -/

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The flat shift current `H_s = 2 A₀(s) - (E₁₁ - E₂₂)(s)`. -/
def flatShiftCurrent (s : ℕ) : Module.End ℂ V :=
  (2 : ℂ) • radicalAlphabetCurrent ρ 0 s - ρ.op 13 s

/-- `H_s = ½ ((E₂₂ - E₃₃)(s) - (E₀₀ - E₁₁)(s))`. -/
theorem flatShiftCurrent_eq_half (s : ℕ) :
    flatShiftCurrent ρ s = (1 / 2 : ℂ) • (ρ.op 14 s - ρ.op 12 s) := by
  apply LinearMap.ext
  intro u
  simp only [flatShiftCurrent, radicalAlphabetCurrent, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.neg_apply, show (0 : Fin 3) ≠ 2 by decide, if_false,
    if_true]
  module

/-- The commutator of `H_s` with a current whose two outer Cartan weights are `a` and `b`. -/
theorem flatShiftCurrent_comm_of (j : Fin 15) (a b : ℤ) (c : ℂ)
    (h12 : ∀ e, bracketInt 12 j e = if e = j then a else 0)
    (h14 : ∀ e, bracketInt 14 j e = if e = j then b else 0)
    (hc : ((b : ℂ) - a) / 2 = c) (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op j s u) =
      ρ.op j s (flatShiftCurrent ρ r u) + c • ρ.op j (r + s) u := by
  rw [← hc, flatShiftCurrent_eq_half]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  rw [op_comm_of_single_bracket ρ h14, op_comm_of_single_bracket ρ h12]
  simp only [map_smul, map_sub]
  module

theorem bracket_outerCartan_first (e : Fin 15) :
    bracketInt 12 6 e = if e = 6 then -2 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_first (e : Fin 15) :
    bracketInt 14 6 e = if e = 6 then 0 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_compound (e : Fin 15) :
    bracketInt 12 7 e = if e = 7 then -1 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_compound (e : Fin 15) :
    bracketInt 14 7 e = if e = 7 then 1 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_highest (e : Fin 15) :
    bracketInt 12 8 e = if e = 8 then -1 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_highest (e : Fin 15) :
    bracketInt 14 8 e = if e = 8 then -1 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_middle (e : Fin 15) :
    bracketInt 12 9 e = if e = 9 then 1 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_middle (e : Fin 15) :
    bracketInt 14 9 e = if e = 9 then 1 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_lastPair (e : Fin 15) :
    bracketInt 12 10 e = if e = 10 then 1 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_lastPair (e : Fin 15) :
    bracketInt 14 10 e = if e = 10 then -1 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_last (e : Fin 15) :
    bracketInt 12 11 e = if e = 11 then 0 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_last (e : Fin 15) :
    bracketInt 14 11 e = if e = 11 then -2 else 0 := by fin_cases e <;> decide
theorem bracket_outerCartan_raising (e : Fin 15) :
    bracketInt 12 3 e = if e = 3 then -1 else 0 := by fin_cases e <;> decide
theorem bracket_lastCartan_raising (e : Fin 15) :
    bracketInt 14 3 e = if e = 3 then -1 else 0 := by fin_cases e <;> decide

/-- `[H_s, x(n)] = x(s + n)`. -/
theorem flatShiftCurrent_first (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 6 s u) = ρ.op 6 s (flatShiftCurrent ρ r u) + ρ.op 6 (r + s) u := by
  rw [flatShiftCurrent_comm_of ρ 6 (-2) 0 1 bracket_outerCartan_first bracket_lastCartan_first
    (by norm_num), one_smul]

/-- `[H_s, y(n)] = y(s + n)`. -/
theorem flatShiftCurrent_compound (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 7 s u) = ρ.op 7 s (flatShiftCurrent ρ r u) + ρ.op 7 (r + s) u := by
  rw [flatShiftCurrent_comm_of ρ 7 (-1) 1 1 bracket_outerCartan_compound
    bracket_lastCartan_compound (by norm_num), one_smul]

/-- `H_s` commutes with `z`. -/
theorem flatShiftCurrent_highest (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 8 s u) = ρ.op 8 s (flatShiftCurrent ρ r u) := by
  rw [flatShiftCurrent_comm_of ρ 8 (-1) (-1) 0 bracket_outerCartan_highest
    bracket_lastCartan_highest (by norm_num), zero_smul, add_zero]

/-- `H_s` commutes with `g`. -/
theorem flatShiftCurrent_middle (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 9 s u) = ρ.op 9 s (flatShiftCurrent ρ r u) := by
  rw [flatShiftCurrent_comm_of ρ 9 1 1 0 bracket_outerCartan_middle bracket_lastCartan_middle
    (by norm_num), zero_smul, add_zero]

/-- `[H_s, q(n)] = -q(s + n)`. -/
theorem flatShiftCurrent_lastPair (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 10 s u) =
      ρ.op 10 s (flatShiftCurrent ρ r u) - ρ.op 10 (r + s) u := by
  rw [flatShiftCurrent_comm_of ρ 10 1 (-1) (-1) bracket_outerCartan_lastPair
    bracket_lastCartan_lastPair (by norm_num), neg_one_smul, ← sub_eq_add_neg]

/-- `[H_s, F(n)] = -F(s + n)`. -/
theorem flatShiftCurrent_last (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 11 s u) =
      ρ.op 11 s (flatShiftCurrent ρ r u) - ρ.op 11 (r + s) u := by
  rw [flatShiftCurrent_comm_of ρ 11 0 (-2) (-1) bracket_outerCartan_last bracket_lastCartan_last
    (by norm_num), neg_one_smul, ← sub_eq_add_neg]

/-- `H_s` commutes with `η`. -/
theorem flatShiftCurrent_raising (r s : ℕ) (u : V) :
    flatShiftCurrent ρ r (ρ.op 3 s u) = ρ.op 3 s (flatShiftCurrent ρ r u) := by
  rw [flatShiftCurrent_comm_of ρ 3 (-1) (-1) 0 bracket_outerCartan_raising
    bracket_lastCartan_raising (by norm_num), zero_smul, add_zero]

/-- `H_s` commutes with every power of `g(0)`. -/
theorem flatShiftCurrent_middlePow (r n : ℕ) (u : V) :
    flatShiftCurrent ρ r ((ρ.op 9 0 ^ n) u) = (ρ.op 9 0 ^ n) (flatShiftCurrent ρ r u) :=
  endomorphism_commute_pow _ _ (fun v => flatShiftCurrent_middle ρ r 0 v) n u

/-- `H_s` commutes with every power of `z(0)`. -/
theorem flatShiftCurrent_highestPow (r n : ℕ) (u : V) :
    flatShiftCurrent ρ r ((ρ.op 8 0 ^ n) u) = (ρ.op 8 0 ^ n) (flatShiftCurrent ρ r u) :=
  endomorphism_commute_pow _ _ (fun v => flatShiftCurrent_highest ρ r 0 v) n u

/-- For `s ≥ 1` the flat shift current kills the local Weyl generator. -/
theorem flatShiftCurrent_source_zero (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
    (s : ℕ) (hs : 1 ≤ s) : flatShiftCurrent ρ s w = 0 := by
  have h₁ := h.cartan_pos 1 s (by omega)
  simp only [simpleH] at h₁
  simp [flatShiftCurrent, radicalAlphabetCurrent_source_zero ρ w a b c h 0 s (by omega), h₁]

/-- The flat shift current preserves every higher first Levi closure. -/
theorem higherRadicalCountClosure_flatShift (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (s : ℕ) :
    higherRadicalCountClosure ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (flatShiftCurrent ρ s) := by
  intro v hv
  rw [Submodule.mem_comap, flatShiftCurrent, LinearMap.sub_apply, LinearMap.smul_apply]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (higherRadicalCountClosure_alphabet_current ρ w a b c h d 0 s hv))
    (a3LeviClosure_inv ρ _ 6 s hv)

/-- For `s ≥ 1` the flat shift current preserves the flat kernel space. -/
theorem flatKernelSpace_flatShift (B s : ℕ) (hs : 1 ≤ s) :
    flatKernelSpace ρ w B ≤ (flatKernelSpace ρ w B).comap (flatShiftCurrent ρ s) := by
  intro v hv
  rw [Submodule.mem_comap, flatShiftCurrent_eq_half, LinearMap.smul_apply, LinearMap.sub_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (flatKernelSpace_positive ρ w B 14 s hs hv) (flatKernelSpace_positive ρ w B 12 s hs hv))

/-- **Vanishing of the leak term.** If `H_s` kills `u` for every `s ≥ 1`, then the Newton
operator `D_f` kills `y^k u` whenever `k < f`. -/
theorem newtonEnd_flatShift_compoundPow_eq_zero (u : V)
    (hu : ∀ s, 1 ≤ s → flatShiftCurrent ρ s u = 0) (k f : ℕ) (hkf : k < f) :
    newtonEnd (flatShiftCurrent ρ) f ((ρ.op 7 0 ^ k) u) = 0 :=
  newtonEnd_shift_pow_eq_zero (flatShiftCurrent ρ) (fun n => ρ.op 7 n)
    (fun s _ n => LinearMap.ext fun v => by
      simp only [LinearMap.sub_apply, Module.End.mul_apply]
      rw [flatShiftCurrent_compound]
      abel)
    u hu k f hkf

end

end VOA.DeligneAudit.SL4T
