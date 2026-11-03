/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictEndpoint

/-!
# Singular vectors of the model ring `R[u_j, v_j]` are `v₀`-powers

Let `R` be any commutative `ℂ`-algebra and let the nonnegative modes `J^a_j` of `sl₂[t]` act
on `R[u_j, v_j]` by the model derivations `mder R` (they kill `R`).  Call `s` *singular of
charge `c`* if every positive mode kills it, `f₀` kills it, and `h₀ s = c s`
(the lowest-weight convention of `VOA.SocleDual.sing`).

* `evV R` — the `R`-algebra map `R[u_j, v_j] → R[y]` with `u_j ↦ 0`, `v₀ ↦ y`, `v_{j+1} ↦ 0`
  (restriction to the line `u = 0`, `v(s) = y`);
* `evV_mder_e0` — `evV ∘ e₀ = 0`; `evV_mder_h0` — `evV ∘ h₀ = -y d/dy ∘ evV`;
* `coeff_evV_eq_zero_of_charge` — an `h₀`-eigenvector of eigenvalue `c` has
  `coeff_k (evV s) = 0` unless `c = -k`;
* `mZeroModeRel R` — the zero-mode relations of `VOA.SocleDual.ZeroModeRel` on the model ring;
* `eq_zero_of_msing_evV` — **a singular vector with `evV s = 0` vanishes** (the `e₀`-string
  argument plus cyclicity of the base-point evaluation `m_cyclic`);
* `msing_eq_C_mul_pow` — **a singular vector of charge `-q` is `τ · v₀^q` with
  `τ = coeff_q (evV s) ∈ R`**, and `msing_eq_zero_of_ne` — there are no nonzero singular
  vectors of any charge outside `-ℕ`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.SocleDual VOA.CyclicEval

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-! ### The line evaluation `evV` -/

/-- `u_j ↦ 0`, `v₀ ↦ y`, `v_{j+1} ↦ 0`. -/
def evV : MPoly R →ₐ[R] Polynomial R :=
  aeval fun x => if x = (1, 0) then Polynomial.X else 0

omit [Algebra ℂ R] in
@[simp] theorem evV_X (x : Fin 2 × ℕ) :
    evV R (X x) = if x = (1, 0) then Polynomial.X else 0 := aeval_X _ _

omit [Algebra ℂ R] in
@[simp] theorem evV_C (a : R) : evV R (MvPolynomial.C a) = Polynomial.C a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_eq]

theorem evV_ι_X (x : Fin 2 × ℕ) :
    evV R (ι R (X x)) = if x = (1, 0) then Polynomial.X else 0 := by
  rw [ι_X, evV_X]

/-- The base-point evaluation is `evV` followed by `y ↦ 1`. -/
theorem evR_eq_eval_evV (Q : MPoly R) : evR R Q = (evV R Q).eval 1 := by
  have h : evR R = (Polynomial.aeval (1 : R)).comp (evV R) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [evR, aeval_X, AlgHom.comp_apply, evV_X, baseVal]
    split_ifs <;> simp
  rw [h, AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval]

/-! ### `evV` against `e₀` and `h₀` -/

theorem mder_X_zero_zero (x : Fin 2 × ℕ) :
    mder R (0, 0) (X x) = if x.1 = 1 then X (0, x.2) else 0 := by
  rw [mder_X]
  obtain ⟨b, j⟩ := x
  fin_cases b <;> simp [jetDerVal, shiftVar]

theorem mder_X_two_zero (x : Fin 2 × ℕ) :
    mder R (2, 0) (X x) = if x.1 = 0 then X x else -X x := by
  rw [mder_X]
  obtain ⟨b, j⟩ := x
  fin_cases b <;> simp [jetDerVal, shiftVar]

/-- `evV ∘ e₀ = 0`: `e₀` produces a `u` in every monomial. -/
theorem evV_mder_e0 (Q : MPoly R) : evV R (mder R (0, 0) Q) = 0 := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [mder_C, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p x hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
      mder_X_zero_zero]
    obtain ⟨b, j⟩ := x
    fin_cases b <;> simp

/-- `evV ∘ h₀ = -y d/dy ∘ evV`. -/
theorem evV_mder_h0 (Q : MPoly R) :
    evV R (mder R (2, 0) Q) = -(Polynomial.X * Polynomial.derivative (evV R Q)) := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [mder_C, map_zero, evV_C, Polynomial.derivative_C, mul_zero, neg_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, Polynomial.derivative_add, mul_add,
      neg_add]
  | mul_X p x hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp,
      mder_X_two_zero, map_mul, Polynomial.derivative_mul]
    obtain ⟨b, j⟩ := x
    fin_cases b
    · simp
    · cases j
      · simp; ring
      · simp

omit [Algebra ℂ R] in
theorem coeff_X_mul_derivative (P : Polynomial R) (k : ℕ) :
    (Polynomial.X * Polynomial.derivative P).coeff k = (k : R) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

theorem evV_smul (c : ℂ) (Q : MPoly R) : evV R (c • Q) = c • evV R Q :=
  (evV R).map_smul_of_tower c Q

/-- **Charge selects the `v₀`-power**: an `h₀`-eigenvector of eigenvalue `c` has
`coeff_k (evV s) = 0` unless `c = -k`. -/
theorem coeff_evV_eq_zero_of_charge {c : ℂ} {Q : MPoly R} (hh : mder R (2, 0) Q = c • Q)
    {k : ℕ} (hk : c ≠ -(k : ℂ)) : (evV R Q).coeff k = 0 := by
  have h1 := congrArg (fun P : Polynomial R => P.coeff k) (evV_mder_h0 R Q)
  simp only [hh, evV_smul, Polynomial.coeff_neg, coeff_X_mul_derivative,
    Polynomial.coeff_smul] at h1
  have h2 : (c + (k : ℂ)) • (evV R Q).coeff k = 0 := by
    rw [add_smul, h1, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul]
    ring
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hk
  · exact h

/-! ### The zero-mode relations on the model ring -/

theorem mder_commutator_X (k k' : Fin 3 × ℕ) (x : Fin 2 × ℕ) :
    ⁅mder R k, mder R k'⁆ (X x) =
      ι R (jetDer k (jetDer k' (X x)) - jetDer k' (jetDer k (X x))) := by
  rw [Derivation.commutator_apply, mder_X, mder_X, mder_ι, mder_ι, ← jetDer_X, ← jetDer_X,
    map_sub]

theorem mder_comm_e (m : ℕ) (Q : MPoly R) :
    mder R (0, m) (mder R (0, 0) Q) = mder R (0, 0) (mder R (0, m) Q) := by
  have h : ⁅mder R (0, m), mder R (0, 0)⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro x
    rw [mder_commutator_X, Derivation.zero_apply, jetComm_e, sub_self, map_zero]
  have := congrArg (fun D : Derivation R (MPoly R) (MPoly R) => D Q) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.mp this

theorem mder_comm_f (m : ℕ) (Q : MPoly R) :
    mder R (1, m) (mder R (0, 0) Q) = mder R (0, 0) (mder R (1, m) Q) - mder R (2, m) Q := by
  have h : ⁅mder R (1, m), mder R (0, 0)⁆ = -mder R (2, m) := by
    apply MvPolynomial.derivation_ext
    intro x
    rw [mder_commutator_X, Derivation.neg_apply, jetComm_f, sub_sub_cancel_left, map_neg,
      mder_X, jetDer_X]
  have := congrArg (fun D : Derivation R (MPoly R) (MPoly R) => D Q) h
  simp only [Derivation.commutator_apply, Derivation.neg_apply] at this
  rw [sub_eq_iff_eq_add'.mp this, sub_eq_add_neg]

theorem mder_comm_h (m : ℕ) (Q : MPoly R) :
    mder R (2, m) (mder R (0, 0) Q) =
      mder R (0, 0) (mder R (2, m) Q) + (2 : ℂ) • mder R (0, m) Q := by
  have h : ⁅mder R (2, m), mder R (0, 0)⁆ = (2 : ℂ) • mder R (0, m) := by
    apply MvPolynomial.derivation_ext
    intro x
    rw [mder_commutator_X, Derivation.smul_apply, jetComm_h, add_sub_cancel_left, map_smul,
      mder_X, jetDer_X]
  have := congrArg (fun D : Derivation R (MPoly R) (MPoly R) => D Q) h
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at this
  exact sub_eq_iff_eq_add'.mp this

/-- **The zero-mode relations on the model ring.** -/
theorem mZeroModeRel : ZeroModeRel (mρ R) where
  pos a j x hx := by
    have hx' : ∀ b : Fin 3, mder R (b, j + 1) x = 0 := hx
    simp only [mρ_apply]
    fin_cases a
    · change mder R (0, j + 1) (mder R (0, 0) x) = 0
      rw [mder_comm_e, hx' 0, map_zero]
    · change mder R (1, j + 1) (mder R (0, 0) x) = 0
      rw [mder_comm_f, hx' 1, hx' 2, map_zero, sub_zero]
    · change mder R (2, j + 1) (mder R (0, 0) x) = 0
      rw [mder_comm_h, hx' 2, hx' 0, map_zero, smul_zero, add_zero]
  fe x := mder_comm_f R 0 x
  he x := mder_comm_h R 0 x

/-! ### Singular vectors of the model ring -/

/-- Singular of charge `c` in the model ring (lowest-weight convention). -/
def MSing (c : ℂ) (s : MPoly R) : Prop :=
  (∀ a j, mρ R (a, j + 1) s = 0) ∧ mρ R (1, 0) s = 0 ∧ mρ R (2, 0) s = c • s

theorem MSing.sub {c : ℂ} {s s' : MPoly R} (h : MSing R c s) (h' : MSing R c s') :
    MSing R c (s - s') :=
  ⟨fun a j => by rw [map_sub, h.1, h'.1, sub_zero], by rw [map_sub, h.2.1, h'.2.1, sub_zero],
    by rw [map_sub, h.2.2, h'.2.2, smul_sub]⟩

theorem evR_pow_e0 (s : MPoly R) (hs : evV R s = 0) (k : ℕ) :
    evR R ((mρ R (0, 0) ^ k) s) = 0 := by
  cases k with
  | zero => simp [evR_eq_eval_evV, hs]
  | succ k =>
    rw [pow_succ_apply', mρ_apply, evR_eq_eval_evV, evV_mder_e0, Polynomial.eval_zero]

/-- **A singular vector with `evV s = 0` vanishes.** -/
theorem eq_zero_of_msing_evV {c : ℂ} {s : MPoly R} (hs : MSing R c s) (h0 : evV R s = 0) :
    s = 0 := by
  refine m_cyclic R s fun l => ?_
  have hmem := word_mem_eString (mZeroModeRel R) hs.1 hs.2.1 hs.2.2 l
  refine Submodule.span_induction (p := fun x _ => evR R x = 0) ?_ (map_zero _) ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩; exact evR_pow_e0 R s h0 k
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro t x _ hx
    rw [show evR R (t • x) = t • evR R x from (evR R).map_smul_of_tower t x, hx, smul_zero]

theorem msing_C_mul_pow (a : R) (q : ℕ) :
    MSing R (-(q : ℂ)) (MvPolynomial.C a * X (1, 0) ^ q) := by
  have hX : ∀ k : Fin 3 × ℕ, mder R k (MvPolynomial.C a * X (1, 0) ^ q) =
      MvPolynomial.C a * (q • (X (1, 0) ^ (q - 1) * mder R k (X (1, 0)))) := by
    intro k
    rw [Derivation.leibniz, mder_C, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz_pow,
      smul_eq_mul]
  refine ⟨fun b j => ?_, ?_, ?_⟩
  · rw [mρ_apply, hX, mder_X]
    fin_cases b <;> simp [jetDerVal, shiftVar]
  · rw [mρ_apply, hX, mder_X]
    simp [jetDerVal]
  · rw [mρ_apply, hX, mder_X_two_zero]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
    cases q with
    | zero => simp
    | succ q =>
      rw [Nat.add_sub_cancel, pow_succ, nsmul_eq_mul, Algebra.smul_def]
      simp only [map_neg, map_natCast]
      push_cast
      ring

/-- **A singular vector of charge `-q` is `τ · v₀^q`**, `τ = coeff_q (evV s)`. -/
theorem msing_eq_C_mul_pow {q : ℕ} {s : MPoly R} (hs : MSing R (-(q : ℂ)) s) :
    s = MvPolynomial.C ((evV R s).coeff q) * X (1, 0) ^ q := by
  have ht := hs.sub R (msing_C_mul_pow R ((evV R s).coeff q) q)
  have h0 : evV R (s - MvPolynomial.C ((evV R s).coeff q) * X (1, 0) ^ q) = 0 := by
    ext k
    rw [map_sub, map_mul, map_pow, evV_C, evV_X, if_pos rfl, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [hk, sub_self]
    · rw [coeff_evV_eq_zero_of_charge R hs.2.2
        (fun h => hk (by exact_mod_cast (neg_inj.mp h).symm)),
        sub_zero]
  exact sub_eq_zero.mp (eq_zero_of_msing_evV R ht h0)

/-- **No nonzero singular vectors of charge outside `-ℕ`.** -/
theorem msing_eq_zero_of_ne {c : ℂ} {s : MPoly R} (hs : MSing R c s)
    (hc : ∀ q : ℕ, c ≠ -(q : ℂ)) : s = 0 := by
  refine eq_zero_of_msing_evV R hs ?_
  ext k
  rw [coeff_evV_eq_zero_of_charge R hs.2.2 (hc k), Polynomial.coeff_zero]

end

end VOA.TwoSeries.StrictModel
