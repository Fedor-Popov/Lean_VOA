import VOA.Classification.COne.PlusRat6TwVac

/-! # Twisted Fock monomials are joint eigenvectors of `o(H⁴)`, `o(H⁶)`

On `FockT 1 ⊗ ℂ` the monomial `X^s ⊗ 1` (`s` an exponent vector; the variable `(n,a)` is the
creation mode `h(-(2n+1)/2)`) satisfies

* `o4_mono`: `o(H⁴)(X^s ⊗ 1) = (-1/128 + wtT 3 s / 8) • (X^s ⊗ 1)`,
* `o6_mono`: `o(H⁶)(X^s ⊗ 1) = (1/256 + wtT 5 s / 32) • (X^s ⊗ 1)`,

with `wtT e s = Σ_v s_v (2 v.1 + 1)^e`.  Proof: the vacuum values (`o4_vac`, `o6_vac`) and the
commutators with the creation modes (`comm_H4`, `comm_H6`).
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3 PlusRat5
open VOA.Moonshine.LatticeTwistedGeneral VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
open scoped TensorProduct

variable (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2)

/-- The power weight `v ↦ (2 v.1 + 1)^e`. -/
def pT (e : ℕ) : ℕ × Fin (rank (latP m)) → ℕ := fun v => (2 * v.1 + 1) ^ e

/-- `wtT e s = Σ_v s_v (2 v.1 + 1)^e`. -/
def wtT (e : ℕ) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) : ℕ := Finsupp.weight (pT m e) s

/-- The monomial state `X^s ⊗ 1`. -/
abbrev monoT (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) : FockT (rank (latP m)) ⊗[ℂ] ℂ :=
  (monomial s (1 : ℂ) : FockT (rank (latP m))) ⊗ₜ[ℂ] (1 : ℂ)

theorem fin_eq_a0 (a : Fin (rank (latP m))) : a = a0 m := by
  apply Fin.ext
  have h : (a : ℕ) < 1 := lt_of_lt_of_eq a.isLt (rank_latP m)
  simp only [a0]
  omega

theorem monoT_add_single (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (v : ℕ × Fin (rank (latP m))) :
    monoT m (Finsupp.single v 1 + s) =
      (Tw m hm t).YM (ls m hR) (-(2 * (v.1 : ℤ) + 1)) (monoT m s) := by
  rw [YM_h, LinearMap.rTensor_tmul, modeT_creation, monoT, monomial_add_single_eq]
  have hv : v = (v.1, a0 m) := Prod.ext rfl (fin_eq_a0 m v.2)
  rw [← hv]
where
  monomial_add_single_eq : (monomial (Finsupp.single v 1 + s) (1 : ℂ) : FockT (rank (latP m))) =
      X v * monomial s 1 := by
    rw [X, monomial_mul, one_mul]

theorem wtT_add_single (e : ℕ) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) (v : ℕ × Fin (rank (latP m))) :
    wtT m e (Finsupp.single v 1 + s) = (2 * v.1 + 1) ^ e + wtT m e s := by
  simp [wtT, pT, map_add, Finsupp.weight_single]

/-- Induction principle: build monomials by adding one variable at a time. -/
theorem finsupp_induction_single {P : ((ℕ × Fin (rank (latP m))) →₀ ℕ) → Prop} (h0 : P 0)
    (hs : ∀ v s, P s → P (Finsupp.single v 1 + s)) : ∀ s, P s := by
  intro s
  induction s using Finsupp.induction with
  | zero => exact h0
  | single_add a b f _ hb ih =>
    clear hb
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      rw [show Finsupp.single a (b + 1) + f = Finsupp.single a 1 + (Finsupp.single a b + f) by
        rw [← add_assoc, ← Finsupp.single_add, add_comm 1 b]]
      exact hs _ _ ihb

/-- Monomial eigenvalues of `o(H⁴)`. -/
theorem o4_mono (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    (Tw m hm t).YM (ls m H4R) 6 (monoT m s) =
      ((-1 / 128 : ℂ) + (wtT m 3 s : ℂ) / 8) • monoT m s := by
  induction s using finsupp_induction_single m with
  | h0 =>
    have := o4_vac m hm t
    simpa [monoT, wtT] using this
  | hs v s ih =>
    rw [monoT_add_single m hm t, comm_H4 m hm t _ ⟨-(v.1 : ℤ) - 1, by ring⟩, ih, map_smul,
      wtT_add_single, ← add_smul]
    congr 1
    push_cast
    ring

/-- Monomial eigenvalues of `o(H⁶)`. -/
theorem o6_mono (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    (Tw m hm t).YM (ls m H6R) 10 (monoT m s) =
      ((1 / 256 : ℂ) + (wtT m 5 s : ℂ) / 32) • monoT m s := by
  induction s using finsupp_induction_single m with
  | h0 =>
    have := o6_vac m hm t
    simpa [monoT, wtT] using this
  | hs v s ih =>
    rw [monoT_add_single m hm t, comm_H6 m hm t _ ⟨-(v.1 : ℤ) - 1, by ring⟩, ih, map_smul,
      wtT_add_single, ← add_smul]
    congr 1
    push_cast
    ring

end VOA.Classification.COne.PlusRat6
