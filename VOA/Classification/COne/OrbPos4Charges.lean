import VOA.Classification.COne.OrbPos4Grading

/-!
# Fractional charge generators on the shifted lattice carrier

These are candidate generator modes, NOT a `TwistedModule`. The charged
exponential is multiplied by `z^(-aβ/n)`; the root zero mode is translated by
`-a/n`. We verify support, truncation, recovery of all old charge modes, and
the obstruction to using an integral gluing lattice for this shift.
-/

namespace VOA.Classification.COne.OrbPos4
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 LatMod

/-- Candidate fractional modes of `e^(βα)`, with index `ℓ` representing `ℓ/n`.
The support congruence is `ℓ ≡ aβ mod n`. -/
noncomputable def fractionalChargeMode (n : ℕ) (a j β ℓ : ℤ) : Module.End ℂ Space :=
  if (ℓ - a*β) % (n : ℤ) = 0 then
    mode ((latticeModule 1 le_rfl j).YM (latChargeGen (latP 1) β))
      ((ℓ - a*β) / n)
  else 0

theorem fractionalChargeMode_support (n : ℕ) (a j β ℓ : ℤ)
    (h : (ℓ - a * β) % (n : ℤ) ≠ 0) : fractionalChargeMode n a j β ℓ = 0 := by
  rw [fractionalChargeMode, if_neg h]

/-- Every original charged mode is recovered at its shifted fractional index. -/
theorem fractionalChargeMode_recover {n : ℕ} (hn : 0 < n) (a j β k : ℤ) :
    fractionalChargeMode n a j β ((n : ℤ)*k+a*β) =
      mode ((latticeModule 1 le_rfl j).YM (latChargeGen (latP 1) β)) k := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  simp only [fractionalChargeMode, add_sub_cancel_right, Int.mul_emod_right,
    ite_true, Int.mul_ediv_cancel_left _ hn0]

theorem fractionalChargeMode_truncation {n : ℕ} (hn : 0 < n)
    (a j β : ℤ) (x : Space) :
    ∃ K : ℤ, ∀ ℓ : ℤ, K ≤ ℓ → fractionalChargeMode n a j β ℓ x = 0 := by
  obtain ⟨K, hK⟩ := (latticeModule 1 le_rfl j).truncation (latChargeGen (latP 1) β) x
  refine ⟨(n : ℤ)*K+a*β, fun ℓ hℓ => ?_⟩
  unfold fractionalChargeMode
  split_ifs
  · apply hK
    rw [Int.le_ediv_iff_mul_le (by exact_mod_cast hn)]
    nlinarith
  · rfl

/-- Invariance under the candidate charged modes is exactly invariance under
the ordinary charged modes. This alone does not assert full irreducibility. -/
theorem fractionalChargeMode_invariant_iff {n : ℕ} (hn : 0 < n)
    (a j : ℤ) (S : Submodule ℂ Space) :
    (∀ β ℓ x, x ∈ S → fractionalChargeMode n a j β ℓ x ∈ S) ↔
    (∀ (β k : ℤ) x, x ∈ S →
      mode ((latticeModule 1 le_rfl j).YM (latChargeGen (latP 1) β)) k x ∈ S) := by
  constructor
  · intro h β k x hx
    simpa only [fractionalChargeMode_recover hn] using h β ((n : ℤ)*k+a*β) x hx
  · intro h β ℓ x hx
    unfold fractionalChargeMode
    split_ifs
    · exact h β _ x hx
    · exact S.zero_mem

/-- The candidate charged generator family has no proper nonzero invariant
subspace. This proves generator irreducibility without asserting twisted Jacobi. -/
theorem fractionalChargeMode_irreducible {n : ℕ} (hn : 0 < n)
    (a j : ℤ) (S : Submodule ℂ Space)
    (hS : ∀ β ℓ x, x ∈ S → fractionalChargeMode n a j β ℓ x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have h := (fractionalChargeMode_invariant_iff hn a j S).mp hS
  let A := latticeModule 1 le_rfl j
  have ht : presSub A.toWeakModule S = ⊤ :=
    latVOA_generated (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) _
      (fun _ hu _ hv k => presSub_smul _ _ hu hv k) h
  let P : WeakModule.Submodule' A.toWeakModule :=
    { carrier := S
      act_mem := by
        intro v k x hx
        have hv : v ∈ presSub A.toWeakModule S := by rw [ht]; trivial
        exact hv k x hx }
  exact (latticeModule_isIrreducible 1 le_rfl j).2 P

/-- Any actual twisted extension of these generator modes is irreducible.
Existence of that extension is not supplied by this theorem. -/
theorem twistedIrreducible_of_fractionalChargeMode
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (P : TwistedModule g n Space)
    (hP : ∀ (β ℓ : ℤ), P.YM (latChargeGen (latP 1) β) ℓ =
      fractionalChargeMode n a j β ℓ) : TwistedIrreducible P := by
  refine ⟨(latticeModule_isIrreducible 1 le_rfl j).1, fun S hS => ?_⟩
  apply fractionalChargeMode_irreducible hn a j S
  intro β ℓ x hx
  rw [← hP]
  exact hS _ _ _ hx

/-- Corrected Heisenberg zero mode, including the central scalar correction. -/
noncomputable def fractionalRootZero (n : ℕ) (a j : ℤ) : Module.End ℂ Space :=
  charge j - ((a : ℂ) / n) • LinearMap.id

theorem fractionalRootZero_latState (n : ℕ) (a j k : ℤ)
    (p : FockN (rank (latP 1))) :
    fractionalRootZero n a j (latStateGen (latP 1) p k) =
      (2*(k : ℂ)+j-a/n) • latStateGen (latP 1) p k := by
  simp only [fractionalRootZero, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, charge_latState, sub_smul]

/-- Undoing the energy shift uses the corrected root zero mode. -/
theorem fractionalEnergy_inverse (n : ℕ) (a j : ℤ) :
    shiftedL0 (energyOperator n a j) (fractionalRootZero n a j)
      (-((a : ℂ)/(2*n))) =
      mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).conformalVector) 1 := by
  have h : (a : ℂ)/n = 2*((a : ℂ)/(2*n)) := by ring
  rw [fractionalRootZero, h]
  exact shiftedL0_inverse _ _ _

/-- A nontrivial normalized rational shift has nonintegral root pairing. -/
theorem shifted_pairing_not_integral {n : ℕ} {a : ℤ}
    (ha : 0 < a) (han : a < n) (j m : ℤ) :
    (j : ℚ) - a/n ≠ m := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  intro h
  have he : (n : ℚ)*((j : ℚ)-m)-a = 0 := by
    field_simp at h
    nlinarith
  have heZ : (n : ℤ)*(j-m)-a = 0 := by exact_mod_cast he
  exact innerCharge_ne_zero ha han (j-m) heZ

/-- Consequently the existing integral-ambient construction cannot realize
this root pairing, regardless of the chosen ambient integral lattice. -/
theorem no_integral_gluing_shift {n : ℕ} {a : ℤ}
    (ha : 0 < a) (han : a < n) (j : ℤ) (N : IntegralLattice)
    (ι : (latP 1).carrier →ₗ[ℤ] N.carrier) :
    ¬ ∃ δ : N.carrier, (N.form (ι (1 : ℤ)) δ : ℚ) = (j : ℚ)-a/n := by
  rintro ⟨δ, hδ⟩
  exact shifted_pairing_not_integral ha han j (N.form (ι (1 : ℤ)) δ) hδ.symm

end VOA.Classification.COne.OrbPos4
