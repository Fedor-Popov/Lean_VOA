import VOA.DeligneAudit.SL4TPiNilpotent
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! # The abstract cell lemma including zero cutoffs -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.CVsl2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

theorem cellFlag_step_bound_any (hS : SL2 E H F) (v : ℕ → V) (i r ν : ℕ)
    (hR : CellRelations E H F (cellFlag E H F v i) (v i) r ν) :
    FiniteDimensional ℂ ((cellFlag E H F v (i + 1)).map (cellFlag E H F v i).mkQ) ∧
      Module.finrank ℂ ((cellFlag E H F v (i + 1)).map (cellFlag E H F v i).mkQ) ≤
        ((bal r ν).map (· + 1)).prod := by
  by_cases hν : 1 ≤ ν
  · exact cellFlag_step_bound hS v i r ν hν hR
  have hν0 : ν = 0 := by omega
  subst ν
  have hst := cellFlag_stable (E := E) (H := H) (F := F) v i
  have hw : H 0 (v i) ∈ cellFlag E H F v i := by
    have he := congrArg (fun A : Module.End ℂ V => A (v i)) (hS.hEF 0 0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Nat.zero_add] at he
    rw [← he]
    exact Submodule.sub_mem _ (hst.1 0 (hR.truncated 0 le_rfl))
      (hst.2.2 0 (hR.raising 0))
  have hR0 : CellRelations E H F (cellFlag E H F v i) (v i) 0 1 := by
    refine ⟨hR.raising, ?_, hR.cartan, ?_, fun s _ => hR.truncated s (Nat.zero_le s)⟩
    · simpa using hw
    · simpa only [Nat.zero_add, pow_one] using hR.truncated 0 le_rfl
  obtain ⟨fd, hb⟩ := cellFlag_step_bound hS v i 0 1 le_rfl hR0
  refine ⟨fd, hb.trans ?_⟩
  simpa [bal] using Nat.one_le_pow r 2 (by omega)

/-- Zero cutoffs contribute at most one, including the empty alphabet. -/
theorem cellFlag_bound_any (hS : SL2 E H F) (v : ℕ → V) (r : ℕ) (ν : ℕ → ℕ) :
    ∀ n, (∀ i < n, CellRelations E H F (cellFlag E H F v i) (v i) r (ν i)) →
      FiniteDimensional ℂ (cellFlag E H F v n) ∧
        Module.finrank ℂ (cellFlag E H F v n) ≤
          ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [cellFlag_zero]
      exact ⟨inferInstance, by simp⟩
  | succ n ih =>
      intro hR
      obtain ⟨fd, bd⟩ := ih (fun i hi => hR i (by omega))
      obtain ⟨fdq, bdq⟩ := cellFlag_step_bound_any hS v n r (ν n) (hR n (by omega))
      let P := cellFlag E H F v n
      let T := cellFlag E H F v (n + 1)
      haveI : FiniteDimensional ℂ P := fd
      have hinf : T ⊓ LinearMap.ker P.mkQ ≤ P := by
        rw [Submodule.ker_mkQ]
        exact inf_le_right
      haveI : FiniteDimensional ℂ T := by
        apply Module.Finite.iff_fg.mpr
        refine Submodule.fg_of_fg_map_of_fg_inf_ker P.mkQ ?_ ?_
        · exact Module.Finite.iff_fg.mp fdq
        · exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hinf)
      refine ⟨inferInstance, ?_⟩
      have hdim := finrank_le_map_add_inf' P.mkQ T
      have hker : Module.finrank ℂ (T ⊓ LinearMap.ker P.mkQ : Submodule ℂ V) ≤
          Module.finrank ℂ P := Submodule.finrank_mono hinf
      rw [Finset.sum_range_succ]
      change Module.finrank ℂ T ≤ _
      change Module.finrank ℂ P ≤ _ at bd
      change Module.finrank ℂ (T.map P.mkQ) ≤ _ at bdq
      omega

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellFlag_step_bound_any
#print axioms VOA.DeligneAudit.SL4T.cellFlag_bound_any

/-! # The pi-form cell bound, conditional on the characteristic relation

The only additional representation-theoretic input is `PiCharacteristic`.
The nilpotence hypothesis is the precise ring input ensuring positive Cartan modes
lower the ideal flag. Both hypotheses are visible in the final theorem.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial VOA.DeligneAudit.CVsl2

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

theorem pi_prefix_le_cellFlag (π : R →ₗ[ℂ] V) (v : ℕ → R) (i : ℕ) :
    generatorPrefix v i ≤ (cellFlag E H F (fun j => π (v j)) i).comap π := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  exact cellFlag_mem _ hj

theorem pi_currentSpan_eq_cellFlag (π : R →ₗ[ℂ] V) (v : ℕ → R) (n : ℕ)
    (hspan : generatorPrefix v n = ⊤) :
    currentSpan E H F (Set.range π) = cellFlag E H F (fun i => π (v i)) n := by
  apply le_antisymm
  · apply currentSpan_le _ (cellFlag_stable _ _)
    rintro _ ⟨a, rfl⟩
    apply pi_prefix_le_cellFlag π v n
    rw [hspan]
    exact Submodule.mem_top
  · apply currentSpan_mono
    rintro _ ⟨i, _, rfl⟩
    exact ⟨v i, rfl⟩

/-- The pi-form theorem after the full one-letter Garland identity is supplied. -/
theorem pi_cellFlag_bound_of_characteristic (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (P : R[X]) (r M n : ℕ)
    (v : ℕ → R) (I : ℕ → Ideal R) (ν : ℕ → ℕ)
    (h0 : I 0 = ⊥) (htop : I n = ⊤)
    (hstep : ∀ i < n,
      (I (i + 1)).restrictScalars ℂ = (I i).restrictScalars ℂ ⊔ ℂ ∙ v i)
    (hrel : ∀ i < n, Polynomial.C (v i) * Polynomial.X ^ (ν i) ∈ (I i).map Polynomial.C ⊔
      (Ideal.span {P} ⊔ Ideal.span {Polynomial.X ^ M}))
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    (hP : PiCharacteristic F π P) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod := by
  have hprefix := idealFlag_eq_prefix v I n h0 hstep
  have himage (i : ℕ) (hi : i ≤ n) (a : R) (ha : a ∈ I i) :
      π a ∈ cellFlag E H F (fun j => π (v j)) i := by
    apply pi_prefix_le_cellFlag π v i
    rw [← hprefix i hi]
    exact ha
  have hspan : generatorPrefix v n = ⊤ := by
    rw [← hprefix n le_rfl, htop, Submodule.restrictScalars_top]
  rw [pi_currentSpan_eq_cellFlag π v n hspan]
  apply cellFlag_bound_any hS _ r ν n
  intro i hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hE]
    exact Submodule.zero_mem _
  · rw [hH0, sub_self]
    exact Submodule.zero_mem _
  · intro s hs
    rw [hH s hs]
    exact himage i (by omega) _
      (ideal_cell_nilpotent_mul (I i) (I (i + 1)) (v i) (p s) (hstep i hi) (hp s hs))
  · rw [hF0]
    exact Submodule.zero_mem _
  · exact piCurrentMap_cell F π (I i) _ P M (himage i (by omega))
      (cellFlag_stable _ i).2.2 hP hM (hrel i hi)

/-- A spanning K1 chain can be consumed directly, with no basis independence assumption. -/
theorem SpanningChain.pi_bound_of_characteristic (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (P : R[X]) (r M : ℕ) {ns : List ℕ}
    (hchain : SpanningChain (Ideal.span {P} ⊔ Ideal.span {Polynomial.X ^ M}) ⊥ ⊤ ns)
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    (hP : PiCharacteristic F π P) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range ns.length, ((bal r (ns.getD i 0)).map (· + 1)).prod := by
  obtain ⟨v, I, h0, ht, hs, hr⟩ := hchain.export
  exact pi_cellFlag_bound_of_characteristic hS π p P r M ns.length v I
    (fun i => ns.getD i 0) h0 ht hs hr hp hE hH0 hH hF0 hM hP

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.pi_prefix_le_cellFlag
#print axioms VOA.DeligneAudit.SL4T.pi_currentSpan_eq_cellFlag
#print axioms VOA.DeligneAudit.SL4T.pi_cellFlag_bound_of_characteristic
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.pi_bound_of_characteristic

/-! # Newton coefficients and their Cartan realization

`newtonCoeff p n` is the signed elementary coefficient, so its sign convention
is the coefficient of `z^n` in `exp(-sum (p_s / s) z^s)`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]

/-- Signed elementary coefficients reconstructed from power sums by Newton recursion. -/
def newtonCoeff (p : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => -(((n + 1 : ℕ) : ℂ)⁻¹) •
      ∑ i : Fin (n + 1), p (n + 1 - i.val) * newtonCoeff p i.val

/-- The corresponding Cartan operator, in the same order as the coefficient recursion. -/
def newtonEnd (H : ℕ → Module.End ℂ V) : ℕ → Module.End ℂ V
  | 0 => 1
  | n + 1 => -(((n + 1 : ℕ) : ℂ)⁻¹) •
      ∑ i : Fin (n + 1), H (n + 1 - i.val) * newtonEnd H i.val

theorem newtonCoeff_rec (p : ℕ → R) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • newtonCoeff p (n + 1) =
      -∑ i : Fin (n + 1), p (n + 1 - i.val) * newtonCoeff p i.val := by
  rw [newtonCoeff, smul_smul, mul_neg, mul_inv_cancel₀
    (show ((n + 1 : ℕ) : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)]
  simp

/-- Any coefficient sequence satisfying Newton's identity is the reconstructed sequence. -/
theorem newtonCoeff_unique (p e : ℕ → R) (h0 : e 0 = 1)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℂ) • e (n + 1) =
      -∑ i : Fin (n + 1), p (n + 1 - i.val) * e i.val) :
    ∀ n, newtonCoeff p n = e n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa only [newtonCoeff] using h0.symm
      | succ n =>
          apply (smul_right_injective R
            (show ((n + 1 : ℕ) : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n))
          dsimp only
          rw [newtonCoeff_rec, hrec]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [ih i.val i.isLt]

/-- Newton's Cartan operators act through the coefficient algebra at every input vector. -/
theorem newtonEnd_pi (H : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a)) :
    ∀ n a, newtonEnd H n (π a) = π (newtonCoeff p n * a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a
      cases n with
      | zero => simp only [newtonEnd, newtonCoeff, Module.End.one_apply, one_mul]
      | succ n =>
          simp only [newtonEnd, newtonCoeff, LinearMap.smul_apply,
            LinearMap.sum_apply, Module.End.mul_apply, smul_mul_assoc, map_smul,
            Finset.sum_mul, map_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [ih i.val i.isLt, hH _ (by have := i.isLt; omega), mul_assoc]

theorem newtonCoeff_map {T : Type*} [CommRing T] [Algebra ℂ T]
    (f : R →ₐ[ℂ] T) (p : ℕ → R) :
    ∀ n, newtonCoeff (fun s => f (p s)) n = f (newtonCoeff p n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp only [newtonCoeff, map_one]
      | succ n =>
          simp only [newtonCoeff, map_smul, map_sum, map_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [ih i.val i.isLt]

/-- Newton's identity with a range index, convenient for well-founded recursion. -/
theorem signed_esymm_newton (ι : Type*) [Fintype ι] (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) •
        ((-1) ^ (n + 1) * MvPolynomial.esymm ι ℂ (n + 1)) =
      -∑ i : Fin (n + 1), MvPolynomial.psum ι ℂ (n + 1 - i.val) *
        ((-1) ^ i.val * MvPolynomial.esymm ι ℂ i.val) := by
  classical
  have h := MvPolynomial.mul_esymm_eq_sum ι ℂ (n + 1)
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at h
  simp only [lt_self_iff_false, if_false, add_zero] at h
  have hs : (∑ i ∈ Finset.range (n + 1),
      if i < n + 1 then (-1) ^ i * MvPolynomial.esymm ι ℂ i *
        MvPolynomial.psum ι ℂ (n + 1 - i) else 0) =
      ∑ i : Fin (n + 1), (-1) ^ i.val * MvPolynomial.esymm ι ℂ i.val *
        MvPolynomial.psum ι ℂ (n + 1 - i.val) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [if_pos i.isLt]
  rw [hs] at h
  have he := congrArg (fun z : MvPolynomial ι ℂ => (-1) ^ (n + 1) * z) h
  dsimp only at he
  have hsign : (-1 : MvPolynomial ι ℂ) ^ (n + 1) * (-1) ^ (n + 1 + 1) = -1 := by
    rw [pow_succ (-1 : MvPolynomial ι ℂ) (n + 1), ← mul_assoc, ← mul_pow]
    simp
  simp only [← mul_assoc] at he
  rw [hsign, neg_one_mul] at he
  convert he using 1
  · simp only [Algebra.smul_def, map_natCast]
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The Newton coefficients really are the signed elementary symmetric polynomials. -/
theorem newtonCoeff_psum (ι : Type*) [Fintype ι] (n : ℕ) :
    newtonCoeff (MvPolynomial.psum ι ℂ) n = (-1) ^ n * MvPolynomial.esymm ι ℂ n := by
  apply newtonCoeff_unique (MvPolynomial.psum ι ℂ)
    (fun j => (-1) ^ j * MvPolynomial.esymm ι ℂ j)
  · simp
  · exact signed_esymm_newton ι

/-- The Newton identification commutes with specialization to any coefficient algebra. -/
theorem newtonCoeff_psum_map (ι : Type*) [Fintype ι]
    (f : MvPolynomial ι ℂ →ₐ[ℂ] R) (n : ℕ) :
    newtonCoeff (fun s => f (MvPolynomial.psum ι ℂ s)) n =
      (-1) ^ n * f (MvPolynomial.esymm ι ℂ n) := by
  rw [newtonCoeff_map, newtonCoeff_psum, map_mul, map_pow, map_neg, map_one]

/-- The isolated Newton-to-Cartan bridge, including its sign convention. -/
theorem newtonEnd_pi_esymm (ι : Type*) [Fintype ι]
    (f : MvPolynomial ι ℂ →ₐ[ℂ] R) (H : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (f (MvPolynomial.psum ι ℂ s) * a))
    (n : ℕ) (a : R) :
    newtonEnd H n (π a) = π (((-1) ^ n * f (MvPolynomial.esymm ι ℂ n)) * a) := by
  rw [newtonEnd_pi H π _ hH, newtonCoeff_psum_map]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_rec
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_unique
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_pi
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_map
#print axioms VOA.DeligneAudit.SL4T.signed_esymm_newton
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_psum
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_psum_map
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_pi_esymm

/-! # Garland's series step with a nontrivial Cartan factor

The correction series `L` satisfies `H(z)L(z) + L'(z) = 0` on the input vector.
This removes the zero-positive-Cartan hypothesis of `Garland.garland`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open PowerSeries VOA.DeligneAudit.Garland

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (E : Module.End ℂ V) (H F : ℕ → Module.End ℂ V)
variable (hEF : ∀ k, E * F k - F k * E = H (k + 1))
variable (hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) =
  (-2 : ℂ) • F (m + 1 + k))
variable (hFF : ∀ j k, F j * F k = F k * F j)

include hHF hFF in
theorem garland_H_series : ∀ q : ℕ,
    Hs H * Fs F ^ (q + 1) = Fs F ^ (q + 1) * Hs H -
      ((2 * (q + 1) : ℕ) : ℂ) • (Fs F ^ q * Dop (Fs F))
  | 0 => by
      simpa [sub_eq_add_neg, neg_smul] using rel_HF H F hHF
  | q + 1 => by
      have hDB : Dop (Fs F) * Fs F ^ (q + 1) = Fs F ^ (q + 1) * Dop (Fs F) :=
        (Commute.pow_right (rel_FD F hFF).symm (q + 1)).eq
      rw [pow_succ' (Fs F) (q + 1), ← mul_assoc, rel_HF H F hHF,
        add_mul, mul_assoc, garland_H_series q, mul_sub, mul_smul_comm,
        smul_mul_assoc, hDB, ← mul_assoc (Fs F) (Fs F ^ (q + 1)),
        ← pow_succ' (Fs F) (q + 1), ← mul_assoc (Fs F) (Fs F ^ q),
        ← pow_succ' (Fs F) q]
      push_cast
      module

include hEF hHF hFF in
theorem garland_E_series : ∀ q : ℕ,
    PowerSeries.C E * Fs F ^ (q + 2) =
      Fs F ^ (q + 2) * PowerSeries.C E +
        ((q + 2 : ℕ) : ℂ) • (Fs F ^ (q + 1) * Hs H) -
        (((q + 2) * (q + 1) : ℕ) : ℂ) • (Fs F ^ q * Dop (Fs F))
  | 0 => by
      rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, C_mul_pow_succ hEF,
        pow_one, rel_EF E H F hEF, mul_add,
        ← mul_assoc (Fs F) (Fs F), ← pow_two, rel_HF H F hHF]
      simp only [pow_zero, one_mul]
      norm_num
      module
  | q + 1 => by
      rw [show q + 1 + 2 = (q + 2) + 1 by omega, C_mul_pow_succ hEF,
        garland_E_series q, mul_sub, mul_add, mul_smul_comm, mul_smul_comm,
        ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← pow_succ', ← pow_succ', ← pow_succ',
        garland_H_series H F hHF hFF (q + 1)]
      push_cast
      module

include hEF hHF hFF in
theorem garland_corrected_step {w : V} (L : PowerSeries (Module.End ℂ V))
    (hE : Kills w (PowerSeries.C E * L)) (hH : Kills w (Hs H * L + Dop L))
    (q j : ℕ) :
    E ((coeff j (Fs F ^ (q + 2) * L)) w) =
      (-(((q + 2) * (j + 1) : ℕ) : ℂ)) •
        (coeff (j + 1) (Fs F ^ (q + 1) * L)) w := by
  have hk := kills_add (kills_mul_left (Fs F ^ (q + 2)) hE)
    (kills_smul ((q + 2 : ℕ) : ℂ) (kills_mul_left (Fs F ^ (q + 1)) hH))
  have heq : Fs F ^ (q + 2) * (PowerSeries.C E * L) +
      ((q + 2 : ℕ) : ℂ) • (Fs F ^ (q + 1) * (Hs H * L + Dop L)) =
      PowerSeries.C E * (Fs F ^ (q + 2) * L) +
        ((q + 2 : ℕ) : ℂ) • Dop (Fs F ^ (q + 1) * L) := by
    rw [← mul_assoc (PowerSeries.C E), garland_E_series E H F hEF hHF hFF q,
      Dop_mul, Dop_pow hFF q]
    simp only [add_mul, sub_mul, smul_mul_assoc, mul_add, smul_add, smul_smul,
      mul_assoc]
    push_cast
    module
  have h := kills_of_eq hk heq j
  rw [map_add, coeff_C_mul, coeff_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Dop, coeff_mk, LinearMap.smul_apply, smul_smul] at h
  rw [eq_neg_of_add_eq_zero_left h, ← neg_smul]
  congr 2
  push_cast
  ring

include hEF hHF hFF in
theorem garland_corrected_iter {w : V} (L : PowerSeries (Module.End ℂ V))
    (hE : Kills w (PowerSeries.C E * L)) (hH : Kills w (Hs H * L + Dop L))
    (q : ℕ) : ∀ (s j : ℕ), ∃ c : ℂ, c ≠ 0 ∧
      (E ^ s) ((coeff j (Fs F ^ (q + 1 + s) * L)) w) =
        c • (coeff (j + s) (Fs F ^ (q + 1) * L)) w
  | 0, j => ⟨1, one_ne_zero, by simp⟩
  | s + 1, j => by
      obtain ⟨c, hc, h⟩ := garland_corrected_iter L hE hH q s (j + 1)
      refine ⟨(-(((q + s + 2) * (j + 1) : ℕ) : ℂ)) * c, mul_ne_zero (by
        rw [neg_ne_zero]
        exact_mod_cast (by positivity : (q + s + 2) * (j + 1) ≠ 0)) hc, ?_⟩
      rw [pow_succ, Module.End.mul_apply, show q + 1 + (s + 1) = q + s + 2 by omega,
        garland_corrected_step E H F hEF hHF hFF L hE hH (q + s) j, map_smul,
        show q + s + 1 = q + 1 + s by omega, h, smul_smul,
        show j + 1 + s = j + (s + 1) by omega]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.garland_H_series
#print axioms VOA.DeligneAudit.SL4T.garland_E_series
#print axioms VOA.DeligneAudit.SL4T.garland_corrected_step
#print axioms VOA.DeligneAudit.SL4T.garland_corrected_iter

/-! # Garland with power-sum Cartan action at the image of a linear map -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open PowerSeries VOA.DeligneAudit.Garland VOA.DeligneAudit.CVsl2

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

def newtonSeries (H : ℕ → Module.End ℂ V) : PowerSeries (Module.End ℂ V) :=
  PowerSeries.mk (newtonEnd H)

theorem newtonSeries_raising (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hE : ∀ s a, E s (π a) = 0)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a)) (a : R) :
    Kills (π a) (PowerSeries.C (E 1) * newtonSeries H) := by
  intro n
  rw [coeff_C_mul, Module.End.mul_apply, newtonSeries, coeff_mk]
  rw [newtonEnd_pi H π p hH, hE]

theorem newtonSeries_differential (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a)) (a : R) :
    Kills (π a) (Hs H * newtonSeries H + Dop (newtonSeries H)) := by
  intro n
  have hHs (k : ℕ) (b : R) : H (k + 1) (π b) = π (p (k + 1) * b) :=
    hH (k + 1) (by omega) b
  have hs : (coeff n (Hs H * newtonSeries H)) (π a) =
      π ((∑ i : Fin (n + 1), p (n + 1 - i.val) * newtonCoeff p i.val) * a) := by
    rw [coeff_mul, LinearMap.sum_apply]
    simp only [Hs, newtonSeries, coeff_mk, Module.End.mul_apply,
      newtonEnd_pi H π p hH, hHs]
    have hswap := Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun x : ℕ × ℕ => π (p (x.2 + 1) * (newtonCoeff p x.1 * a)))
    simp only [Prod.fst_swap, Prod.snd_swap] at hswap
    rw [hswap]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Fin.sum_univ_eq_sum_range, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show n - i.val + 1 = n + 1 - i.val by have := i.isLt; omega, mul_assoc]
  rw [map_add, LinearMap.add_apply, hs, Dop, coeff_mk, LinearMap.smul_apply]
  rw [newtonSeries, coeff_mk]
  rw [newtonEnd_pi H π p hH, ← map_smul, ← smul_mul_assoc,
    newtonCoeff_rec, neg_mul, map_neg, add_neg_cancel]

/-- The general Garland coefficient vanishing with the full Cartan correction. -/
theorem garland_pi_coeff (hS : SL2 E H F) (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hE : ∀ s a, E s (π a) = 0)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (r : ℕ) (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (k s : ℕ) (hk : 1 ≤ k) (hs : r + 1 ≤ k + s) (a : R) :
    (coeff s (Fs F ^ k * newtonSeries H)) (π a) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hEF (j : ℕ) : E 1 * F j - F j * E 1 = H (j + 1) := by
    simpa only [Nat.add_comm] using hS.hEF 1 j
  obtain ⟨c, hc, he⟩ := garland_corrected_iter (E 1) H F hEF
    (fun m j => hS.hHF (m + 1) j) hS.hFF (newtonSeries H)
    (newtonSeries_raising π p hE hH a) (newtonSeries_differential π p hH a) q s 0
  have hz : (coeff 0 (Fs F ^ (q + 1 + s) * newtonSeries H)) (π a) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_pow]
    simp only [Fs, newtonSeries, constantCoeff_mk, newtonEnd, mul_one]
    rw [show q + 1 + s = (q + 1 + s - (r + 1)) + (r + 1) by omega,
      pow_add, Module.End.mul_apply, hF0, map_zero]
  rw [hz, map_zero, zero_add, eq_comm, smul_eq_zero] at he
  exact he.resolve_left hc

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.newtonSeries_raising
#print axioms VOA.DeligneAudit.SL4T.newtonSeries_differential
#print axioms VOA.DeligneAudit.SL4T.garland_pi_coeff

/-! # The characteristic-polynomial relation from the corrected Garland identity -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial VOA.DeligneAudit.Garland VOA.DeligneAudit.CVsl2

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- The one-letter Garland recurrence, with the full coefficient algebra retained. -/
theorem garland_pi_one (hS : SL2 E H F) (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hE : ∀ s a, E s (π a) = 0)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (r : ℕ) (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (htail : ∀ j, r < j → newtonCoeff p j = 0) (k : ℕ) (a : R) :
    ∑ j ∈ Finset.range (r + 1), F (r - j + k) (π (newtonCoeff p j * a)) = 0 := by
  have h := garland_pi_coeff hS π p hE hH r hF0 1 (r + k) (by omega) (by omega) a
  rw [pow_one, PowerSeries.coeff_mul, LinearMap.sum_apply] at h
  simp only [Fs, newtonSeries, PowerSeries.coeff_mk, Module.End.mul_apply,
    newtonEnd_pi H π p hH] at h
  have hswap := Finset.Nat.sum_antidiagonal_swap (n := r + k)
    (f := fun x : ℕ × ℕ => F x.2 (π (newtonCoeff p x.1 * a)))
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [hswap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have heq : (∑ j ∈ Finset.range (r + 1),
      F (r + k - j) (π (newtonCoeff p j * a))) =
      ∑ j ∈ Finset.range (r + k + 1), F (r + k - j) (π (newtonCoeff p j * a)) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hjr : r < j := by
      have := Nat.not_lt.mp (fun hj' => hj (Finset.mem_range.mpr hj'))
      omega
    rw [htail j hjr, zero_mul, map_zero, map_zero]
  rw [← heq] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r - j + k = r + k - j by have := Finset.mem_range.mp hj; omega]

/-- Garland annihilates every polynomial multiple of the characteristic polynomial. -/
theorem piCharacteristic_of_highest (hS : SL2 E H F) (π : R →ₗ[ℂ] V) (p : ℕ → R)
    (hE : ∀ s a, E s (π a) = 0)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (r : ℕ) (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (htail : ∀ j, r < j → newtonCoeff p j = 0) :
    PiCharacteristic F π (descendingPoly (newtonCoeff p) r) := by
  intro a k
  rw [descendingPoly_eq_sum, Finset.mul_sum, map_sum]
  convert garland_pi_one hS π p hE hH r hF0 htail k a using 1
  apply Finset.sum_congr rfl
  intro j _
  have heq : Polynomial.C a * Polynomial.X ^ k *
      (Polynomial.C (newtonCoeff p j) * Polynomial.X ^ (r - j)) =
      Polynomial.C (newtonCoeff p j * a) * Polynomial.X ^ (r - j + k) := by
    rw [map_mul, pow_add]
    ring
  rw [heq, piCurrentMap_C_mul_X_pow]

/-- Theorem C in pi-form, including zero cell cutoffs.

The ring hypotheses express that the alphabet has `r` letters and its positive power sums
are nilpotent. No characteristic relation is assumed: it is proved by Garland above.
-/
theorem pi_cellFlag_bound (hS : SL2 E H F)
    (π : R →ₗ[ℂ] V) (p : ℕ → R) (r M n : ℕ)
    (v : ℕ → R) (I : ℕ → Ideal R) (ν : ℕ → ℕ)
    (h0 : I 0 = ⊥) (htop : I n = ⊤)
    (hstep : ∀ i < n,
      (I (i + 1)).restrictScalars ℂ = (I i).restrictScalars ℂ ⊔ ℂ ∙ v i)
    (hrel : ∀ i < n, Polynomial.C (v i) * Polynomial.X ^ (ν i) ∈
      (I i).map Polynomial.C ⊔
        (Ideal.span {descendingPoly (newtonCoeff p) r} ⊔ Ideal.span {Polynomial.X ^ M}))
    (hp : ∀ s, 1 ≤ s → IsNilpotent (p s))
    (htail : ∀ j, r < j → newtonCoeff p j = 0)
    (hE : ∀ s a, E s (π a) = 0)
    (hH0 : ∀ a, H 0 (π a) = (r : ℂ) • π a)
    (hH : ∀ s, 1 ≤ s → ∀ a, H s (π a) = π (p s * a))
    (hF0 : ∀ a, (F 0 ^ (r + 1)) (π a) = 0)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ i ∈ Finset.range n, ((bal r (ν i)).map (· + 1)).prod :=
  pi_cellFlag_bound_of_characteristic hS π p (descendingPoly (newtonCoeff p) r)
    r M n v I ν h0 htop hstep hrel hp hE hH0 hH hF0 hM
    (piCharacteristic_of_highest hS π p hE hH r hF0 htail)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.garland_pi_one
#print axioms VOA.DeligneAudit.SL4T.piCharacteristic_of_highest
#print axioms VOA.DeligneAudit.SL4T.pi_cellFlag_bound

