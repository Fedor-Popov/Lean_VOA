/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorPairAssembly

/-!
# `PairComparison` and `DivisorComparison` for A₂, proved

The factor `H⁴ F = (G_a G_b)⁴ ∏_{j∉{a,b}} D_j³` divides `E_{ab}^{8 + 3m}`: `G_a`, `G_b` and each `D_j`
(`j ∉ {a,b}`) are rows of the product `E_{ab} = ∏_{i ≠ j, {i,j} ≠ {a,b}} (z_i - z_j)`.  With
`good_pairTable` and `tensor_eq_sum_emb` this gives **`pairComparison`**, and with
`divisorComparison_of_pair`, **`divisorComparison : DivisorComparison`** (B8 at `(Δ)`).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable {m : ℕ}

/-- The `i`-th row of `E_{ab}`. -/
def rowE (a b i : Fin m) : Pm m :=
  ∏ j : Fin m, if i = j ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else (X i - X j)

theorem rowE_dvd (a b i : Fin m) : rowE a b i ∣ pairE (m := m) a b :=
  Finset.dvd_prod_of_mem (fun i => rowE a b i) (Finset.mem_univ i)

theorem zr_eq (i : Fin m) : (zr (K := ℂ) i : Pm m) = X i := rfl

theorem Gpair_eq (a b i : Fin m) :
    Gpair a b i = ∏ j : Fin m, if j = a ∨ j = b then 1 else (X i - X j) := by
  rw [Gpair, Lpair, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [zr_eq]

theorem Gpair_a_dvd (a b : Fin m) (hab : a ≠ b) : Gpair a b a ∣ pairE (m := m) a b := by
  refine dvd_trans (dvd_of_eq ?_) (rowE_dvd a b a)
  rw [Gpair_eq, rowE]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h1 : j = a
  · subst h1; simp
  · by_cases h2 : j = b
    · subst h2; simp
    · rw [if_neg (by tauto), if_neg]
      rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
      · exact h1 h.symm
      · exact h2 h
      · exact hab h

theorem Gpair_b_dvd (a b : Fin m) (hab : a ≠ b) : Gpair a b b ∣ pairE (m := m) a b := by
  refine dvd_trans (dvd_of_eq ?_) (rowE_dvd a b b)
  rw [Gpair_eq, rowE]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h1 : j = a
  · subst h1; simp
  · by_cases h2 : j = b
    · subst h2; simp
    · rw [if_neg (by tauto), if_neg]
      rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
      · exact h2 h.symm
      · exact hab h.symm
      · exact h1 h

theorem Dslot_dvd (a b j : Fin m) (hja : j ≠ a) (hjb : j ≠ b) : Dslot j ∣ pairE (m := m) a b := by
  refine dvd_trans (dvd_of_eq ?_) (rowE_dvd a b j)
  rw [Dslot, rowE]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk; simp
  · rw [if_neg hk, if_neg]
    · rfl
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact hk h.symm
      · exact hja h
      · exact hjb h

theorem factor_dvd (a b : Fin m) (hab : a ≠ b) :
    Hpair a b ^ 4 * Fspec a b ∣ pairE (m := m) a b ^ (8 + 3 * m) := by
  rw [pow_add]
  apply mul_dvd_mul
  · rw [Hpair, mul_pow, show 8 = 4 + 4 by rfl, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (Gpair_a_dvd a b hab) 4)
      (pow_dvd_pow_of_dvd (Gpair_b_dvd a b hab) 4)
  · rw [Fspec]
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ (fun _ => pairE (m := m) a b ^ 3)
      fun j hj => ?_) ?_
    · simp only [Finset.mem_filter] at hj
      exact pow_dvd_pow_of_dvd (Dslot_dvd a b j hj.2.1 hj.2.2) 3
    · rw [Finset.prod_const, ← pow_mul]
      apply pow_dvd_pow
      have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => j ≠ a ∧ j ≠ b)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega

/-- **`PairComparison` holds** (B7 at the divisor). -/
theorem pairComparison : PairComparison := by
  refine ⟨fun m x hx a b hab => ⟨8 + 3 * m, ?_⟩⟩
  rw [tensor_eq_sum_emb x a b hab, Finset.smul_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hcan : IsCanon a b s := (Finset.mem_filter.mp hs).2
  obtain ⟨k, hk⟩ := factor_dvd (m := m) a b hab
  have hg := good_pairTable hab hcan hx
  change emb a b s ((Hpair a b ^ 4 * Fspec a b) • pairTable x a b s) ∈ MP m at hg
  rw [emb_smul] at hg
  rw [hk, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hg

/-- **`DivisorComparison` holds** (B8 at `(Δ)`). -/
theorem divisorComparison : DivisorComparison := divisorComparison_of_pair pairComparison

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.pairComparison
#print axioms VOA.DeligneAudit.A2.divisorComparison
end AxiomAudit
