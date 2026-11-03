import VOA.DeligneAudit.D4FusionToroidalFusionPolynomial
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The uniform recurrence for `h_N(z_S)` (★b, scalar part for all `j`)

For `S ⊆ Fin m` let `H_S = ∏_{q ∈ S} (1 − z_q X)^{-1}` (coefficients `h_N(z_S)`) and
`E_S = ∏_{q ∈ S} (1 − z_q X)`.  Then `H_S · E_{all} = E_{Sᶜ}` is a polynomial of degree
`≤ m − |S|`, so for `N > m − |S|`

`∑_{a+s=N} h_a(z_S) c̃_s = 0`,  `c̃_s = [X^s] E_{all}`, `c̃_0 = 1`  (`HS_recurrence`).

Hence on injective `k`-tuples `p : Fin k → Fin m` the function `p ↦ h_N(z ∘ p)` is a
combination of `p ↦ h_a(z ∘ p)`, `a < N`, with constant coefficients, and therefore lies in the
span of the monomial functions of total degree `< N`, up to a function vanishing on injective
tuples (`hvecT_mem`).  This is the scalar input for `P^{(j)}_N v_F = 0`, `N ≥ m − j`,
`k = j + 1`.
-/

namespace VOA.DeligneAudit.Toroidal.StarB2

open Finset PowerSeries

noncomputable section

section Series

/-- The geometric series `∑ a^n X^n`. -/
def geo (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => a ^ n

theorem one_sub_mul_geo (a : ℂ) : (1 - PowerSeries.C a * X) * geo a = 1 := by
  ext n
  rcases n with _ | n
  · rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, sub_zero,
      geo, coeff_mk, pow_zero, coeff_zero_one]
  · rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul, geo, coeff_mk,
      coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

variable {m : ℕ} (z : Fin m → ℂ)

/-- `H_S = ∏_{q ∈ S} geo (z q)`; its coefficients are `h_N(z_S)`. -/
def HS (S : Finset (Fin m)) : PowerSeries ℂ := ∏ q ∈ S, geo (z q)

/-- `E_S = ∏_{q ∈ S} (1 − z_q X)`. -/
def ES (S : Finset (Fin m)) : PowerSeries ℂ := ∏ q ∈ S, (1 - PowerSeries.C (z q) * X)

theorem ES_mul_HS (S : Finset (Fin m)) : ES z S * HS z S = 1 := by
  rw [ES, HS, ← prod_mul_distrib]
  exact prod_eq_one fun q _ => one_sub_mul_geo (z q)

theorem coeff_ES_zero (S : Finset (Fin m)) : coeff 0 (ES z S) = 1 := by
  simp [ES, coeff_zero_eq_constantCoeff, map_prod]

theorem coeff_ES_high (S : Finset (Fin m)) : ∀ N, S.card < N → coeff N (ES z S) = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro N hN
    rw [card_empty] at hN
    rw [ES, prod_empty, coeff_one, if_neg (by omega)]
  | insert a S ha ih =>
    intro N hN
    rw [card_insert_of_notMem ha] at hN
    rw [ES, prod_insert ha, ← ES]
    rcases N with _ | N
    · omega
    · rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul,
        ih (N + 1) (by omega), ih N (by omega), mul_zero, sub_zero]

theorem ES_univ_eq (S : Finset (Fin m)) : ES z univ = ES z S * ES z Sᶜ := by
  rw [ES, ES, ES, prod_mul_prod_compl]

/-- **The uniform recurrence**: for `|S| + N > m`, `∑_{a+s=N} h_a(z_S) c̃_s = 0`. -/
theorem HS_recurrence (S : Finset (Fin m)) (N : ℕ) (hN : m < S.card + N) :
    ∑ p ∈ antidiagonal N, coeff p.1 (HS z S) * coeff p.2 (ES z univ) = 0 := by
  rw [← coeff_mul, ES_univ_eq z S, ← mul_assoc, mul_comm (HS z S), ES_mul_HS, one_mul]
  apply coeff_ES_high
  have hS : S.card ≤ m := by simpa using Finset.card_le_univ S
  rw [card_compl, Fintype.card_fin]
  omega

/-! ## Functions on `k`-tuples of sites -/

/-- `h_N(z ∘ p)` for a tuple `p`. -/
def hT (k : ℕ) (p : Fin k → Fin m) (N : ℕ) : ℂ := coeff N (∏ i, geo (z (p i)))

theorem hT_eq_HS (k : ℕ) (p : Fin k → Fin m) (hp : Function.Injective p) (N : ℕ) :
    hT z k p N = coeff N (HS z (univ.image p)) := by
  rw [hT, HS, prod_image (fun x _ y _ h => hp h)]

/-- The monomial function `p ↦ ∏_i z_{p i}^{l i}`. -/
def monT (k : ℕ) (l : Fin k → ℕ) : (Fin k → Fin m) → ℂ := fun p => ∏ i, z (p i) ^ l i

/-- Functions spanned by the monomials of total degree `< N`. -/
def lowSpanT (k N : ℕ) : Submodule ℂ ((Fin k → Fin m) → ℂ) :=
  Submodule.span ℂ {φ | ∃ l : Fin k → ℕ, ∑ i, l i < N ∧ φ = monT z k l}

/-- Functions vanishing on injective tuples. -/
def NI (k : ℕ) : Submodule ℂ ((Fin k → Fin m) → ℂ) where
  carrier := {φ | ∀ p, Function.Injective p → φ p = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ p hp
    simp [hφ p hp, hψ p hp]
  smul_mem' := by
    intro a φ hφ p hp
    simp [hφ p hp]

/-- The function `p ↦ h_N(z ∘ p)`. -/
def hvecT (k N : ℕ) : (Fin k → Fin m) → ℂ := fun p => hT z k p N

theorem hvecT_eq_sum (k N : ℕ) :
    hvecT z k N =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin k)) N, monT z k (fun i => l i) := by
  funext p
  simp only [hvecT, hT, coeff_prod, Finset.sum_apply, monT, geo, coeff_mk]

theorem hvecT_mem_of_lt (k a N : ℕ) (h : a < N) : hvecT z k a ∈ lowSpanT z k N := by
  rw [hvecT_eq_sum]
  refine Submodule.sum_mem _ fun l hl => ?_
  rw [mem_finsuppAntidiag] at hl
  exact Submodule.subset_span ⟨fun i => l i, by rw [hl.1]; exact h, rfl⟩

/-- **The scalar reduction on tuples**: for `k + N > m` (and `N ≥ 1`), `p ↦ h_N(z ∘ p)`
lies in the span of the monomials of degree `< N`, up to a function vanishing on injective
tuples. -/
theorem hvecT_mem (k N : ℕ) (hN : m < k + N) (hN0 : 1 ≤ N) :
    hvecT z k N ∈ lowSpanT z k N ⊔ NI k := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  set ν : (Fin k → Fin m) → ℂ := hvecT z k (N' + 1) +
    ∑ p ∈ antidiagonal N', coeff (p.2 + 1) (ES z univ) • hvecT z k p.1 with hνdef
  have hν : ν ∈ NI k := by
    intro p hp
    simp only [hνdef, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvecT,
      hT_eq_HS z k p hp]
    have hrec := HS_recurrence z (univ.image p) (N' + 1) (by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
      omega)
    rw [Nat.sum_antidiagonal_succ', coeff_ES_zero, mul_one] at hrec
    rw [← hrec]
    congr 1
    exact sum_congr rfl fun q _ => mul_comm _ _
  have hsplit : hvecT z k (N' + 1) =
      ν - ∑ p ∈ antidiagonal N', coeff (p.2 + 1) (ES z univ) • hvecT z k p.1 := by
    rw [hνdef]
    abel
  rw [hsplit]
  refine Submodule.sub_mem _ (Submodule.mem_sup_right hν) (Submodule.mem_sup_left ?_)
  refine Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ ?_
  have := mem_antidiagonal.mp hp
  exact hvecT_mem_of_lt z k p.1 (N' + 1) (by omega)

end Series

end

end VOA.DeligneAudit.Toroidal.StarB2

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.StarB2.HS_recurrence
#print axioms VOA.DeligneAudit.Toroidal.StarB2.hvecT_mem
end AxiomAudit
