/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterInterface
import VOA.Commutative.QuadraticCurrentAuxiliaryTensor
import VOA.Commutative.QuadraticCurrentGradedCarrier
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The graded auxiliary tensor split

For any quadratic current relations `Q`, the current carrier with `m` currents and `d` auxiliary
spectators satisfies, in every derivative degree `r`,

  `dim (m,d)_r ≤ Σ_{a ≤ r} dim (m,0)_a · p_{≤d}(r - a)`,

where `p_{≤d}(N)` (`A2.partitionsLe`) counts partitions of `N` into parts of size at most `d`,
i.e. `Σ_N p_{≤d}(N) q^N = 1/(q)_d` is the Hilbert series of the symmetric polynomials in `d`
variables.  This is the graded form of `currentAuxiliaryTensorEquiv`.

Proof: a carrier vector is determined by its auxiliary coefficients (`auxiliaryCoefficient_ext`),
which are constant on permutation orbits of auxiliary exponents; each orbit contains a monotone
exponent; monotone exponents of total degree `b` in `d` variables are indexed by `Idx d b`,
whose cardinality is `p_{≤d}(b)` by construction (`card_idx`); and the coefficient at an exponent
of degree `b` is homogeneous of degree `r - b` (vanishing if `b > r`).
-/

namespace VOA.DeligneAudit.SectorTensor

open VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticCurrentAuxiliaryCoefficients VOA.QuadraticCurrentAuxiliaryTensor
open VOA.DeligneAudit.A2 (partitionsLe)

noncomputable section

/-! ## Monotone exponents, indexed by partitions into parts `≤ d` -/

/-- Monotone exponent vectors of total degree `b` in `d` variables, by their first entry and the
recursive remainder. -/
def Idx : ℕ → ℕ → Type
  | 0, b => {_u : Unit // b = 0}
  | d + 1, b => Σ j : Fin (b / (d + 1) + 1), Idx d (b - j * (d + 1))

instance instFintypeIdx : ∀ d b, Fintype (Idx d b)
  | 0, b => inferInstanceAs (Fintype {_u : Unit // b = 0})
  | d + 1, b =>
      letI := fun j : Fin (b / (d + 1) + 1) => instFintypeIdx d (b - j * (d + 1))
      inferInstanceAs (Fintype (Σ j : Fin (b / (d + 1) + 1), Idx d (b - j * (d + 1))))

theorem card_idx : ∀ d b, Fintype.card (Idx d b) = partitionsLe d b
  | 0, b => by
      change Fintype.card {_u : Unit // b = 0} = _
      rw [partitionsLe]
      by_cases hb : b = 0
      · subst hb; simp
      · simp [hb]
  | d + 1, b => by
      change Fintype.card (Σ j : Fin (b / (d + 1) + 1), Idx d (b - j * (d + 1))) = _
      rw [Fintype.card_sigma, partitionsLe, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => card_idx d _

/-- The monotone exponent vector of an index. -/
def toExp : ∀ d b, Idx d b → Fin d → ℕ
  | 0, _, _ => fun i => i.elim0
  | d + 1, _, ⟨j, i⟩ => Fin.cons (j : ℕ) fun k => (j : ℕ) + toExp d _ i k

theorem sum_toExp : ∀ d b (i : Idx d b), ∑ k, toExp d b i k = b
  | 0, b, i => by simp [i.2]
  | d + 1, b, ⟨j, i⟩ => by
      have ih := sum_toExp d _ i
      have hj : (j : ℕ) * (d + 1) ≤ b := by
        have := j.isLt
        have h2 := Nat.div_mul_le_self b (d + 1)
        calc (j : ℕ) * (d + 1) ≤ (b / (d + 1)) * (d + 1) :=
              Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp this)
          _ ≤ b := h2
      rw [toExp, Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ih]
      have h1 : (j : ℕ) * (d + 1) = j + d * j := by ring
      have h2 : (d + 1) * (j : ℕ) = j + d * j := by ring
      omega

/-- Every monotone exponent vector is some `toExp`. -/
theorem exists_toExp : ∀ d (γ : Fin d → ℕ), Monotone γ → ∀ b, ∑ k, γ k = b →
    ∃ i : Idx d b, toExp d b i = γ
  | 0, γ, _, b, hb => ⟨⟨(), by simpa using hb.symm⟩, funext fun i => i.elim0⟩
  | d + 1, γ, hγ, b, hb => by
      set j := γ 0 with hj
      let γ' : Fin d → ℕ := fun k => γ k.succ - j
      have hγ' : Monotone γ' := fun a c hac =>
        Nat.sub_le_sub_right (hγ (Fin.succ_le_succ_iff.mpr hac)) _
      have hge : ∀ k, j ≤ γ k := fun k => hγ (Fin.zero_le k)
      have hsum : ∑ k, γ' k = b - j * (d + 1) := by
        have h1 : ∑ k : Fin d, (γ' k + j) = ∑ k : Fin d, γ k.succ :=
          Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hge k.succ)
        rw [Finset.sum_add_distrib] at h1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
        rw [Fin.sum_univ_succ] at hb
        rw [← hj] at hb
        have : j * (d + 1) = j + d * j := by ring
        omega
      have hjle : j * (d + 1) ≤ b := by
        rw [← hb, Fin.sum_univ_succ, ← hj]
        have : ∑ k : Fin d, j ≤ ∑ k : Fin d, γ k.succ :=
          Finset.sum_le_sum fun k _ => hge k.succ
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
        nlinarith
      have hjlt : j < b / (d + 1) + 1 :=
        Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (Nat.succ_pos d)).mpr hjle)
      obtain ⟨i, hi⟩ := exists_toExp d γ' hγ' _ hsum
      refine ⟨⟨⟨j, hjlt⟩, i⟩, ?_⟩
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [toExp, hj]
      · simp only [toExp, Fin.cons_succ, hi, γ']
        exact Nat.add_sub_cancel' (hge k.succ)

/-! ## Homogeneity of auxiliary coefficients -/

section Homogeneity

variable {K : Type*} [Field K]

theorem weight_one_eq_sum {n : ℕ} (e : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ => (1 : ℕ)) e = ∑ i, e i := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

/-- Current part of a particle exponent. -/
def curPart {m d : ℕ} (e : Fin (m + d) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => e (Fin.castAdd d i)

/-- Auxiliary part of a particle exponent. -/
def auxPart {m d : ℕ} (e : Fin (m + d) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => e (Fin.natAdd m j)

theorem weight_cur_add_aux {m d : ℕ} (e : Fin (m + d) →₀ ℕ) :
    Finsupp.weight (fun _ => (1 : ℕ)) e =
      Finsupp.weight (fun _ => (1 : ℕ)) (curPart e) +
        Finsupp.weight (fun _ => (1 : ℕ)) (auxPart e) := by
  simp only [weight_one_eq_sum, curPart, auxPart, Finsupp.coe_equivFunOnFinite_symm]
  exact Fin.sum_univ_add _

theorem split_monomial (m d : ℕ) (e : Fin (m + d) →₀ ℕ) (c : K) :
    split m d (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (auxPart e) (MvPolynomial.monomial (curPart e) c) := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.monomial_eq, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [map_mul, map_prod, map_pow, Fin.prod_univ_add, split_current_X, split_auxiliary_X,
    curPart, auxPart, Finsupp.coe_equivFunOnFinite_symm]
  have hC : split (K := K) m d (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
    simp [split]
  rw [hC]
  ring

/-- **Auxiliary coefficients of a homogeneous polynomial are homogeneous**, of the complementary
degree, and vanish when the auxiliary degree exceeds the total degree. -/
theorem coeff_split_homogeneous {m d r : ℕ} (p : MvPolynomial (Fin (m + d)) K)
    (hp : p.IsWeightedHomogeneous (fun _ => 1) r) (α : Fin d →₀ ℕ) :
    (MvPolynomial.coeff α (split m d p)).IsWeightedHomogeneous (fun _ => 1)
        (r - Finsupp.weight (fun _ => (1 : ℕ)) α) ∧
      (r < Finsupp.weight (fun _ => (1 : ℕ)) α → MvPolynomial.coeff α (split m d p) = 0) := by
  classical
  have hsum : MvPolynomial.coeff α (split m d p) = ∑ e ∈ p.support,
      if auxPart e = α then MvPolynomial.monomial (curPart e) (MvPolynomial.coeff e p) else 0 := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [split_monomial, MvPolynomial.coeff_monomial]
  have hw : ∀ e ∈ p.support, Finsupp.weight (fun _ => (1 : ℕ)) e = r := fun e he =>
    hp (MvPolynomial.mem_support_iff.mp he)
  refine ⟨?_, fun hlt => ?_⟩
  · rw [hsum]
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    split_ifs with h
    · apply MvPolynomial.isWeightedHomogeneous_monomial
      have := weight_cur_add_aux e
      rw [hw e he, h] at this
      omega
    · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · rw [hsum]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [if_neg]
    intro h
    have := weight_cur_add_aux e
    rw [hw e he, h] at this
    omega

end Homogeneity

/-! ## The graded bound -/

section Bound

variable {K σ ρ : Type*} [Field K] [Fintype σ] (Q : ρ → σ × σ → K)

/-- The exponent of an index. -/
def expOf {d b : ℕ} (i : Idx d b) : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (toExp d b i)

theorem weight_expOf {d b : ℕ} (i : Idx d b) :
    Finsupp.weight (fun _ => (1 : ℕ)) (expOf i) = b := by
  rw [weight_one_eq_sum, expOf, Finsupp.coe_equivFunOnFinite_symm]
  exact sum_toExp d b i

/-- One auxiliary coefficient, as a map of homogeneous pieces. -/
def coeffDeg (m d r b : ℕ) (α : Fin d →₀ ℕ) (hα : Finsupp.weight (fun _ => (1 : ℕ)) α = b) :
    degreePiece (currentCarrier Q m d) r →ₗ[K] degreePiece (currentCarrier Q m 0) (r - b) where
  toFun x := ⟨coefficientLinear Q m d α x.1, fun t => by
    have h := (coeff_split_homogeneous (x.1.1 t) (x.2 t) α).1
    rw [hα] at h
    exact h⟩
  map_add' x y := by
    apply Subtype.ext
    exact (coefficientLinear Q m d α).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (coefficientLinear Q m d α).map_smul c x.1

/-- All monotone auxiliary coefficients of degree at most `r`. -/
def coeffAll (m d r : ℕ) :
    degreePiece (currentCarrier Q m d) r →ₗ[K]
      ((b : Fin (r + 1)) → (i : Idx d b) → degreePiece (currentCarrier Q m 0) (r - b)) :=
  LinearMap.pi fun b => LinearMap.pi fun i => coeffDeg Q m d r b (expOf i) (weight_expOf i)

theorem auxiliaryCoefficient_perm {m d : ℕ} (x : currentCarrier Q m d)
    (h : Equiv.Perm (Fin d)) (a : Fin d →₀ ℕ) :
    auxiliaryCoefficient (a.mapDomain h) x.1 = auxiliaryCoefficient a x.1 :=
  (auxiliarySymmetric_iff_coefficients x.1).mp
    ((mem_currentCarrier_iff_coefficients Q x.1).mp x.2).1 h a

theorem coeffAll_injective (m d r : ℕ) : Function.Injective (coeffAll Q m d r) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply Subtype.ext
  apply auxiliaryCoefficient_ext
  intro β
  have h0 : auxiliaryCoefficient β (0 : TensorPolynomial (K := K) (σ := σ) m d) = 0 := by
    funext t
    simp [auxiliaryCoefficient]
  change auxiliaryCoefficient β x.1.1 = auxiliaryCoefficient β
    (0 : TensorPolynomial (K := K) (σ := σ) m d)
  rw [h0]
  set w := Finsupp.weight (fun _ => (1 : ℕ)) β with hw
  by_cases hlt : r < w
  · funext t
    exact (coeff_split_homogeneous (x.1.1 t) (x.2 t) β).2 hlt
  · let s := Tuple.sort (⇑β)
    have hmono : Monotone (⇑β ∘ s) := Tuple.monotone_sort _
    have hsum : ∑ k, (⇑β ∘ s) k = w := by
      rw [hw, weight_one_eq_sum]
      exact Equiv.sum_comp s (⇑β)
    obtain ⟨i, hi⟩ := exists_toExp d _ hmono w hsum
    have hβ : β = (expOf i).mapDomain s := by
      ext k
      rw [Finsupp.mapDomain_equiv_apply, expOf, Finsupp.coe_equivFunOnFinite_symm, hi]
      simp
    have hc := congrFun (congrFun hx ⟨w, by omega⟩) i
    have hc' := congrArg (fun y => y.1.1) hc
    change auxiliaryCoefficient (expOf i) x.1.1 = 0 at hc'
    rw [hβ, auxiliaryCoefficient_perm Q x.1 s (expOf i)]
    exact hc'

/-- **The graded auxiliary tensor bound.** -/
theorem finrank_currentCarrier_le (m d r : ℕ) :
    Module.finrank K (degreePiece (currentCarrier Q m d) r) ≤
      ∑ a ∈ Finset.range (r + 1),
        Module.finrank K (degreePiece (currentCarrier Q m 0) a) * partitionsLe d (r - a) := by
  have h := LinearMap.finrank_le_finrank_of_injective (coeffAll_injective Q m d r)
  rw [Module.finrank_pi_fintype] at h
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, card_idx,
    smul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  rw [Fin.sum_univ_eq_sum_range (fun b => partitionsLe d b *
    Module.finrank K (degreePiece (currentCarrier Q m 0) (r - b))) (r + 1),
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun a ha => ?_
  have har := Finset.mem_range.mp ha
  rw [show r - (r + 1 - 1 - a) = a by omega, show r + 1 - 1 - a = r - a by omega, mul_comm]

end Bound

end

end VOA.DeligneAudit.SectorTensor

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorTensor.card_idx
#print axioms VOA.DeligneAudit.SectorTensor.coeff_split_homogeneous
#print axioms VOA.DeligneAudit.SectorTensor.finrank_currentCarrier_le
end AxiomAudit
