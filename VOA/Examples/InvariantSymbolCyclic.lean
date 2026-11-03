import VOA.Examples.LeeYangTransferAssemblyCharacter
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The cyclic-evaluation bound for invariant symbols

This file proves the purely algebraic half of the invariant-symbol upper bound

  `dim ((gr_r A) ⊗ L_1)^{sl2[t]}_N ≤ [z^N] z^{r(r+1)} / ∏_{j ≤ r} (1 - z^j)`

(`= gapTwoCoefficient N r`), following the inverse-system argument of the coset global-fusion strictness proof
(dual orientation; highest-weight algebra relations).

Setting. Variables are indexed by `m : ℕ` and stand for the mode `m + 1`:
* `C[H_1, H_2, …] = MvPolynomial ℕ ℂ`, `H_{m+1}` of weight `m + 1`;
* the charge-`r` oscillator space of the level-one lattice module, `C[a_1, a_2, …]`, is the
  same `MvPolynomial ℕ ℂ`, `a_{m+1}` of weight `m + 1` (energy `r² + r + weight` after the shift
  by the source degree `r`);
* the Cartan evaluation `H_m ↦ 2 p_m(s_1,…,s_r)` (`cartanEval`), whose kernel is the
  symmetric-center Cartan ideal `I_r` (`cartanIdeal`, relation (A1) of the note);
* the perfect pairing `⟨F, P⟩` (`modePairing`), the value of `F(2∂_{a_1}, 4∂_{a_2}, …) P` at
  matching weighted degree (`∂^k a^k = k!`).

`finrank_le_gapTwoCoefficient_of_cyclicEvaluation`: a space `V` with an injective linear map
`ev : V → C[a]` landing in weighted degree `N - r(r+1)`, whose image is annihilated by the
pairing with the degree-matching part of `I_r`, has `dim V ≤ gapTwoCoefficient N r`.
Proved outright (Mathlib axioms only).

The physical inputs that produce `ev` — the identification of `gr_R A` with the restricted
dual of the cyclic global module with the Cartan relations (input (A) of the note), the
level-one lattice realization of the charge-`r` sector, and equivariance of evaluation at the
cyclic vector — are **not** formalized in this file; see `InvariantSymbolAssembly`. They are
proved for the Lee–Yang endpoint (the lattice realization replaced by the intrinsic Heisenberg
separation) in the `CyclicEval*`, `SymbolModel*`, `KoszulConcrete*` and `KoszulResidual*` files,
assembled in `TwoSeries.leeYang_symbolBound` (`TwoSeriesLeeYang.lean`).
-/

namespace VOA.InvariantSymbol

open MvPolynomial Module
open scoped BigOperators

noncomputable section

/-! ### Antitone tuples and gap-two multiplicity tuples -/

/-- Extension of a tuple by zero. -/
def extTuple {r : ℕ} (β : Fin r → ℕ) (i : ℕ) : ℕ := if h : i < r then β ⟨i, h⟩ else 0

theorem extTuple_of_lt {r : ℕ} (β : Fin r → ℕ) (i : Fin r) : extTuple β i = β i := by
  simp [extTuple, i.isLt]

theorem extTuple_r {r : ℕ} (β : Fin r → ℕ) : extTuple β r = 0 := by simp [extTuple]

theorem extTuple_antitone {r : ℕ} (β : Fin r → ℕ) (hβ : Antitone β) : Antitone (extTuple β) := by
  intro i j hij
  unfold extTuple
  by_cases hj : j < r
  · rw [dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    exact hβ (Fin.mk_le_mk.mpr hij)
  · rw [dif_neg hj]; exact Nat.zero_le _

/-- Telescoping for an antitone sequence. -/
theorem telescope (b : ℕ → ℕ) (hb : Antitone b) (n : ℕ) :
    ∑ j ∈ Finset.range n, (j + 1) * (b j - b (j + 1)) + n * b n =
      ∑ j ∈ Finset.range n, b j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    have h1 : b (n + 1) ≤ b n := hb (Nat.le_succ n)
    have h2 : (n + 1) * (b n - b (n + 1)) + (n + 1) * b (n + 1) = (n + 1) * b n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h1]
    have h3 : ((n + 1 : ℕ) : ℕ) = n + 1 := rfl
    calc ∑ j ∈ Finset.range n, (j + 1) * (b j - b (j + 1)) + (n + 1) * (b n - b (n + 1)) +
          (n + 1) * b (n + 1)
        = ∑ j ∈ Finset.range n, (j + 1) * (b j - b (j + 1)) + (n + 1) * b n := by
          rw [add_assoc, h2]
      _ = ∑ j ∈ Finset.range n, (j + 1) * (b j - b (j + 1)) + n * b n + b n := by ring

theorem sum_extTuple {r : ℕ} (β : Fin r → ℕ) :
    ∑ j ∈ Finset.range r, extTuple β j = ∑ i, β i := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => extTuple_of_lt β i

/-- Weakly decreasing exponent vectors of total degree `D` in `r` variables. -/
def Sorted (r D : ℕ) : Type :=
  {β : Fin r → Fin (D + 1) // Antitone (fun i => (β i : ℕ)) ∧ ∑ i, (β i : ℕ) = D}

instance (r D : ℕ) : Finite (Sorted r D) := Subtype.finite

/-- The index type of `gapTwoCoefficient`. -/
def GapTuples (N : ℤ) (r : ℕ) : Type :=
  {a : Fin r → Fin (N.toNat + 1) //
    ((r * (r + 1) + ∑ j : Fin r, (j.val + 1) * (a j).val : ℕ) : ℤ) = N}

instance (N : ℤ) (r : ℕ) : Finite (GapTuples N r) := Subtype.finite

theorem gapTwoCoefficient_eq_card (N : ℤ) (r : ℕ) :
    LeeYangTransferAssembly.gapTwoCoefficient N r = Nat.card (GapTuples N r) := by
  classical
  unfold LeeYangTransferAssembly.gapTwoCoefficient
  exact Fintype.card_eq_nat_card

/-- Differences of an antitone tuple, as a gap-two multiplicity tuple. -/
def toGap {N : ℤ} {r D : ℕ} (hD : ((r * (r + 1) + D : ℕ) : ℤ) = N) (β : Sorted r D) :
    GapTuples N r :=
  ⟨fun j => ⟨extTuple (fun i => (β.1 i : ℕ)) j - extTuple (fun i => (β.1 i : ℕ)) (j + 1), by
      have h1 : extTuple (fun i => (β.1 i : ℕ)) j ≤ D := by
        unfold extTuple
        split_ifs
        · exact Nat.lt_succ_iff.mp (β.1 _).isLt
        · exact Nat.zero_le _
      omega⟩, by
    have hb := extTuple_antitone _ β.2.1
    have ht := telescope _ hb r
    rw [extTuple_r, mul_zero, add_zero, sum_extTuple, β.2.2] at ht
    have hsum : r * (r + 1) + ∑ j : Fin r, ((j : ℕ) + 1) * (extTuple (fun i => (β.1 i : ℕ)) j -
        extTuple (fun i => (β.1 i : ℕ)) (j + 1)) = r * (r + 1) + D := by
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun j => (j + 1) *
        (extTuple (fun i => (β.1 i : ℕ)) j - extTuple (fun i => (β.1 i : ℕ)) (j + 1)))]
      exact ht
    change ((r * (r + 1) + ∑ j : Fin r, ((j : ℕ) + 1) * (extTuple (fun i => (β.1 i : ℕ)) j -
        extTuple (fun i => (β.1 i : ℕ)) (j + 1)) : ℕ) : ℤ) = N
    rw [hsum]; exact hD⟩

theorem toGap_injective {N : ℤ} {r D : ℕ} (hD : ((r * (r + 1) + D : ℕ) : ℤ) = N) :
    Function.Injective (toGap hD) := by
  intro β γ h
  set b := extTuple (fun i => (β.1 i : ℕ))
  set c := extTuple (fun i => (γ.1 i : ℕ))
  have hb := extTuple_antitone _ β.2.1
  have hc := extTuple_antitone _ γ.2.1
  have hdiff : ∀ j < r, b j - b (j + 1) = c j - c (j + 1) := by
    intro j hj
    have := congrArg (fun a : GapTuples N r => ((a.1 ⟨j, hj⟩ : Fin _) : ℕ)) h
    exact this
  have key : ∀ k ≤ r, b (r - k) = c (r - k) := by
    intro k
    induction k with
    | zero => intro _; simp [b, c, extTuple_r]
    | succ k ih =>
      intro hk
      have hj : r - (k + 1) < r := by omega
      have hj1 : r - (k + 1) + 1 = r - k := by omega
      have e1 := hdiff _ hj
      rw [hj1] at e1
      have hb1 : b (r - k) ≤ b (r - (k + 1)) := hb (by omega)
      have hc1 : c (r - k) ≤ c (r - (k + 1)) := hc (by omega)
      have := ih (by omega)
      omega
  apply Subtype.ext
  funext i
  apply Fin.ext
  have := key (r - i) (by omega)
  rw [show r - (r - (i : ℕ)) = i by omega] at this
  simpa [b, c, extTuple_of_lt] using this

theorem card_sorted_le {N : ℤ} {r D : ℕ} (hD : ((r * (r + 1) + D : ℕ) : ℤ) = N) :
    Nat.card (Sorted r D) ≤ LeeYangTransferAssembly.gapTwoCoefficient N r := by
  rw [gapTwoCoefficient_eq_card]
  exact Nat.card_le_card_of_injective _ (toGap_injective hD)

/-! ### The Cartan evaluation and the symmetric-center ideal -/

/-- Mode weights `m ↦ m + 1`, in `ℕ` and in `ℤ`. -/
def modeWeight (m : ℕ) : ℕ := m + 1
def modeWeightZ (m : ℕ) : ℤ := (m : ℤ) + 1

theorem weight_modeWeightZ (α : ℕ →₀ ℕ) :
    Finsupp.weight modeWeightZ α = (Finsupp.weight modeWeight α : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, modeWeightZ, modeWeight, Nat.cast_sum,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem weight_modeWeightZ_nonneg (α : ℕ →₀ ℕ) : 0 ≤ Finsupp.weight modeWeightZ α := by
  rw [weight_modeWeightZ]; exact Nat.cast_nonneg _

/-- The generator images `H_{m+1} ↦ 2 p_{m+1}(s_1, …, s_r)`. -/
def cartanGen (r m : ℕ) : MvPolynomial (Fin r) ℂ := MvPolynomial.C 2 * psum (Fin r) ℂ (m + 1)

/-- The Cartan evaluation `C[H_1, H_2, …] → C[s_1, …, s_r]^{S_r}`. -/
def cartanEval (r : ℕ) : MvPolynomial ℕ ℂ →ₐ[ℂ] MvPolynomial (Fin r) ℂ := aeval (cartanGen r)

/-- The symmetric-center Cartan ideal `I_r = ker (H_m ↦ 2 Σ_i s_i^m)`. -/
def cartanIdeal (r : ℕ) : Ideal (MvPolynomial ℕ ℂ) := RingHom.ker (cartanEval r)

theorem cartanGen_isSymmetric (r m : ℕ) : (cartanGen r m).IsSymmetric :=
  (IsSymmetric.C 2).mul (psum_isSymmetric _ _ _)

theorem cartanEval_isSymmetric (r : ℕ) (F : MvPolynomial ℕ ℂ) : (cartanEval r F).IsSymmetric := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [cartanEval, aeval_C]; exact IsSymmetric.C a
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p n hp => rw [map_mul, cartanEval, aeval_X]; exact hp.mul (cartanGen_isSymmetric r n)

theorem cartanGen_isHomogeneous (r m : ℕ) : (cartanGen r m).IsHomogeneous (m + 1) := by
  have h : (psum (Fin r) ℂ (m + 1)).IsHomogeneous (m + 1) :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i (m + 1)
  simpa using (isHomogeneous_C (Fin r) (2 : ℂ)).mul h

theorem cartanEval_monomial_isHomogeneous (r : ℕ) (α : ℕ →₀ ℕ) (c : ℂ) :
    (cartanEval r (monomial α c)).IsHomogeneous (Finsupp.weight modeWeight α) := by
  rw [cartanEval, aeval_monomial, Finsupp.prod]
  have hp := IsHomogeneous.prod α.support (fun i => cartanGen r i ^ α i)
    (fun i => (i + 1) * α i) fun i _ => (cartanGen_isHomogeneous r i).pow (α i)
  have hw : Finsupp.weight modeWeight α = 0 + ∑ i ∈ α.support, (i + 1) * α i := by
    rw [Finsupp.weight_apply, Finsupp.sum, zero_add]
    exact Finset.sum_congr rfl fun i _ => by simp [modeWeight, mul_comm]
  rw [hw]
  exact (isHomogeneous_C (Fin r) c).mul hp

theorem cartanEval_isHomogeneous (r D : ℕ) (F : MvPolynomial ℕ ℂ)
    (hF : IsWeightedHomogeneous modeWeightZ F (D : ℤ)) :
    (cartanEval r F).IsHomogeneous D := by
  rw [F.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun α hα => ?_
  have hw := hF (mem_support_iff.mp hα)
  rw [weight_modeWeightZ] at hw
  have hw' : Finsupp.weight modeWeight α = D := by exact_mod_cast hw
  rw [← hw']
  exact cartanEval_monomial_isHomogeneous r α _

/-- The exponent vector of a sorted tuple. -/
def sortedExp {r D : ℕ} (β : Sorted r D) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (β.1 i : ℕ)

/-- A symmetric homogeneous polynomial of degree `D` vanishing at all weakly decreasing
exponent vectors is zero. -/
theorem eq_zero_of_sorted_coeff {r D : ℕ} (φ : MvPolynomial (Fin r) ℂ) (hs : φ.IsSymmetric)
    (hh : φ.IsHomogeneous D) (h : ∀ β : Sorted r D, coeff (sortedExp β) φ = 0) : φ = 0 := by
  ext γ
  rw [coeff_zero]
  by_contra hne
  have hdeg : ∑ i, γ i = D := by
    have h1 := hh hne
    have h2 : Finsupp.degree γ = D := by rw [Finsupp.degree_eq_weight_one]; exact h1
    rwa [Finsupp.degree_eq_sum] at h2
  let g : Fin r → ℕ := γ
  let τ : Equiv.Perm (Fin r) := Fin.revPerm.trans (Tuple.sort g)
  have hanti : Antitone (g ∘ τ) := by
    intro i j hij
    have hm := Tuple.monotone_sort g
    exact hm (Fin.rev_le_rev.mpr hij)
  have hsum : ∑ i, g (τ i) = D := by
    rw [Equiv.sum_comp τ g]; exact hdeg
  have hle : ∀ i, g (τ i) < D + 1 := by
    intro i
    have := Finset.single_le_sum (s := Finset.univ) (f := fun i => g (τ i))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only at this
    omega
  let β : Sorted r D := ⟨fun i => ⟨g (τ i), hle i⟩, hanti, hsum⟩
  have hβ := h β
  have hmap : (sortedExp β).mapDomain τ = γ := by
    ext a
    rw [Finsupp.mapDomain_equiv_apply]
    simp [sortedExp, β, g]
  have hc := coeff_rename_mapDomain (τ : Fin r → Fin r) τ.injective φ (sortedExp β)
  rw [hmap, hs τ] at hc
  exact hne (hc.trans hβ)

/-! ### The pairing `⟨F, P⟩ = F(2∂_{a_1}, 4∂_{a_2}, …) P` at matching degree -/

/-- `∏_m (2(m+1))^{α_m} α_m!`, the value of `⟨H^α, a^α⟩`. -/
def pairConst (α : ℕ →₀ ℕ) : ℂ :=
  α.prod fun m k => (2 * ((m : ℂ) + 1)) ^ k * (k.factorial : ℂ)

theorem pairConst_ne_zero (α : ℕ →₀ ℕ) : pairConst α ≠ 0 := by
  rw [pairConst, Finsupp.prod]
  refine Finset.prod_ne_zero_iff.mpr fun m _ => mul_ne_zero (pow_ne_zero _ ?_) ?_
  · have : (2 * ((m : ℂ) + 1)) = ((2 * (m + 1) : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- The pairing, as a sum over the support of the oscillator polynomial `P`. -/
def pairSum (F P : MvPolynomial ℕ ℂ) : ℂ :=
  ∑ α ∈ P.support, coeff α F * coeff α P * pairConst α

theorem pairSum_eq_of_subset (F P : MvPolynomial ℕ ℂ) (s : Finset (ℕ →₀ ℕ))
    (hs : P.support ⊆ s) :
    pairSum F P = ∑ α ∈ s, coeff α F * coeff α P * pairConst α := by
  apply Finset.sum_subset hs
  intro α _ hα
  rw [notMem_support_iff.mp hα]; ring

/-- The bilinear pairing `⟨F, P⟩` between `C[H_1, H_2, …]` and the oscillators
`C[a_1, a_2, …]`: for `F`, `P` homogeneous of the same weighted degree it is the constant
`F(2∂_{a_1}, 4∂_{a_2}, 6∂_{a_3}, …) P`. -/
def modePairing : MvPolynomial ℕ ℂ →ₗ[ℂ] MvPolynomial ℕ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ pairSum
    (fun F G P => by
      simp only [pairSum, coeff_add, add_mul, Finset.sum_add_distrib])
    (fun c F P => by
      simp only [pairSum, coeff_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun F P Q => by
      classical
      rw [pairSum_eq_of_subset F (P + Q) (P.support ∪ Q.support) support_add,
        pairSum_eq_of_subset F P (P.support ∪ Q.support) Finset.subset_union_left,
        pairSum_eq_of_subset F Q (P.support ∪ Q.support) Finset.subset_union_right,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by rw [coeff_add]; ring)
    (fun c F P => by
      simp only [smul_eq_mul]
      rw [pairSum_eq_of_subset F (c • P) P.support (support_smul), pairSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [coeff_smul, smul_eq_mul]; ring)

theorem modePairing_apply (F P : MvPolynomial ℕ ℂ) : modePairing F P = pairSum F P := rfl

theorem modePairing_monomial (α : ℕ →₀ ℕ) (P : MvPolynomial ℕ ℂ) :
    modePairing (monomial α 1) P = coeff α P * pairConst α := by
  classical
  rw [modePairing_apply, pairSum_eq_of_subset _ P (insert α P.support)
    (Finset.subset_insert _ _)]
  rw [Finset.sum_eq_single α]
  · rw [coeff_monomial, if_pos rfl]; ring
  · intro β _ hβ
    rw [coeff_monomial, if_neg (Ne.symm hβ)]; ring
  · intro h; exact absurd (Finset.mem_insert_self α _) h

/-! ### The bound -/

/-- Coefficients of the Cartan image at the sorted exponent vectors. -/
def sortedCoeffs (r D : ℕ) : MvPolynomial ℕ ℂ →ₗ[ℂ] (Sorted r D → ℂ) :=
  LinearMap.pi fun β => (lcoeff ℂ (sortedExp β)).comp (cartanEval r).toLinearMap

/-- **The cyclic-evaluation bound.** An injective linear map into the oscillator space
`C[a_1, a_2, …]`, landing in weighted degree `N - r(r+1)` and annihilated (through `modePairing`)
by the degree-matching part of the symmetric-center Cartan ideal `I_r`, bounds the dimension of
its source by `gapTwoCoefficient N r = [z^N] z^{r(r+1)}/∏_{j ≤ r}(1 - z^j)`.
Proved outright. -/
theorem finrank_le_gapTwoCoefficient_of_cyclicEvaluation
    {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℤ) (r : ℕ)
    (ev : V →ₗ[ℂ] MvPolynomial ℕ ℂ) (hinj : Function.Injective ev)
    (hdeg : ∀ x, IsWeightedHomogeneous modeWeightZ (ev x) (N - r * (r + 1)))
    (hann : ∀ x (F : MvPolynomial ℕ ℂ), F ∈ cartanIdeal r →
      IsWeightedHomogeneous modeWeightZ F (N - r * (r + 1)) → modePairing F (ev x) = 0) :
    finrank ℂ V ≤ LeeYangTransferAssembly.gapTwoCoefficient N r := by
  classical
  by_cases hN : N - r * (r + 1) < 0
  · have hzero : ∀ x, ev x = 0 := by
      intro x
      ext α
      rw [coeff_zero]
      by_contra hne
      have := hdeg x hne
      have := weight_modeWeightZ_nonneg α
      omega
    haveI : Subsingleton V := ⟨fun a b => hinj (by rw [hzero a, hzero b])⟩
    rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
  replace hN := not_lt.mp hN
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = N - r * (r + 1) := ⟨(N - r * (r + 1)).toNat, by omega⟩
  have hDN : ((r * (r + 1) + D : ℕ) : ℤ) = N := by push_cast; omega
  rw [← hD] at hdeg hann
  let H0 := weightedHomogeneousSubmodule ℂ modeWeightZ (D : ℤ)
  let L0 : H0 →ₗ[ℂ] (Sorted r D → ℂ) := (sortedCoeffs r D).comp H0.subtype
  let Φ : V →ₗ[ℂ] Module.Dual ℂ H0 :=
    (LinearMap.dualMap H0.subtype).comp (modePairing.flip.comp ev)
  have hΦ : ∀ x, Φ x ∈ (LinearMap.ker L0).dualAnnihilator := by
    intro x
    rw [Submodule.mem_dualAnnihilator]
    intro F hF
    have hFh : IsWeightedHomogeneous modeWeightZ (F : MvPolynomial ℕ ℂ) (D : ℤ) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
    have hzero : cartanEval r F = 0 := by
      apply eq_zero_of_sorted_coeff _ (cartanEval_isSymmetric r F)
        (cartanEval_isHomogeneous r D F hFh)
      intro β
      have := congrFun (LinearMap.mem_ker.mp hF) β
      exact this
    exact hann x F (RingHom.mem_ker.mpr hzero) hFh
  let Ψ : V →ₗ[ℂ] (LinearMap.ker L0).dualAnnihilator := Φ.codRestrict _ hΦ
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz' : Φ z = 0 := congrArg Subtype.val hz
    rw [Submodule.mem_bot]
    apply hinj
    rw [map_zero]
    ext α
    rw [coeff_zero]
    by_cases hα : Finsupp.weight modeWeightZ α = (D : ℤ)
    · have hmem : (monomial α (1 : ℂ)) ∈ H0 :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_monomial _ _ _ hα)
      have h1 := LinearMap.congr_fun hz' ⟨_, hmem⟩
      change modePairing (monomial α 1) (ev z) = 0 at h1
      rw [modePairing_monomial] at h1
      exact (mul_eq_zero.mp h1).resolve_right (pairConst_ne_zero α)
    · by_contra hne
      exact hα (hdeg z hne)
  haveI : Fintype (Sorted r D) := Fintype.ofFinite _
  haveI : FiniteDimensional ℂ (H0 ⧸ LinearMap.ker L0) :=
    Module.Finite.equiv L0.quotKerEquivRange.symm
  haveI : FiniteDimensional ℂ (LinearMap.ker L0).dualAnnihilator :=
    Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator _)
  calc finrank ℂ V
      ≤ finrank ℂ (LinearMap.ker L0).dualAnnihilator :=
        LinearMap.finrank_le_finrank_of_injective hΨ
    _ = finrank ℂ (Module.Dual ℂ (H0 ⧸ LinearMap.ker L0)) :=
        (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq.symm
    _ = finrank ℂ (H0 ⧸ LinearMap.ker L0) := Subspace.dual_finrank_eq
    _ = finrank ℂ (LinearMap.range L0) := L0.quotKerEquivRange.finrank_eq
    _ ≤ finrank ℂ (Sorted r D → ℂ) := Submodule.finrank_le _
    _ = Nat.card (Sorted r D) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
    _ ≤ _ := card_sorted_le hDN

end

end VOA.InvariantSymbol
