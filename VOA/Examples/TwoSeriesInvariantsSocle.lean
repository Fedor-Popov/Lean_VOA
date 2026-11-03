/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesKoszulLeeYang
import VOA.Examples.TwoSeriesCharacterAGIdentity
import VOA.Examples.TwoSeriesCharacterGU
import VOA.Examples.LevelOneHeisEndpoint

/-!
# The invariant count for every `n` from a family of socle duals

For `k = -2 + 2/(2n+1)` the last open input of
`twoSeries_gradedUnitary_of_affine_invariants_gordon_final` is

  `rank (gr_r L_k(sl₂) ⊗ L_1(sl₂))^{g[t]}_N ≤ gordonCoeff n N r`.

At `n = 1` it is proved from **one** cyclic dual vector `w_r` per filtration degree
(`leeYang_affineInvariants_rank_le`, via `finrank_le_of_heisenberg`).  For `n ≥ 2` a single
cyclic vector cannot work: at `n = 2`, `r = 2`, `N = 4` there is an invariant tensor, but the
charge-`2r` contraction would land in an `L_1` space of charge `4` and energy `2 < 4`, which is
zero (numerical evidence, not a proof).  The restricted dual of
`gr_r L_k` needs **several** generators: one for each `g[t]`-singular vector of `gr_r L_k`
(its *socle*), indexed by words in the letters `0, …, n-1` (a letter `j` is a cluster of
size `j+1`).

## Abstract part (proved outright)

* `cartanDualSpace E s` — the functionals on the weighted-degree-`E` oscillator polynomials
  that vanish on the Cartan ideal `I_s`; `cartanDualSpace_finiteDimensional`,
  `finrank_cartanDualSpace_le` (`≤ gapTwoCoefficient N s` for `E = N - s(s+1)`).
* `SocleDualFamily` — a finite family of functionals `w_i` on `M` that is **jointly cyclic**
  (their translates by mode words separate points), each supported in one conformal degree
  `deg i`, of charge `2·clusters i`, and annihilated by the Cartan ideal `I_{clusters i}`.
* `finiteDimensional_and_finrank_le_of_socle` — invariant tensors of weight `N` span a
  finite-dimensional space of dimension `≤ Σ_i gapTwoCoefficient (N - deg i + clusters i)
  (clusters i)`, given Heisenberg separation of `B`.  At a one-element family with
  `deg = clusters = r` this is `finrank_le_of_heisenberg`.

## Specialization to `L_k(sl₂) ⊗ L_1(sl₂)` (proved, conditional on the displayed inputs)

* `grRho_cartan_comm` — the induced Cartan modes commute on `gr_r L_k` (every level);
  `grCartanCalc` — the polynomial calculus `H_{i+1} ↦ -J^h_{i+1}` on `gr_r L_k`.
* `socleDegree`, `socleWordCount n N r = Σ_{words} gapTwoCoefficient (N - deg + N₁) N₁`, where a
  word `x` of length `N₁` with `Σ (x_j + 1) = r` has degree
  `N₁ + Σ_{t=1}^{n-1} (c_t² + c_t) + inv(x)`, `c_t = #{j : x_j ≥ t}`.
* `TwoSeriesSocleInput n` — OPEN (affine input, the generalization of input (A) of the coset
  note): socle duals on `gr_r L_k` indexed by these words, jointly cyclic, with the stated
  degree, charge and Cartan relations.
* `SocleWordGordon n` — pure combinatorics; proved for every `n` by `SocleCount.socleWordGordon`
  (`TwoSeriesSocleCountGordon.lean`): `socleWordCount n N r ≤ gordonCoeff n N r` (in fact equality:
  it is the
  fixed-number-of-parts Andrews–Gordon fermionic formula, written with `q`-multinomials as
  inversion counts).
* `twoSeries_affineInvariants_rank_le_socleWordCount` and
  `twoSeries_gradedUnitary_of_socle` — **Affine GU ⇒ GU of `M(2, 2n+3)`**, conditional on
  `hA`, `TwoSeriesSocleInput n` and `SocleWordGordon n`.  The level-one input is the proved
  `VOA.LevelOneHeis.levelOneHeisenbergSeparation`.
-/

namespace VOA.SocleEval

open MvPolynomial Module VOA.InvariantSymbol VOA.CyclicEval TensorProduct
open scoped BigOperators

noncomputable section

/-! ### The Cartan-annihilated dual space -/

/-- Functionals on the weighted-degree-`E` oscillator polynomials that vanish on the Cartan
ideal `I_s`. -/
def cartanDualSpace (E : ℤ) (s : ℕ) :
    Submodule ℂ (Module.Dual ℂ (weightedHomogeneousSubmodule ℂ modeWeightZ E)) where
  carrier := {φ | ∀ F : weightedHomogeneousSubmodule ℂ modeWeightZ E,
    (F : MvPolynomial ℕ ℂ) ∈ cartanIdeal s → φ F = 0}
  add_mem' := by
    intro φ ψ hφ hψ F hF
    simp only [Set.mem_setOf_eq] at hφ hψ
    rw [LinearMap.add_apply, hφ F hF, hψ F hF, add_zero]
  zero_mem' := by
    intro F _
    rfl
  smul_mem' := by
    intro c φ hφ F hF
    simp only [Set.mem_setOf_eq] at hφ
    rw [LinearMap.smul_apply, hφ F hF, smul_zero]

/-- The Cartan-annihilated dual space is finite-dimensional. -/
theorem cartanDualSpace_finiteDimensional (N : ℤ) (s : ℕ) :
    FiniteDimensional ℂ (cartanDualSpace (N - s * (s + 1)) s) := by
  classical
  by_cases hN : N - s * (s + 1) < 0
  · haveI : Subsingleton (weightedHomogeneousSubmodule ℂ modeWeightZ (N - s * (s + 1))) :=
      ⟨fun a b => Subtype.ext (by
        rw [eq_zero_of_isWeightedHomogeneous_neg hN
            ((mem_weightedHomogeneousSubmodule _ _ _ _).mp a.2),
          eq_zero_of_isWeightedHomogeneous_neg hN
            ((mem_weightedHomogeneousSubmodule _ _ _ _).mp b.2)])⟩
    haveI : Subsingleton
        (Module.Dual ℂ (weightedHomogeneousSubmodule ℂ modeWeightZ (N - s * (s + 1)))) :=
      ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    infer_instance
  replace hN := not_lt.mp hN
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = N - s * (s + 1) := ⟨(N - s * (s + 1)).toNat, by omega⟩
  rw [← hD]
  let H0 := weightedHomogeneousSubmodule ℂ modeWeightZ (D : ℤ)
  let L0 : H0 →ₗ[ℂ] (Sorted s D → ℂ) := (sortedCoeffs s D).comp H0.subtype
  have hle : cartanDualSpace (D : ℤ) s ≤ (LinearMap.ker L0).dualAnnihilator := by
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator]
    intro F hF
    have hFh : IsWeightedHomogeneous modeWeightZ (F : MvPolynomial ℕ ℂ) (D : ℤ) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
    have hzero : cartanEval s F = 0 := by
      apply eq_zero_of_sorted_coeff _ (cartanEval_isSymmetric s F)
        (cartanEval_isHomogeneous s D F hFh)
      intro β
      exact congrFun (LinearMap.mem_ker.mp hF) β
    exact hφ F (RingHom.mem_ker.mpr hzero)
  haveI : Fintype (Sorted s D) := Fintype.ofFinite _
  haveI : FiniteDimensional ℂ (H0 ⧸ LinearMap.ker L0) :=
    Module.Finite.equiv L0.quotKerEquivRange.symm
  haveI : FiniteDimensional ℂ (LinearMap.ker L0).dualAnnihilator :=
    Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator _)
  exact Submodule.finiteDimensional_of_le hle

/-- The Cartan-annihilated dual space has dimension at most `gapTwoCoefficient N s`. -/
theorem finrank_cartanDualSpace_le (N : ℤ) (s : ℕ) :
    finrank ℂ (cartanDualSpace (N - s * (s + 1)) s) ≤
      LeeYangTransferAssembly.gapTwoCoefficient N s :=
  finrank_le_gapTwoCoefficient_of_dual N s (cartanDualSpace _ s).subtype Subtype.val_injective
    (fun v F hF => v.2 F hF)

/-! ### Families of socle duals -/

section Family

variable {M B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} (ρ : κ → Module.End ℂ M) (σ : κ → Module.End ℂ B)
variable (hz : κ) (hpos : ℕ → κ) (Mdeg : ℤ → Submodule ℂ M) (Bdeg : ℤ → Submodule ℂ B)

/-- **A jointly cyclic family of Cartan-annihilated dual vectors** (the generalization of
`CyclicDual` to a restricted dual with several generators).  `w i` is supported in conformal
degree `deg i`, has weight `2 · clusters i` under the negative-transpose action of `h₀`, and is
annihilated by the Cartan ideal `I_{clusters i}`; the translates of all `w i` by mode words
jointly separate the points of `M`. -/
structure SocleDualFamily (ι : Type*) where
  w : ι → Module.Dual ℂ M
  deg : ι → ℕ
  clusters : ι → ℕ
  cyclic : ∀ m : M, (∀ i (l : List κ), w i (word ρ l m) = 0) → m = 0
  supp : ∀ i (d : ℤ), d ≠ (deg i : ℤ) → ∀ m ∈ Mdeg d, w i m = 0
  charge : ∀ i, w i ∘ₗ ρ hz = (-(2 * (clusters i : ℂ))) • w i
  comm : ∀ j, Commute (ρ hz) (ρ (hpos j))
  π : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ M
  π_X : ∀ j, π (X j) = -ρ (hpos j)
  cartan : ∀ i, ∀ F ∈ cartanIdeal (clusters i), w i ∘ₗ π F = 0

variable {ρ σ hz hpos Mdeg Bdeg} {ι : Type*}

namespace SocleDualFamily

variable (D : SocleDualFamily ρ hz hpos Mdeg ι)

theorem commute_π (F : MvPolynomial ℕ ℂ) : Commute (ρ hz) (D.π F) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact Algebra.commutes a _ |>.symm
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | mul_X p i hp => rw [map_mul, D.π_X]; exact hp.mul_right (D.comm i).neg_right

theorem charge_contract_π {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (i : ι) (F : MvPolynomial ℕ ℂ) :
    σ hz (contract (D.w i ∘ₗ D.π F) x) =
      (2 * (D.clusters i : ℂ)) • contract (D.w i ∘ₗ D.π F) x := by
  have h1 := contract_comp_of_isInv hx (D.w i ∘ₗ D.π F) hz
  have h2 : (D.w i ∘ₗ D.π F) ∘ₗ ρ hz = (-(2 * (D.clusters i : ℂ))) • (D.w i ∘ₗ D.π F) := by
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← (D.commute_π F).eq,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, D.charge, LinearMap.smul_comp]
  rw [h2, contract_smul] at h1
  rw [neg_smul] at h1
  exact (neg_inj.mp h1).symm

theorem contract_π_eq (πB : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ B)
    (πB_X : ∀ j, πB (X j) = σ (hpos j)) {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (i : ι)
    (F : MvPolynomial ℕ ℂ) :
    contract (D.w i ∘ₗ D.π F) x = πB F (contract (D.w i) x) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      contract_smul, LinearMap.smul_apply]
    rfl
  | add p q hp hq =>
    rw [map_add, LinearMap.comp_add, contract_add, hp, hq, map_add, LinearMap.add_apply]
  | mul_X p j hp =>
    have hcomp : D.w i ∘ₗ D.π (p * X j) = -((D.w i ∘ₗ D.π p) ∘ₗ ρ (hpos j)) := by
      rw [map_mul, D.π_X, mul_neg, Module.End.mul_eq_comp, LinearMap.comp_neg,
        LinearMap.comp_assoc]
    rw [hcomp, contract_neg, contract_comp_of_isInv hx, neg_neg, hp, mul_comm, map_mul, πB_X,
      Module.End.mul_apply]

end SocleDualFamily

/-- **The inverse-system bound from a jointly cyclic socle family.**  A space `V` embedded in
the invariant tensors of total weight `N` is finite-dimensional, of dimension at most
`Σ_i gapTwoCoefficient (N - deg i + clusters i) (clusters i)`.  Proved outright. -/
theorem finiteDimensional_and_finrank_le_of_socle [Fintype ι]
    (D : SocleDualFamily ρ hz hpos Mdeg ι) (H : ∀ s, HeisenbergSeparation σ hz hpos Bdeg s)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℤ) (j : V →ₗ[ℂ] M ⊗[ℂ] B)
    (hj : Function.Injective j) (hinv : ∀ v, IsInv ρ σ (j v))
    (hwt : ∀ v, j v ∈ tensorWeight Mdeg Bdeg N) :
    FiniteDimensional ℂ V ∧
      finrank ℂ V ≤ ∑ i, LeeYangTransferAssembly.gapTwoCoefficient
        (N - (D.deg i : ℤ) + (D.clusters i : ℤ)) (D.clusters i) := by
  classical
  let s : ι → ℕ := D.clusters
  let N' : ι → ℤ := fun i => N - (D.deg i : ℤ) + (s i : ℤ)
  let E : ι → ℤ := fun i => N' i - (s i : ℤ) * ((s i : ℤ) + 1)
  let y : ι → V →ₗ[ℂ] B := fun i => contract (D.w i) ∘ₗ j
  let Ψi : ∀ i, V →ₗ[ℂ] Module.Dual ℂ (weightedHomogeneousSubmodule ℂ modeWeightZ (E i)) :=
    fun i => LinearMap.mk₂ ℂ (fun v (F : weightedHomogeneousSubmodule ℂ modeWeightZ (E i)) =>
        (H (s i)).β ((H (s i)).πB F (y i v)))
      (fun v v' F => by simp only [map_add])
      (fun c v F => by simp only [map_smul, smul_eq_mul])
      (fun v F F' => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply])
      (fun c v F => by simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul])
  have hΨi : ∀ i v F, Ψi i v F = (H (s i)).β ((H (s i)).πB F (y i v)) := fun i v F => rfl
  have hmem : ∀ i v, Ψi i v ∈ cartanDualSpace (E i) (s i) := by
    intro i v F hF
    rw [hΨi]
    change (H (s i)).β ((H (s i)).πB F (contract (D.w i) (j v))) = 0
    rw [← D.contract_π_eq (H (s i)).πB (H (s i)).πB_X (hinv v), D.cartan i F hF, contract_zero,
      map_zero]
  let Ψ : V →ₗ[ℂ] (∀ i, cartanDualSpace (E i) (s i)) :=
    LinearMap.pi fun i => (Ψi i).codRestrict _ (hmem i)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    have hy : ∀ i, y i v = 0 := by
      intro i
      have hvi : Ψi i v = 0 := by
        have := congrFun (congrArg (fun f => (f : ∀ i, cartanDualSpace (E i) (s i))) hv) i
        exact congrArg Subtype.val this
      have hcharge : σ hz (y i v) = (2 * (s i : ℂ)) • y i v := by
        have := D.charge_contract_π (hinv v) i 1
        simpa only [map_one, LinearMap.comp_id] using this
      refine (H (s i)).sep (N - D.deg i) (y i v)
        (contract_mem_of_tensorWeight (D.w i) (D.supp i) (hwt v)) hcharge fun F hF => ?_
      have he : (N - (D.deg i : ℤ)) - (s i : ℤ) * (s i) = E i := by
        simp only [E, N']; ring
      rw [he] at hF
      have := LinearMap.congr_fun hvi ⟨F, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hF⟩
      rw [hΨi] at this
      exact this
    have hjv : j v = 0 := by
      refine eq_zero_of_contract_separating {u | ∃ i l, u = D.w i ∘ₗ word ρ l} ?_ (j v) ?_
      · intro m hm
        exact D.cyclic m fun i l => hm _ ⟨i, l, rfl⟩
      · rintro _ ⟨i, l, rfl⟩
        obtain ⟨T, hT⟩ := exists_contract_word (hinv v) l
        rw [hT, show contract (D.w i) (j v) = y i v from rfl, hy i, map_zero]
    exact hj (by rw [hjv, map_zero])
  haveI : ∀ i, FiniteDimensional ℂ (cartanDualSpace (E i) (s i)) :=
    fun i => cartanDualSpace_finiteDimensional (N' i) (s i)
  haveI hV : FiniteDimensional ℂ V := Module.Finite.of_injective Ψ hΨ
  refine ⟨hV, ?_⟩
  calc finrank ℂ V ≤ finrank ℂ (∀ i, cartanDualSpace (E i) (s i)) :=
        LinearMap.finrank_le_finrank_of_injective hΨ
    _ = ∑ i, finrank ℂ (cartanDualSpace (E i) (s i)) := Module.finrank_pi_fintype ℂ
    _ ≤ _ := Finset.sum_le_sum fun i _ => finrank_cartanDualSpace_le (N' i) (s i)

end Family

/-! ### Socle words -/

/-- Words of length `N₁` in the letters `0, …, n-1` (a letter `t` is a cluster of size `t+1`)
with total cluster size `r`. -/
def SocleWord (n r N₁ : ℕ) : Type := {x : Fin N₁ → Fin n // ∑ j, ((x j : ℕ) + 1) = r}

instance (n r N₁ : ℕ) : Fintype (SocleWord n r N₁) := by
  unfold SocleWord; infer_instance

/-- `c_t = #{j : x_j ≥ t}`: the number of clusters of size `> t`. -/
def clusterAtLeast {n N₁ : ℕ} (x : Fin N₁ → Fin n) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun j => t ≤ (x j : ℕ)).card

/-- The number of inversions of a word. -/
def inversions {n N₁ : ℕ} (x : Fin N₁ → Fin n) : ℕ :=
  (Finset.univ.filter fun p : Fin N₁ × Fin N₁ => p.1 < p.2 ∧ x p.2 < x p.1).card

/-- The conformal degree of the socle vector labelled by a word:
`N₁ + Σ_{t=1}^{n-1} (c_t² + c_t) + inv(x)`. -/
def socleDegree {n N₁ : ℕ} (x : Fin N₁ → Fin n) : ℕ :=
  N₁ + ∑ t ∈ Finset.Ico 1 n, (clusterAtLeast x t ^ 2 + clusterAtLeast x t) + inversions x

/-- The socle labels in filtration degree `r`: a word together with its length `N₁ ≤ r`. -/
abbrev SocleIndex (n r : ℕ) : Type := Σ N₁ : Fin (r + 1), SocleWord n r N₁

/-- **The socle-word count** `Σ_x gapTwoCoefficient (N - deg x + N₁) N₁`
`= Σ_x #{partitions of N - N₁² - deg x into at most N₁ parts}`. -/
def socleWordCount (n : ℕ) (N : ℤ) (r : ℕ) : ℕ :=
  ∑ i : SocleIndex n r, LeeYangTransferAssembly.gapTwoCoefficient
    (N - (socleDegree i.2.1 : ℤ) + ((i.1 : ℕ) : ℤ)) (i.1 : ℕ)

/-- Pure combinatorics, proved for every `n`: `SocleCount.socleWordGordon`
(`TwoSeriesSocleCountGordon.lean`).  The socle-word count is at most the Andrews–Gordon coefficient.
(It is equal: the
inversion generating function of words of content `m` is the `q`-multinomial
`(q)_{N₁}/∏(q)_{m_j}`, and the sum is the fixed-number-of-parts Andrews–Gordon fermionic
formula `Σ_m q^{Σ_i (N_i² + N_i)}/∏_j (q)_{m_j}`.) -/
def SocleWordGordon (n : ℕ) : Prop :=
  ∀ (N : ℤ) (r : ℕ), socleWordCount n N r ≤ VOA.TwoSeriesCharacter.gordonCoeff n N r

end

end VOA.SocleEval

namespace VOA.TwoSeries

open VOA.SocleEval VOA.CyclicEval VOA.InvariantSymbol MvPolynomial Module
open VOA.ConcreteHodge VOA.SymbolModel VOA.GradedUnitaryCohomology VirGradedUnitarity
open Sl2CosetConcrete
open scoped TensorProduct BigOperators

noncomputable section

variable (L : CosetLevels)

/-! ### The Cartan calculus on `gr_r L_k`, at every level -/

/-- `h_i h_j = h_j h_i` on the simple affine factor, `i, j ≥ 0`. -/
theorem aMode_cartan_comm (i j : ℕ) :
    aMode L 2 i * aMode L 2 j = aMode L 2 j * aMode L 2 i := by
  have h := (aAction L).current_comm 2 2 i j
  have h' : aMode L 2 i * aMode L 2 j - aMode L 2 j * aMode L 2 i = 0 := by
    change mode ((ASVA L).Y ((aAction L).current 2)) i *
        mode ((ASVA L).Y ((aAction L).current 2)) j -
      mode ((ASVA L).Y ((aAction L).current 2)) j *
        mode ((ASVA L).Y ((aAction L).current 2)) i = 0
    rw [h]
    split_ifs with hij
    · have hi : (i : ℤ) = 0 := by omega
      rw [hi, Finset.sum_eq_zero fun c _ => by rw [VOA.CyclicEval.fabc_two_two c, zero_smul]]; simp
    · rw [add_zero]
      exact Finset.sum_eq_zero fun c _ => by rw [VOA.CyclicEval.fabc_two_two c, zero_smul]
  exact sub_eq_zero.mp h'

/-- The induced Cartan modes commute on `gr_r L_k`. -/
theorem grRho_cartan_comm (r i j : ℕ) :
    Commute (grRho L r (2, i)) (grRho L r (2, j)) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply,
    grRho_mk]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (aMode_cartan_comm L i j) x

theorem grZero_comm' (r : ℕ) : ∀ i, Commute (grRho L r bHZero) (grRho L r (bHPos i)) :=
  fun i => grRho_cartan_comm L r 0 (i + 1)

/-- The commutative algebra generated by the negated positive Cartan modes on `gr_r L_k`. -/
abbrev GrCartanAlg (r : ℕ) : Subalgebra ℂ (Module.End ℂ (GrA L r)) :=
  Algebra.adjoin ℂ (Set.range fun i : ℕ => -grRho L r (bHPos i))

instance grCartanAlg_isMulCommutative (r : ℕ) : IsMulCommutative (GrCartanAlg L r) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((grRho_cartan_comm L r (i + 1) (j + 1)).neg_left.neg_right).eq)

open scoped IsMulCommutative

set_option synthInstance.maxHeartbeats 400000 in
-- the commutative-semiring instance on the adjoined Cartan subalgebra is found slowly
/-- The negative-transpose Cartan calculus `H_{i+1} ↦ -J^h_{i+1}` on `gr_r L_k`. -/
def grCartanCalc (r : ℕ) : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ (GrA L r) :=
  (GrCartanAlg L r).val.comp
    (aeval fun i => (⟨-grRho L r (bHPos i), Algebra.subset_adjoin ⟨i, rfl⟩⟩ : GrCartanAlg L r))

set_option synthInstance.maxHeartbeats 400000 in
-- as for `grCartanCalc`
@[simp] theorem grCartanCalc_X (r i : ℕ) : grCartanCalc L r (X i) = -grRho L r (bHPos i) := by
  simp [grCartanCalc]

/-! ### The affine socle input and the conditional theorems -/

/-- OPEN (affine input; for `n = 1` it is input (A) of the coset note, proved): **socle duals
of `gr_r L_k(sl₂)`**, `k = -2 + 2/(2n+1)`.  For each filtration degree `r` and each socle word
`x` of length `N₁`, a functional `w` on `gr_r L_k` of conformal degree `socleDegree x`, of weight
`2N₁` under the negative-transpose action of `h₀`, annihilated by the Cartan ideal `I_{N₁}`;
the translates of all of them by mode words separate the points of `gr_r L_k`.  (Dually: the
`g[t]`-singular vectors of `gr_r L_k` have the socle-word Hilbert series, and the Cartan ideal
acts transversally to them; this is numerical evidence, not a proof.) -/
structure TwoSeriesSocleInput (n : ℕ) where
  w : ∀ r, SocleIndex n r → Module.Dual ℂ (GrA (twoSeriesLevels n) r)
  cyclic : ∀ r (m : GrA (twoSeriesLevels n) r),
    (∀ i (l : List (Fin 3 × ℕ)), w r i (word (grRho (twoSeriesLevels n) r) l m) = 0) → m = 0
  supp : ∀ r i (d : ℤ), d ≠ (socleDegree i.2.1 : ℤ) →
    ∀ m ∈ grDeg (twoSeriesLevels n) r d, w r i m = 0
  charge : ∀ r i, w r i ∘ₗ grRho (twoSeriesLevels n) r bHZero =
    (-(2 * (((i.1 : ℕ) : ℂ)))) • w r i
  cartan : ∀ r i, ∀ F ∈ cartanIdeal (i.1 : ℕ),
    w r i ∘ₗ grCartanCalc (twoSeriesLevels n) r F = 0

/-- The socle input as an abstract `SocleDualFamily`. -/
def TwoSeriesSocleInput.toFamily {n : ℕ} (S : TwoSeriesSocleInput n) (r : ℕ) :
    SocleDualFamily (grRho (twoSeriesLevels n) r) bHZero bHPos (grDeg (twoSeriesLevels n) r)
      (SocleIndex n r) where
  w := S.w r
  deg i := socleDegree i.2.1
  clusters i := i.1
  cyclic := S.cyclic r
  supp := S.supp r
  charge := S.charge r
  comm := grZero_comm' _ r
  π := grCartanCalc _ r
  π_X := grCartanCalc_X _ r
  cartan := S.cartan r

/-- **The affine invariant count from the socle input**: the invariant space of
`gr_r L_k(sl₂) ⊗ L_1(sl₂)` at weight `N` has rank at most `socleWordCount n N r`.
`#print axioms`-clean, conditional on `S`. -/
theorem twoSeries_affineInvariants_rank_le_socleWordCount (n : ℕ) (S : TwoSeriesSocleInput n)
    (N : ℤ) (r : ℕ) :
    Module.rank ℂ (affineInvariants (twoSeriesLevels n) r N) ≤ socleWordCount n N r := by
  obtain ⟨hfd, hle⟩ := finiteDimensional_and_finrank_le_of_socle (S.toFamily r)
    (fun s => VOA.LevelOneHeis.levelOneHeisenbergSeparation.toSep s) N
    (affineInvariants (twoSeriesLevels n) r N).subtype Subtype.val_injective
    (fun v => ((mem_affineInvariants (twoSeriesLevels n) r N _).mp v.2).2)
    (fun v => ((mem_affineInvariants (twoSeriesLevels n) r N _).mp v.2).1)
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

/-- **Affine GU ⇒ GU of `M(2, 2n+3)` from the socle input.**  `#print axioms`-clean,
conditional on `hA`, the affine socle input `S`, and the combinatorial identity
`SocleWordGordon n`. -/
theorem twoSeries_gradedUnitary_of_socle (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (S : TwoSeriesSocleInput n) (hcomb : SocleWordGordon n) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_affine_invariants_gordon_final n hA fun N r =>
    (twoSeries_affineInvariants_rank_le_socleWordCount n S N r).trans
      (by exact_mod_cast hcomb N r)

end

end VOA.TwoSeries
