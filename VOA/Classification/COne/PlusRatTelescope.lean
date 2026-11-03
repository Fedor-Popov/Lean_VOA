import VOA.Classification.COne.PlusSplitSessionFifteen

/-! # Translation telescoping for a generalized vacuum lift

Setting (general VOA `W`): a weak module `A` with a map `π` onto the adjoint module whose
kernel has positive intrinsic bottom, and a generalized vacuum lift `x`.  Put `y = T x`.

For homogeneous `a ∈ W_α` (`α ≥ 1`), `b ∈ W_β` and `J = α + β - 2`, the translation-defect
formula, the vanishing of weight-zero kernel vectors and the vanishing of the zero mode on
`x` telescope to the exact identity

  `∑_{n < α} (-1)^n C(J,n) b_{J-n} a_n (T x) = 0`        (`translation_telescope`).

For any top vector `y ∈ Ω(A)` the same left-hand side is the action of one explicit element
`zeta a b α J` of Zhu's algebra (`telescope_eq_topEvaluation`), which does not depend on the
module.  Nothing here is specific to `V_{2m}⁺`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRatTelescope
open PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

section Lift
variable (A : WeakModule W M) (π : A.Hom (adjointWeakModule W)) (h : ℂ)
  (hb : FactorBottom A ⊥ (modeComap π ⊥) h) (hh : 0 < h.re)
  {x : M} (hx : x ∈ (L0 A).maxGenEigenspace 0) (he : π.toLinearMap x = W.vacuum)

include hb hh hx he in
/-- A composite of a non-negative mode and a second mode of total degree zero kills the
generalized vacuum lift: the result lies in the kernel at generalized weight zero. -/
theorem double_mode_vanish {α β : ℤ} {a b : V} (ha : a ∈ W.grading α)
    (hb' : b ∈ W.grading β) (n p : ℤ) (hn : 0 ≤ n) (hw : α + β - n - p - 2 = 0) :
    mode (A.YM b) p (mode (A.YM a) n x) = 0 := by
  apply generalized_vacuum_lift_unique A π h hb hh
    (x := mode (A.YM b) p (mode (A.YM a) n x)) (y := 0)
  · have h1 := mode_mem_maxGenEigenspace A ha n hx
    have h2 := mode_mem_maxGenEigenspace A hb' p h1
    have hc : (0 : ℂ) + ((α - n - 1 : ℤ) : ℂ) + ((β - p - 1 : ℤ) : ℂ) = 0 := by
      have hz : ((α - n - 1 : ℤ) + (β - p - 1 : ℤ) : ℤ) = 0 := by omega
      have hz' : (((α - n - 1 : ℤ) + (β - p - 1 : ℤ) : ℤ) : ℂ) = 0 := by
        rw [hz]; simp
      push_cast at hz' ⊢
      linear_combination hz'
    rwa [hc] at h2
  · exact Submodule.zero_mem _
  · change π.toLinearMap (A.act b p (A.act a n x)) = π.toLinearMap 0
    rw [π.map_act, π.map_act, he, map_zero]
    have hv : (adjointWeakModule W).act a n W.vacuum = 0 := (W.creation a).2 n hn
    rw [hv, WeakModule.act_def, map_zero]

/-- Binomial bookkeeping, valid for every `n` (both sides vanish when `n > J`). -/
theorem choose_mul_sub (J n : ℕ) :
    (J.choose n : ℂ) * ((J : ℂ) - n) = (J.choose (n + 1) : ℂ) * ((n : ℂ) + 1) := by
  rcases le_or_gt n J with hle | hlt
  · have h := Nat.choose_succ_right_eq J n
    have hc : ((J.choose (n + 1) * (n + 1) : ℕ) : ℂ) = ((J.choose n * (J - n) : ℕ) : ℂ) := by
      rw [h]
    push_cast [Nat.cast_sub hle] at hc
    linear_combination -hc
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **The telescoping core.** If the zero mode `a_{N-1}` kills `x` and every composite
`b_{J-n} a_n x` (`n < N`) vanishes, then `∑_{n<N} (-1)^n C(J,n) b_{J-n} a_n (T x) = 0`.
No grading hypothesis on `x` is used. -/
theorem telescope_core (a b : V) (N J : ℕ) (x : M)
    (hz : mode (A.YM a) ((N : ℤ) - 1) x = 0)
    (h0 : ∀ n : ℕ, n < N → mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) n x) = 0) :
    ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
      mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) n (translation A x)) = 0 := by
  let G : ℕ → M := fun k => (-(-1 : ℂ) ^ k * (k : ℂ) * (J.choose k : ℂ)) •
    mode (A.YM b) ((J : ℤ) - k) (mode (A.YM a) ((k : ℤ) - 1) x)
  have hstep : ∀ n ∈ Finset.range N, ((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
      mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) n (translation A x)) = G (n + 1) - G n := by
    intro n hn
    have h1 := mode_translation_defect A a (n : ℤ) x
    have h2 := mode_translation_defect A b ((J : ℤ) - n) (mode (A.YM a) n x)
    have h0n := h0 n (Finset.mem_range.mp hn)
    rw [h1, map_add, map_smul, h2, h0n, map_zero, zero_add]
    have e1 : (J : ℤ) - n - 1 = (J : ℤ) - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    simp only [G]
    rw [e1, e2]
    have hc := choose_mul_sub J n
    set X := mode (A.YM b) ((J : ℤ) - ((n + 1 : ℕ) : ℤ)) (mode (A.YM a) (n : ℤ) x)
    set Y := mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) ((n : ℤ) - 1) x)
    have hcast : (((J : ℤ) - n : ℤ) : ℂ) = (J : ℂ) - n := by push_cast; ring
    rw [hcast]
    push_cast
    linear_combination (norm := module) (((-1 : ℂ) ^ n) * hc) • X
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub]
  simp only [G, hz, map_zero, smul_zero, Nat.cast_zero, mul_zero, zero_mul, zero_smul,
    sub_zero]

include hb hh hx he in
/-- **Translation telescoping.** For `a ∈ W_α` (`α = N ≥ 1`), `b ∈ W_β`, `J = α + β - 2`:
`∑_{n<α} (-1)^n C(J,n) b_{J-n} a_n (T x) = 0`. -/
theorem translation_telescope {α β : ℤ} {a b : V} (ha : a ∈ W.grading α)
    (hb' : b ∈ W.grading β) (N J : ℕ) (hN : (N : ℤ) = α) (hN1 : 1 ≤ N)
    (hJ : (J : ℤ) = α + β - 2) :
    ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
      mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) n (translation A x)) = 0 := by
  apply telescope_core A a b N J x
  · have := zeroMode_vacuum_lift_eq_zero A π h hb hh hx he ha (by omega)
    rwa [← hN] at this
  · intro n _
    exact double_mode_vanish A π h hb hh hx he ha hb' n _ (by positivity) (by omega)

end Lift

section Zhu
variable (A : WeakModule W M)

/-- The finite rewriting of a natural-index binomial finsum. -/
theorem finsum_cbz_nat (P : ℕ) (g : ℤ → M) :
    ∑ᶠ i : ℤ, cbz (P : ℤ) i • g i =
      ∑ i ∈ Finset.range (P + 1), (P.choose i : ℂ) • g i := by
  rw [finsum_eq_sum_of_support_subset (s := (Finset.range (P + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ P := by have := Finset.mem_range.mp hi; omega
    simp only [Nat.castEmbedding_apply]
    rw [cbz_natCast_eq_choose hi']
  · intro i hi
    rw [Function.mem_support] at hi
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg _ (by omega), zero_smul])
    have h1 : i ≤ P := by
      by_contra hgt
      exact hi (by rw [cbz_lt (by positivity) (by omega), zero_smul])
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    exact ⟨i.toNat, by omega, by omega⟩

/-- The explicit state `∑_i C(P,i) b_i a`. -/
def zstate (W : VertexOperatorAlgebra V) (a b : V) (P : ℕ) : V :=
  ∑ i ∈ Finset.range (P + 1), (P.choose i : ℂ) • W.smul b i a

/-- On a top vector, a lowering mode after a raising mode is the zero mode of `zstate`. -/
theorem lowering_composite_eq {α β : ℤ} {a b : V} (ha : a ∈ W.grading α)
    (hb : b ∈ W.grading β) {y : M} (hy : y ∈ Omega A) (P : ℕ) (q : ℤ)
    (hP : β ≤ (P : ℤ)) (hq : (P : ℤ) + q = α + β - 2) :
    mode (A.YM b) (P : ℤ) (mode (A.YM a) q y) = oLevW A 0 (zstate W a b P) y := by
  have hc := mode_commutator A b a y (P : ℤ) q
  rw [Omega_mode_vanish hy hb hP, map_zero, sub_zero, finsum_cbz_nat] at hc
  rw [hc, zstate, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, LinearMap.smul_apply,
    oLevW_homogeneous A 0 (W.toPreVertexAlgebra.smul_mem_grading hb ha (i : ℤ))]
  have hi : (P : ℤ) + q - (i : ℤ) = β + α - (i : ℤ) - 1 - 1 + 0 := by omega
  rw [hi]

end Zhu

section ZhuAlg
variable (A : WeakModule W M)

/-- The Zhu element whose top action is the telescoping sum. -/
def zeta (W : VertexOperatorAlgebra V) (a b : V) (N J : ℕ) : VOA.A W :=
  letI := instRingA W
  letI := instAlgebraA W
  ∑ n ∈ Finset.range (N - 1), ((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
      VOA.mk W (zstate W a b (J - n)) +
    ((-1 : ℂ) ^ (N - 1) * (J.choose (N - 1) : ℂ)) • (VOA.mk W b * VOA.mk W a)

/-- **Zhu evaluation of the telescoping sum on any top vector.** -/
theorem telescope_eq_topEvaluation {α β : ℤ} {a b : V} (ha : a ∈ W.grading α)
    (hb : b ∈ W.grading β) {y : M} (hy : y ∈ Omega A) (N J : ℕ) (hN : (N : ℤ) = α)
    (hN1 : 1 ≤ N) (hJ : (J : ℤ) = α + β - 2) (hβ : 0 ≤ β) :
    ∑ n ∈ Finset.range N, ((-1 : ℂ) ^ n * (J.choose n : ℂ)) •
      mode (A.YM b) ((J : ℤ) - n) (mode (A.YM a) n y) =
      topEvaluation A y hy (zeta W a b N J) := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ, zeta, map_add, map_sum, map_smul, Nat.add_sub_cancel]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    rw [map_smul, topEvaluation_mk]
    congr 1
    have hJn : ((J - n : ℕ) : ℤ) = (J : ℤ) - n := by
      rw [Nat.cast_sub (by omega)]
    rw [← hJn]
    have h1 : β ≤ ((J - n : ℕ) : ℤ) := by rw [hJn]; omega
    have h2 : ((J - n : ℕ) : ℤ) + (n : ℤ) = α + β - 2 := by rw [hJn]; omega
    exact lowering_composite_eq A ha hb hy (J - n) (n : ℤ) h1 h2
  · congr 1
    rw [topEvaluation_mk_mul, topEvaluation_mk, oLevW_homogeneous A 0 ha,
      oLevW_homogeneous A 0 hb]
    have h1 : (J : ℤ) - ((K : ℕ) : ℤ) = β - 1 + 0 := by omega
    have h2 : ((K : ℕ) : ℤ) = α - 1 + 0 := by omega
    rw [h1, h2]

end ZhuAlg

end VOA.Classification.COne.PlusRatTelescope
