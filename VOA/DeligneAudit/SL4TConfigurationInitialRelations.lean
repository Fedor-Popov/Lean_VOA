import VOA.DeligneAudit.SL4TConfigurationPointDescent

/-! Elementary and root-power relations in the initial ideal of stratum configurations. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {ι σ : Type*}

/-- The top component of a product is the product of the two bounded top components. -/
theorem homogeneousComponent_mul_top (p q : MvPolynomial σ ℂ) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogeneousComponent (m + n) (p * q) =
      homogeneousComponent m p * homogeneousComponent n q := by
  classical
  have he : p * q = ∑ a ∈ Finset.range (m + 1),
      ∑ b ∈ Finset.range (n + 1), homogeneousComponent a p * homogeneousComponent b q := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul,
      homogeneousComponents_sum_upto p m hp, homogeneousComponents_sum_upto q n hq]
  rw [he, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [map_sum, Finset.sum_eq_single n]
    · rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous m p).mul
          (homogeneousComponent_isHomogeneous n q)), if_pos rfl]
    · intro b hb hbn
      rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous m p).mul
          (homogeneousComponent_isHomogeneous b q)), if_neg (by omega)]
    · simp
  · intro a ha ham
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b hb
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous a p).mul
        (homogeneousComponent_isHomogeneous b q)), if_neg (by
          have ha' := Finset.mem_range.mp ha
          have hb' := Finset.mem_range.mp hb
          omega)]
  · simp

/-- A product of affine factors in one variable is monic in its highest total degree. -/
theorem affineRootProduct_top (i : σ) (zs : List ℂ) :
    let p : MvPolynomial σ ℂ := (zs.map fun z => X i - MvPolynomial.C z).prod
    p.totalDegree ≤ zs.length ∧ homogeneousComponent zs.length p = X i ^ zs.length := by
  classical
  induction zs with
  | nil => simp
  | cons z zs ih =>
      dsimp only [List.map_cons, List.prod_cons, List.length_cons] at ih ⊢
      have ha : (X i - MvPolynomial.C z : MvPolynomial σ ℂ).totalDegree ≤ 1 := by
        exact (totalDegree_sub _ _).trans (by simp)
      have hc : homogeneousComponent 1 (X i - MvPolynomial.C z : MvPolynomial σ ℂ) = X i := by
        rw [map_sub, homogeneousComponent_of_mem (isHomogeneous_X ℂ i),
          if_pos rfl, homogeneousComponent_eq_zero 1 (MvPolynomial.C z) (by simp), sub_zero]
      refine ⟨(totalDegree_mul _ _).trans (by omega), ?_⟩
      rw [show zs.length + 1 = 1 + zs.length by omega,
        homogeneousComponent_mul_top _ _ 1 zs.length ha ih.1, hc, ih.2]
      rw [pow_add, pow_one]

/-- If a coordinate takes values at finitely many sites, its cutoff power is a leading relation. -/
theorem pointInitialIdeal_coordinate_power (x : ι → σ → ℂ) (N : ℕ)
    (ζ : Fin N → ℂ) (i : σ) (label : ι → Fin N)
    (hx : ∀ a, x a i = ζ (label a)) :
    (X i : MvPolynomial σ ℂ) ^ N ∈ pointInitialIdeal x := by
  classical
  let p : MvPolynomial σ ℂ := ((List.ofFn ζ).map fun z => X i - MvPolynomial.C z).prod
  have htop := affineRootProduct_top i (List.ofFn ζ)
  simp only [List.length_ofFn] at htop
  have hz : finitePointEvaluation x p = 0 := by
    funext a
    change MvPolynomial.aeval (x a) p = 0
    simp only [p, List.map_ofFn, List.prod_ofFn, map_prod, Function.comp_def,
      map_sub, aeval_X, aeval_C, hx]
    exact Finset.prod_eq_zero (Finset.mem_univ (label a)) (sub_self _)
  have h := pointInitialIdeal_of_vanishing x p hz N htop.1
  rwa [htop.2] at h

/-- A positive-degree homogeneous polynomial constant on the points is a leading relation. -/
theorem pointInitialIdeal_of_constant (x : ι → σ → ℂ) (p : MvPolynomial σ ℂ)
    (n : ℕ) (hn : 0 < n) (hp : p.IsHomogeneous n) (c : ℂ)
    (hc : finitePointEvaluation x p = fun _ => c) : p ∈ pointInitialIdeal x := by
  apply (pointInitialSubmodule_homogeneous x p n hp).mpr
  rw [hc]
  exact Submodule.subset_span ⟨MvPolynomial.C c, by simpa using hn, by
    ext a
    simp [finitePointEvaluation]⟩

/-- Two configurations with the same site multiplicities differ by a position permutation. -/
theorem fullFlagConfiguration_positionEquiv (B k : ℕ) (f g : FullFlagConfiguration B k) :
    ∃ e : Equiv.Perm (Fin B), ∀ i, g.val (e i) = f.val i := by
  classical
  have hc (a : Fin (B - k)) :
      Fintype.card {i : Fin B // f.val i = a} = Fintype.card {i : Fin B // g.val i = a} := by
    simpa only [Fintype.card_subtype] using (f.property a).trans (g.property a).symm
  let e := fun a => Classical.choice (Fintype.card_eq.mp (hc a))
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Symmetric polynomials have constant values on every full-flag configuration stratum. -/
theorem fullFlagStratumPoint_symmetric_constant (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) (p : MvPolynomial (Fin B) ℂ) (hp : p.IsSymmetric) :
    ∃ c : ℂ, finitePointEvaluation (fullFlagStratumPoint B k j Y ζ) p = fun _ => c := by
  classical
  by_cases hn : Nonempty (FullFlagStratumConfiguration B k j Y)
  · let f := Classical.choice hn
    refine ⟨MvPolynomial.aeval (fullFlagStratumPoint B k j Y ζ f) p, ?_⟩
    funext g
    obtain ⟨e, he⟩ := fullFlagConfiguration_positionEquiv B k f.val g.val
    have hx : fullFlagStratumPoint B k j Y ζ g ∘ e =
        fullFlagStratumPoint B k j Y ζ f := by ext i; exact congrArg ζ (he i)
    have h := congrArg (MvPolynomial.aeval (fullFlagStratumPoint B k j Y ζ g)) (hp e)
    rw [MvPolynomial.aeval_rename, hx] at h
    exact h.symm
  · refine ⟨0, funext fun f => False.elim (hn ⟨f⟩)⟩

/-- Elementary symmetric functions are homogeneous in their ordinary polynomial degree. -/
theorem elementarySymmetric_homogeneous {σ : Type*} [Fintype σ] (n : ℕ) :
    (esymm σ ℂ n).IsHomogeneous n := by
  classical
  unfold esymm
  apply IsHomogeneous.sum
  intro s hs
  have he := (Finset.mem_powersetCard.mp hs).2
  have h := IsHomogeneous.prod s (fun i => (X i : MvPolynomial σ ℂ))
    (fun _ => 1) (fun i _ => isHomogeneous_X ℂ i)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, he] using h

/-- All elementary and root-power relations lie in the initial ideal of the stratum points. -/
theorem fullFlagTruncationIdeal_le_pointInitialIdeal (B k j : ℕ) (Y : Finset (Fin B))
    (ζ : Fin (B - k) → ℂ) :
    fullFlagTruncationIdeal B (B - k) ≤
      pointInitialIdeal (fullFlagStratumPoint B k j Y ζ) := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro p ⟨n, hn, rfl⟩
    obtain ⟨c, hc⟩ := fullFlagStratumPoint_symmetric_constant B k j Y ζ
      (esymm (Fin B) ℂ n) (esymm_isSymmetric (Fin B) ℂ n)
    exact pointInitialIdeal_of_constant _ _ n hn (elementarySymmetric_homogeneous n) c hc
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact pointInitialIdeal_coordinate_power _ (B - k) ζ i (fun f => f.val.val i)
      (fun _ => rfl)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.homogeneousComponent_mul_top
#print axioms VOA.DeligneAudit.SL4T.affineRootProduct_top
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_coordinate_power
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_of_constant
#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_positionEquiv
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratumPoint_symmetric_constant
#print axioms VOA.DeligneAudit.SL4T.elementarySymmetric_homogeneous
#print axioms VOA.DeligneAudit.SL4T.fullFlagTruncationIdeal_le_pointInitialIdeal
