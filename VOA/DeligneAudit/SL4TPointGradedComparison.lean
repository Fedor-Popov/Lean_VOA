import VOA.DeligneAudit.SL4TPointInitialIdeal

/-! The leading-relation quotient is the graded vector space of finite point functions. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {ι σ : Type*}

/-- One successive quotient of the degree filtration on point functions. -/
abbrev PointDegreeLayer (x : ι → σ → ℂ) (n : ℕ) :=
  pointDegreeFiltration x (n + 1) ⧸
    (pointDegreeFiltration x n).comap (pointDegreeFiltration x (n + 1)).subtype

/-- Evaluation of one homogeneous component, followed by passage to its degree layer. -/
def pointDegreeLayerMap (x : ι → σ → ℂ) (n : ℕ) :
    MvPolynomial σ ℂ →ₗ[ℂ] PointDegreeLayer x n :=
  ((pointDegreeFiltration x n).comap (pointDegreeFiltration x (n + 1)).subtype).mkQ.comp
    (((finitePointEvaluation x).toLinearMap.comp (homogeneousComponent n)).codRestrict
      (pointDegreeFiltration x (n + 1)) (fun p => Submodule.subset_span
        ⟨homogeneousComponent n p,
          (homogeneousComponent_isHomogeneous n p).totalDegree_le.trans_lt
            (Nat.lt_succ_self n), rfl⟩))

/-- A degree-layer evaluation vanishes exactly when that component has lower-degree values. -/
theorem pointDegreeLayerMap_eq_zero (x : ι → σ → ℂ) (n : ℕ) (p : MvPolynomial σ ℂ) :
    pointDegreeLayerMap x n p = 0 ↔
      finitePointEvaluation x (homogeneousComponent n p) ∈ pointDegreeFiltration x n :=
  Submodule.Quotient.mk_eq_zero _

/-- Every point-function degree layer is represented by a homogeneous polynomial. -/
theorem pointDegreeLayerMap_surjective (x : ι → σ → ℂ) (n : ℕ) :
    Function.Surjective (pointDegreeLayerMap x n) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ f =>
      obtain ⟨p, hp, he⟩ := (pointDegreeFiltration_succ_mem x n f.val).mp f.property
      refine ⟨p, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      change finitePointEvaluation x (homogeneousComponent n p) - f.val ∈
        pointDegreeFiltration x n
      rw [← he]
      exact sub_mem_comm_iff.mp
        (pointDegreeFiltration_lowerDifference x p n hp)

/-- Homogeneous projection is diagonal for the degree-layer evaluation maps. -/
theorem pointDegreeLayerMap_component (x : ι → σ → ℂ) (m n : ℕ)
    (p : MvPolynomial σ ℂ) :
    pointDegreeLayerMap x m (homogeneousComponent n p) =
      if m = n then pointDegreeLayerMap x m p else 0 := by
  classical
  by_cases h : m = n
  · subst m
    rw [if_pos rfl]
    apply congrArg
      (((pointDegreeFiltration x n).comap (pointDegreeFiltration x (n + 1)).subtype).mkQ)
    apply Subtype.ext
    change finitePointEvaluation x
      (homogeneousComponent n (homogeneousComponent n p)) = _
    rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous n p), if_pos rfl]
    rfl
  · rw [if_neg h, pointDegreeLayerMap_eq_zero]
    rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous n p), if_neg h,
      map_zero]
    exact Submodule.zero_mem _

/-- Evaluation into all degree layers below a fixed cutoff. -/
def pointGradedEvaluation (x : ι → σ → ℂ) (d : ℕ) :
    MvPolynomial σ ℂ →ₗ[ℂ] ((n : Fin d) → PointDegreeLayer x n.val) :=
  LinearMap.pi fun n => pointDegreeLayerMap x n.val

/-- The homogeneous components independently generate all degree layers. -/
theorem pointGradedEvaluation_surjective (x : ι → σ → ℂ) (d : ℕ) :
    Function.Surjective (pointGradedEvaluation x d) := by
  classical
  intro f
  choose p hp using fun n : Fin d => pointDegreeLayerMap_surjective x n.val (f n)
  refine ⟨∑ n : Fin d, homogeneousComponent n.val (p n), ?_⟩
  funext m
  change pointDegreeLayerMap x m.val _ = f m
  rw [map_sum]
  simp only [pointDegreeLayerMap_component, Fin.val_inj]
  simpa using hp m

/-- Once the filtration stabilizes, its graded evaluation kernel is the leading relation ideal. -/
theorem pointGradedEvaluation_kernel (x : ι → σ → ℂ) (d : ℕ)
    (hd : pointDegreeFiltration x d = ⊤) :
    LinearMap.ker (pointGradedEvaluation x d) = (pointInitialIdeal x).restrictScalars ℂ := by
  ext p
  change pointGradedEvaluation x d p = 0 ↔
    ∀ n, finitePointEvaluation x (homogeneousComponent n p) ∈ pointDegreeFiltration x n
  constructor
  · intro h n
    by_cases hn : n < d
    · exact (pointDegreeLayerMap_eq_zero x n p).mp (congrFun h ⟨n, hn⟩)
    · have ht : pointDegreeFiltration x n = ⊤ :=
        top_unique (hd ▸ pointDegreeFiltration_mono x (Nat.le_of_not_gt hn))
      rw [ht]
      trivial
  · intro h
    funext n
    exact (pointDegreeLayerMap_eq_zero x n.val p).mpr (h n.val)

/-- The leading-relation quotient is linearly equivalent to the graded point functions. -/
def pointInitialQuotientGradedEquiv (x : ι → σ → ℂ) (d : ℕ)
    (hd : pointDegreeFiltration x d = ⊤) :
    (MvPolynomial σ ℂ ⧸ pointInitialIdeal x) ≃ₗ[ℂ]
      ((n : Fin d) → PointDegreeLayer x n.val) :=
  (Submodule.quotEquivOfEq _ _ (pointGradedEvaluation_kernel x d hd).symm).trans
    ((pointGradedEvaluation x d).quotKerEquivOfSurjective
      (pointGradedEvaluation_surjective x d))

/-- The dimensions of the point-function layers telescope to the full point-function dimension. -/
theorem pointDegreeLayer_finrank_sum [Fintype ι] (x : ι → σ → ℂ) (d : ℕ)
    (hd : pointDegreeFiltration x d = ⊤) :
    (∑ n ∈ Finset.range d, Module.finrank ℂ (PointDegreeLayer x n)) = Fintype.card ι := by
  have hstep (n : ℕ) : Module.finrank ℂ (PointDegreeLayer x n) +
      Module.finrank ℂ (pointDegreeFiltration x n) =
        Module.finrank ℂ (pointDegreeFiltration x (n + 1)) := by
    have h := ((pointDegreeFiltration x n).comap
      (pointDegreeFiltration x (n + 1)).subtype).finrank_quotient_add_finrank
    rw [← Submodule.finrank_map_subtype_eq (pointDegreeFiltration x (n + 1)),
      Submodule.map_comap_subtype,
      inf_eq_right.mpr (pointDegreeFiltration_mono x (Nat.le_succ n))] at h
    exact h
  have hsum : ∀ m, (∑ n ∈ Finset.range m, Module.finrank ℂ (PointDegreeLayer x n)) =
      Module.finrank ℂ (pointDegreeFiltration x m) := by
    intro m
    induction m with
    | zero => rw [pointDegreeFiltration_zero]; simp
    | succ m ih => rw [Finset.sum_range_succ, ih, add_comm]; exact hstep m
  have h := hsum d
  rw [hd, finrank_top, Module.finrank_pi] at h
  exact h

/-- Taking leading homogeneous relations preserves the number of finite distinct points. -/
theorem pointInitialQuotient_finrank [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) :
    FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ pointInitialIdeal x) ∧
      Module.finrank ℂ (MvPolynomial σ ℂ ⧸ pointInitialIdeal x) = Fintype.card ι := by
  obtain ⟨d, hd⟩ := pointDegreeFiltration_eventually_top x hx
  let e := pointInitialQuotientGradedEquiv x d hd
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  exact (Fin.sum_univ_eq_sum_range (fun n => Module.finrank ℂ (PointDegreeLayer x n)) d).trans
    (pointDegreeLayer_finrank_sum x d hd)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.pointDegreeLayerMap_eq_zero
#print axioms VOA.DeligneAudit.SL4T.pointDegreeLayerMap_surjective
#print axioms VOA.DeligneAudit.SL4T.pointDegreeLayerMap_component
#print axioms VOA.DeligneAudit.SL4T.pointGradedEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.pointGradedEvaluation_kernel
#print axioms VOA.DeligneAudit.SL4T.pointDegreeLayer_finrank_sum
#print axioms VOA.DeligneAudit.SL4T.pointInitialQuotient_finrank
