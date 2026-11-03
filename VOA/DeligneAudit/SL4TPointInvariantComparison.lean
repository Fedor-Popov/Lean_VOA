import VOA.DeligneAudit.SL4TPointGradedComparison

/-! Equivariance of the leading-relation comparison and its exact invariant dimension. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {ι σ G : Type*} [Group G] [MulAction G ι]

/-- The representation on polynomials induced by permutation of their variables. -/
def polynomialPositionRepresentation (η : G →* Equiv.Perm σ) :
    Representation ℂ G (MvPolynomial σ ℂ) where
  toFun g := (MvPolynomial.rename (η g)).toLinearMap
  map_one' := by apply LinearMap.ext; intro p; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change rename (η (g * h)) p = rename (η g) (rename (η h) p)
    rw [rename_rename, map_mul]
    rfl

/-- Homogeneous projection commutes with permutation of polynomial variables. -/
theorem homogeneousComponent_rename_positions (e : Equiv.Perm σ)
    (p : MvPolynomial σ ℂ) (n : ℕ) :
    homogeneousComponent n (rename e p) = rename e (homogeneousComponent n p) := by
  classical
  have he := sum_homogeneousComponent p
  calc
    _ = homogeneousComponent n
        (rename e (∑ a ∈ Finset.range (p.totalDegree + 1), homogeneousComponent a p)) := by
          rw [he]
    _ = ∑ a ∈ Finset.range (p.totalDegree + 1),
        homogeneousComponent n (rename e (homogeneousComponent a p)) := by
          rw [map_sum, map_sum]
    _ = ∑ a ∈ Finset.range (p.totalDegree + 1),
        rename e (homogeneousComponent n (homogeneousComponent a p)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [homogeneousComponent_of_mem
            (homogeneousComponent_isHomogeneous a p).rename_isHomogeneous,
            homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous a p)]
          split_ifs <;> simp
    _ = _ := by rw [← map_sum, ← map_sum, he]

/-- Coordinate symmetries preserve the leading relation ideal. -/
theorem pointInitialIdeal_stable (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) (g : G) :
    (pointInitialIdeal x).restrictScalars ℂ ≤
      ((pointInitialIdeal x).restrictScalars ℂ).comap
        (polynomialPositionRepresentation η g) := by
  intro p hp n
  change finitePointEvaluation x (homogeneousComponent n (rename (η g) p)) ∈ _
  rw [homogeneousComponent_rename_positions, finitePointEvaluation_rename x η hx]
  exact pointDegreeFiltration_stable x η hx n g (hp n)

/-- The quotient representation on the leading-relation algebra of an equivariant point set. -/
def pointInitialRepresentation (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) :
    Representation ℂ G (MvPolynomial σ ℂ ⧸ pointInitialIdeal x) :=
  (polynomialPositionRepresentation η).quotient ((pointInitialIdeal x).restrictScalars ℂ)
    (pointInitialIdeal_stable x η hx)

/-- A product of complex representations acts componentwise. -/
def productRepresentation {κ : Type*} {V : κ → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) : Representation ℂ G (∀ i, V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := by ext v i; exact congrArg (fun f => f (v i)) (ρ i).map_one
  map_mul' g h := by ext v i; exact congrArg (fun f => f (v i)) ((ρ i).map_mul g h)

/-- Invariants of a product representation are the product of its invariant spaces. -/
def productRepresentationFixedEquiv {κ : Type*} {V : κ → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) :
    (productRepresentation ρ).invariants ≃ₗ[ℂ] (∀ i, (ρ i).invariants) where
  toFun v i := ⟨v.val i, fun g => congrFun (v.property g) i⟩
  invFun v := ⟨fun i => (v i).val, fun g => funext fun i => (v i).property g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The representation on the finitely many degree layers of point functions. -/
def pointGradedRepresentation (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) (d : ℕ) :
    Representation ℂ G ((n : Fin d) → PointDegreeLayer x n.val) :=
  productRepresentation fun n : Fin d =>
    stableFiltrationLayer pointFunctionRepresentation (pointDegreeFiltration x)
      (pointDegreeFiltration_stable x η hx) n.val

/-- The graded evaluation map intertwines position permutations. -/
theorem pointGradedEvaluation_equivariant (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s))
    (d : ℕ) (g : G) (p : MvPolynomial σ ℂ) :
    pointGradedEvaluation x d (polynomialPositionRepresentation η g p) =
      pointGradedRepresentation x η hx d g (pointGradedEvaluation x d p) := by
  funext n
  apply congrArg (((pointDegreeFiltration x n.val).comap
    (pointDegreeFiltration x (n.val + 1)).subtype).mkQ)
  apply Subtype.ext
  change finitePointEvaluation x (homogeneousComponent n.val (rename (η g) p)) =
    pointFunctionRepresentation g (finitePointEvaluation x (homogeneousComponent n.val p))
  rw [homogeneousComponent_rename_positions, finitePointEvaluation_rename x η hx]

/-- The leading-relation comparison is equivariant as a linear equivalence. -/
theorem pointInitialQuotientGradedEquiv_equivariant (x : ι → σ → ℂ)
    (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s))
    (d : ℕ) (hd : pointDegreeFiltration x d = ⊤) (g : G)
    (v : MvPolynomial σ ℂ ⧸ pointInitialIdeal x) :
    pointInitialQuotientGradedEquiv x d hd (pointInitialRepresentation x η hx g v) =
      pointGradedRepresentation x η hx d g (pointInitialQuotientGradedEquiv x d hd v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ p => exact pointGradedEvaluation_equivariant x η hx d g p

/-- The invariant dimension of the leading-relation algebra equals the number of point orbits. -/
theorem pointInitialQuotient_fixed_finrank [Fintype G] [Fintype ι]
    (x : ι → σ → ℂ) (hinj : Function.Injective x) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) :
    Module.finrank ℂ (pointInitialRepresentation x η hx).invariants =
      Nat.card (MulAction.orbitRel.Quotient G ι) := by
  obtain ⟨d, hd⟩ := pointDegreeFiltration_eventually_top x hinj
  let e := representationFixedEquiv (pointInitialRepresentation x η hx)
    (pointGradedRepresentation x η hx d) (pointInitialQuotientGradedEquiv x d hd)
    (pointInitialQuotientGradedEquiv_equivariant x η hx d hd)
  let ρ := fun n : Fin d => stableFiltrationLayer pointFunctionRepresentation
    (pointDegreeFiltration x) (pointDegreeFiltration_stable x η hx) n.val
  rw [e.finrank_eq]
  change Module.finrank ℂ (productRepresentation ρ).invariants = _
  rw [(productRepresentationFixedEquiv ρ).finrank_eq, Module.finrank_pi_fintype]
  have h := stableFiltration_fixed_finrank pointFunctionRepresentation
    (pointDegreeFiltration x) (pointDegreeFiltration_stable x η hx)
    (pointDegreeFiltration_mono x) (pointDegreeFiltration_zero x) d hd
  exact (Fin.sum_univ_eq_sum_range (fun n => Module.finrank ℂ
    (stableFiltrationLayer pointFunctionRepresentation (pointDegreeFiltration x)
      (pointDegreeFiltration_stable x η hx) n).invariants) d).trans
    (h.trans (pointFunction_fixed_finrank (G := G) (ι := ι)))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.homogeneousComponent_rename_positions
#print axioms VOA.DeligneAudit.SL4T.pointInitialIdeal_stable
#print axioms VOA.DeligneAudit.SL4T.pointGradedEvaluation_equivariant
#print axioms VOA.DeligneAudit.SL4T.pointInitialQuotientGradedEquiv_equivariant
#print axioms VOA.DeligneAudit.SL4T.pointInitialQuotient_fixed_finrank
