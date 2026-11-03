import VOA.DeligneAudit.SL4TInvariantFiltration

/-! The degree filtration on finite point functions and its invariant orbit count. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {ι σ G : Type*}

/-- Functions represented by polynomials of degree strictly below the filtration index. -/
def pointDegreeFiltration (x : ι → σ → ℂ) (n : ℕ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ {f | ∃ p : MvPolynomial σ ℂ,
    p.totalDegree < n ∧ finitePointEvaluation x p = f}

/-- The degree filtration begins with the zero subspace. -/
theorem pointDegreeFiltration_zero (x : ι → σ → ℂ) : pointDegreeFiltration x 0 = ⊥ := by
  apply le_antisymm (Submodule.span_le.mpr ?_) bot_le
  rintro f ⟨p, hp, _⟩
  omega

/-- Increasing the degree bound enlarges the point-function filtration. -/
theorem pointDegreeFiltration_mono (x : ι → σ → ℂ) :
    Monotone (pointDegreeFiltration x) := by
  intro m n h
  apply Submodule.span_mono
  rintro f ⟨p, hp, rfl⟩
  exact ⟨p, hp.trans_le h, rfl⟩

/-- Interpolation makes the degree filtration exhaustive for distinct finite points. -/
theorem pointDegreeFiltration_exhaustive [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) : (⨆ n, pointDegreeFiltration x n) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨p, rfl⟩ := finitePointEvaluation_surjective x hx f
  apply (le_iSup (pointDegreeFiltration x) (p.totalDegree + 1))
  exact Submodule.subset_span ⟨p, Nat.lt_succ_self _, rfl⟩

/-- A single finite degree bound suffices to represent every point function. -/
theorem pointDegreeFiltration_eventually_top [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) : ∃ d, pointDegreeFiltration x d = ⊤ := by
  classical
  have hc : IsCompactElement (⊤ : Submodule ℂ (ι → ℂ)) :=
    (Submodule.fg_iff_compact _).mp (Module.Finite.iff_fg.mp inferInstance)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (Submodule ℂ (ι → ℂ)) hc (pointDegreeFiltration x)
    (by rw [pointDegreeFiltration_exhaustive x hx])
  refine ⟨s.sup id, top_unique (hs.trans ?_)⟩
  exact iSup_le fun n => iSup_le fun hn =>
    pointDegreeFiltration_mono x (Finset.le_sup (f := id) hn)

variable [Group G] [MulAction G ι]

/-- The complex representation on point functions obtained from the permutation action. -/
def pointFunctionRepresentation : Representation ℂ G (ι → ℂ) :=
  (AlgEquiv.toLinearMapHom ℂ (ι → ℂ)).comp (pointFunctionAction (G := G))

/-- Coordinate permutations give the same action after evaluation on an equivariant point set. -/
theorem finitePointEvaluation_rename (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s))
    (g : G) (p : MvPolynomial σ ℂ) :
    finitePointEvaluation x (MvPolynomial.rename (η g) p) =
      pointFunctionRepresentation (G := G) g (finitePointEvaluation x p) := by
  funext i
  change MvPolynomial.aeval (x i) (MvPolynomial.rename (η g) p) =
    MvPolynomial.aeval (x (g⁻¹ • i)) p
  rw [MvPolynomial.aeval_rename]
  have he : x i ∘ η g = x (g⁻¹ • i) := funext fun s => (hx g i s).symm
  rw [he]

/-- Coordinate permutations preserve the degree filtration on point functions. -/
theorem pointDegreeFiltration_stable (x : ι → σ → ℂ) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) (n : ℕ) (g : G) :
    pointDegreeFiltration x n ≤
      (pointDegreeFiltration x n).comap (pointFunctionRepresentation (G := G) g) := by
  apply Submodule.span_le.mpr
  rintro f ⟨p, hp, rfl⟩
  change pointFunctionRepresentation (G := G) g (finitePointEvaluation x p) ∈
    pointDegreeFiltration x n
  rw [← finitePointEvaluation_rename x η hx]
  exact Submodule.subset_span ⟨MvPolynomial.rename (η g) p,
    (MvPolynomial.totalDegree_rename_le _ _).trans_lt hp, rfl⟩

/-- Fixed dimension of the graded point-function layers equals the number of point orbits. -/
theorem pointDegreeFiltration_fixed_count [Fintype G] [Fintype ι]
    (x : ι → σ → ℂ) (hinj : Function.Injective x) (η : G →* Equiv.Perm σ)
    (hx : ∀ (g : G) i s, x (g⁻¹ • i) s = x i (η g s)) :
    ∃ d, pointDegreeFiltration x d = ⊤ ∧
      (∑ n ∈ Finset.range d, Module.finrank ℂ
        (stableFiltrationLayer pointFunctionRepresentation (pointDegreeFiltration x)
          (pointDegreeFiltration_stable x η hx) n).invariants) =
            Nat.card (MulAction.orbitRel.Quotient G ι) := by
  obtain ⟨d, hd⟩ := pointDegreeFiltration_eventually_top x hinj
  refine ⟨d, hd, ?_⟩
  rw [stableFiltration_fixed_finrank pointFunctionRepresentation (pointDegreeFiltration x)
    (pointDegreeFiltration_stable x η hx) (pointDegreeFiltration_mono x)
    (pointDegreeFiltration_zero x) d hd]
  exact pointFunction_fixed_finrank (G := G) (ι := ι)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_zero
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_mono
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_exhaustive
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_eventually_top
#print axioms VOA.DeligneAudit.SL4T.finitePointEvaluation_rename
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_stable
#print axioms VOA.DeligneAudit.SL4T.pointDegreeFiltration_fixed_count
