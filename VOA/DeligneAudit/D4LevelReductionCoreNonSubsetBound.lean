import VOA.DeligneAudit.D4LevelReductionCoreRaisedTruncation

/-! The raised submodule and highest-weight quotient bound every non-subset core cell. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (Q : CurrentModule A3Sector.bracketTable V) (v : V) (b : ℕ)
variable (h : SingleAdjointCellRelations Q v b)

/-- The quotient current action after killing the middle-raised cyclic submodule. -/
def singleAdjointRaisedQuotient :=
  quotRepG Q (cycSubG Q (Q.op 3 0 v)) (cycSubG_inv Q (Q.op 3 0 v))

include h

/-- Killing the raised submodule makes the original vector a local Weyl highest vector. -/
theorem singleAdjoint_quotient_localWeyl :
    A3Sector.LocalWeylRel (singleAdjointRaisedQuotient Q v)
      ((cycSubG Q (Q.op 3 0 v)).mkQ v) (A3Sector.weightABC 1 b 1) := by
  let N := cycSubG Q (Q.op 3 0 v)
  let R := singleAdjointRaisedQuotient Q v
  let w := N.mkQ v
  have he : ∀ e : Fin 15, e.val < 6 → ∀ s, R.op e s w = 0 := by
    intro e he s
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    by_cases heq : e = 3
    · subst e
      by_cases hs : s = 0
      · subst s
        exact wordOp_mem_cycSubG Q (Q.op 3 0 v) []
      · rw [h.middle s (by omega)]
        exact Submodule.zero_mem _
    · rw [h.parabolic e he heq s]
      exact Submodule.zero_mem _
  have hh : ∀ j, R.op (A3Sector.simpleH j) 0 w =
      (A3Sector.weightABC 1 b 1 j : ℂ) • w := by
    intro j
    change N.mkQ (Q.op (A3Sector.simpleH j) 0 v) = _
    rw [h.weight, map_smul]
  refine ⟨he, ?_, hh, ?_⟩
  · intro j s hs
    change N.mkQ (Q.op (A3Sector.simpleH j) s v) = 0
    rw [h.cartan j s hs, map_zero]
  · intro j
    exact coreFinite_simple_lowering R w j _ (he _ (A3Sector.simpleE_raising j) 0) (hh j)

/-- The cyclic span maps onto the cyclic span of its quotient generator. -/
theorem singleAdjoint_cyclic_quotient :
    (cycSubG Q v).map (cycSubG Q (Q.op 3 0 v)).mkQ =
      cycSubG (singleAdjointRaisedQuotient Q v) ((cycSubG Q (Q.op 3 0 v)).mkQ v) := by
  let N := cycSubG Q (Q.op 3 0 v)
  change (Submodule.span ℂ (Set.range fun l : List (Ltr 15) => wordOp Q l v)).map N.mkQ =
    Submodule.span ℂ (Set.range fun l : List (Ltr 15) =>
      wordOp (singleAdjointRaisedQuotient Q v) l (N.mkQ v))
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, quot_wordOpG Q _ (cycSubG_inv Q (Q.op 3 0 v)) v l⟩
  · rintro ⟨l, rfl⟩
    exact ⟨wordOp Q l v, ⟨l, rfl⟩,
      (quot_wordOpG Q _ (cycSubG_inv Q (Q.op 3 0 v)) v l).symm⟩

/-- The highest-weight quotient has the local Weyl bound for weight theta plus middle labels. -/
theorem singleAdjoint_quotient_rank :
    Module.finrank ℂ ((cycSubG Q v).map (cycSubG Q (Q.op 3 0 v)).mkQ) ≤ 16 * 6 ^ b := by
  rw [singleAdjoint_cyclic_quotient Q v b h]
  have hb := (A3Sector.a3_all_weight_rank (singleAdjointRaisedQuotient Q v)
    ((cycSubG Q (Q.op 3 0 v)).mkQ v) 1 b 1 (singleAdjoint_quotient_localWeyl Q v b h)).2
  simpa only [pow_one, show (4 : ℕ) * 6 ^ b * 4 = 16 * 6 ^ b by ring] using hb

/-- The raised submodule and its quotient give the exterior-pair bound on the cyclic cell. -/
theorem singleAdjoint_cyclic_rank : Module.finrank ℂ (cycSubG Q v) ≤ 6 ^ (b + 2) := by
  have hdim := finrank_le_map_add_infG (cycSubG Q (Q.op 3 0 v)).mkQ (cycSubG Q v)
  have hker : Module.finrank ℂ
      (cycSubG Q v ⊓ LinearMap.ker (cycSubG Q (Q.op 3 0 v)).mkQ : Submodule ℂ V) ≤
        Module.finrank ℂ (cycSubG Q (Q.op 3 0 v)) := by
    apply Submodule.finrank_mono
    rw [Submodule.ker_mkQ]
    exact inf_le_right
  have hr := singleAdjoint_raised_rank Q v b h
  have hq := singleAdjoint_quotient_rank Q v b h
  have he : 6 ^ (b + 2) = 20 * 6 ^ b + 16 * 6 ^ b := by
    rw [pow_add]
    ring
  omega

omit h

/-- Every single-adjoint cell satisfies the parabolic and Cartan presentation used above. -/
theorem coreCell_singleAdjoint_relations (b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing 1 b c →ₗ[ℂ] V)
    (h : CoreRelations Q 1 b c π) (F : CoreCellFlag 1 b c)
    (i : ℕ) (hi : i < (coreCellCatalog 1 b c).length) :
    SingleAdjointCellRelations (coreIdealQuotientCurrent 1 b c Q π (F.ideal i))
      ((coreCellFiltration 1 b c Q π F i).mkQ (π (F.generator i))) b where
  parabolic e he hne r := by
    change (coreCellFiltration 1 b c Q π F i).mkQ (Q.op e r (π (F.generator i))) = 0
    rw [h.parabolic e he hne, map_zero]
  weight := coreCellGenerator_weight 1 b c Q π h F i
  cartan := coreCellGenerator_cartan_zero 1 b c Q π h F i hi
  middle s hs := (Submodule.Quotient.mk_eq_zero _).mpr
    (coreCellGenerator_middle_raising_truncation 1 b c Q π h F i hi s hs)

/-- In particular every non-subset cell has the required exterior-pair rank bound. -/
theorem coreCell_singleAdjoint_pair_rank (b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing 1 b c →ₗ[ℂ] V)
    (h : CoreRelations Q 1 b c π) (F : CoreCellFlag 1 b c)
    (i : ℕ) (hi : i < (coreCellCatalog 1 b c).length) :
    Module.finrank ℂ (coreCellPiece 1 b c Q π F i) ≤ 6 ^ (b + 2) := by
  rw [coreCellPiece_cyclic 1 b c Q π F i hi]
  exact singleAdjoint_cyclic_rank (coreIdealQuotientCurrent 1 b c Q π (F.ideal i))
    ((coreCellFiltration 1 b c Q π F i).mkQ (π (F.generator i))) b
    (coreCell_singleAdjoint_relations b c Q π h F i hi)

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_quotient_localWeyl
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_cyclic_quotient
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_quotient_rank
#print axioms VOA.DeligneAudit.D4LevelReduction.singleAdjoint_cyclic_rank
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_singleAdjoint_relations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCell_singleAdjoint_pair_rank
