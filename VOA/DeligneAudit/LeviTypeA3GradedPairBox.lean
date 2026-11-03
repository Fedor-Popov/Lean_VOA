import VOA.DeligneAudit.LeviTypeA3GradedPairMode

/-! The homogeneous Garland box for either adjacent pair at one radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

def a3PairBoxSpan (j : Fin 2) (xs zs : List ℕ)
    (m t d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ f : ℕ →₀ ℕ,
    BoxP m f ∧ Finsupp.weight om f = (t, d) ∧
      v = (aWord (fun i => ρ.op (F (a3ConvA j)) i) xs *
        Sl2Weyl.evAlg (fun i => ρ.op (F (a3ConvB j)) i)
          (a3_convB_comm ρ j) (MvPolynomial.monomial f 1)) (
            (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod w)}

theorem a3_pair_box_fixed_key (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (j : Fin 2) (xs zs : List ℕ) (t d : ℕ) {P : R}
    (hP : P.IsWeightedHomogeneous om (t, d)) :
    let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
    let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
    let R : Module.End ℂ V :=
      (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
    let m := (weightABC a b c) (Fin.succ j)
    let K : A3RadicalKey :=
      if j = 0 then ⟨xs.length, t, zs.length, xs.sum + d + zs.sum⟩
      else ⟨zs.length, xs.length, t, xs.sum + d + zs.sum⟩
    (aWord A xs * Sl2Weyl.evAlg B (a3_convB_comm ρ j) P) (R w) ∈
      a3PairBoxSpan ρ w j xs zs m t d ⊔
        (a3PairModeLowerSpan ρ w j zs xs.length t (xs.sum + d) xs.sum ⊔
          a3HigherLeviClosure ρ w b c K) := by
  let A : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvA j)) i
  let B : ℕ → Module.End ℂ V := fun i => ρ.op (F (a3ConvB j)) i
  let R : Module.End ℂ V :=
    (zs.map fun i => ρ.op (F (a3ConvSpectator j)) i).prod
  let m := (weightABC a b c) (Fin.succ j)
  let K : A3RadicalKey :=
    if j = 0 then ⟨xs.length, t, zs.length, xs.sum + d + zs.sum⟩
    else ⟨zs.length, xs.length, t, xs.sum + d + zs.sum⟩
  let T : Module.End ℂ V := aWord A xs
  let Bspan := a3PairBoxSpan ρ w j xs zs m t d
  let N := a3PairModeLowerSpan ρ w j zs xs.length t
      (xs.sum + d) xs.sum ⊔ a3HigherLeviClosure ρ w b c K
  have hmapB : ∀ v ∈ Submodule.span ℂ
      {z | ∃ f, BoxP m f ∧ Finsupp.weight om f = (t, d) ∧
        z = Sl2Weyl.evAlg B (a3_convB_comm ρ j)
          (MvPolynomial.monomial f 1) (R w)}, T v ∈ Bspan := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, hf, hw, rfl⟩ := hv
        exact Submodule.subset_span ⟨f, hf, hw, rfl⟩
    | zero => simp
    | add v z _ _ hv hz =>
        rw [map_add]
        exact Bspan.add_mem hv hz
    | smul x v _ hv =>
        rw [map_smul]
        exact Bspan.smul_mem x hv
  have hmapD : ∀ v ∈ a2GradedDefect B (a3_convB_comm ρ j)
      (R w) m (t, d), T v ∈ N := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, k, s, hk, hks, hw, rfl⟩ := hv
        have h := a3_defect_reduces_pairMode ρ w a b c h j xs zs f
          k s t d hk hks hw
        have hlen : (VOA.DeligneAudit.CLAssembly.lst f).length + k = t := by
          rw [a2_lst_length]
          have ht := congrArg Prod.fst hw
          simp only [Prod.fst_add] at ht
          omega
        have hK : a3ConvKey j k (xs.sum + d + zs.sum) xs
            (VOA.DeligneAudit.CLAssembly.lst f) zs = K := by
          fin_cases j <;> simp [a3ConvKey, K, hlen]
        simpa only [A, B, R, N, hK] using h
    | zero => simp
    | add v z _ _ hv hz =>
        rw [map_add]
        exact N.add_mem hv hz
    | smul x v _ hv =>
        rw [map_smul]
        exact N.smul_mem x hv
  obtain ⟨vB, hvB, vD, hvD, hsum⟩ := Submodule.mem_sup.mp
    (a2_span_box_graded_explicit_eval B (a3_convB_comm ρ j)
      (R w) m hP)
  change T (Sl2Weyl.evAlg B (a3_convB_comm ρ j) P (R w)) ∈
    Bspan ⊔ N
  rw [← hsum, map_add]
  exact Submodule.add_mem_sup (hmapB vB hvB) (hmapD vD hvD)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_pair_box_fixed_key
