import VOA.DeligneAudit.LeviTypeA2CertGradedDefectConvert

/-! A common lower-mode span for every F₂ defect at one radical key. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

/-- Radical words of one key whose first-colour mode sum is below `σ`. -/
def a2ModeLowerSpan (a b d σ : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ xs ys : List ℕ,
    xs.length = a ∧ ys.length = b ∧ xs.sum + ys.sum = d ∧
      xs.sum < σ ∧
        v = (aWord (fun i => ρ.op 3 i) xs *
          (ys.map fun i => ρ.op 5 i).prod) w}

/-- The positional lower terms of one conversion lie in the common
lower span at its fixed radical key. -/
theorem a2_gradedLower_le_mode (xs ys : List ℕ) (k d : ℕ) :
    gradedLowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
      xs ys k d 1 w ≤
      a2ModeLowerSpan ρ w xs.length (ys.length + k) d xs.sum := by
  rw [gradedLowerModeSpan, a2ModeLowerSpan, Submodule.span_le]
  rintro z ⟨zs, bs, hza, hbs, hd, hsmall, rfl⟩
  exact Submodule.subset_span ⟨zs, bs, hza, hbs, hd, hsmall, by simp⟩

/-- The common lower-mode span remains in its stated radical key layer. -/
theorem a2ModeLowerSpan_le_key (a b d σ : ℕ) :
    a2ModeLowerSpan ρ w a b d σ ≤ a2KeyLayer ρ w ⟨a, b, d⟩ := by
  rw [a2ModeLowerSpan, Submodule.span_le]
  intro z hz
  obtain ⟨xs, ys, hxa, hyb, hdegree, _, rfl⟩ := hz
  let l : List (Fin 2 × ℕ) :=
    (xs.map fun s => ((0 : Fin 2), s)) ++
      (ys.map fun s => ((1 : Fin 2), s))
  have hkey : a2WordKey l = ⟨a, b, d⟩ := by
    simp [l, a2WordKey, List.countP_append, List.sum_append,
      List.map_map, Function.comp_def, hxa, hyb, hdegree]
  have hword : radicalWord (a2RadicalOp ρ) l • w =
      (aWord (fun i => ρ.op 3 i) xs *
        (ys.map fun i => ρ.op 5 i).prod) w := by
    simp [l, radicalWord, a2RadicalOp, aWord, List.map_append,
      List.map_map, Function.comp_def, List.prod_append, mul_smul]
  have hw := radicalWord_mem_own_key ρ w l
  rw [hword, hkey] at hw
  exact hw

/-- Every fixed-bidegree F₂ defect enters the same lower-mode span,
independent of the monomial multiplier chosen by the ideal expansion. -/
theorem a2_f2_defect_reduces_mode (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (xs : List ℕ) (f : ℕ →₀ ℕ) (k s b d₂ : ℕ)
    (hk : 1 ≤ k) (hks : q + 1 ≤ k + s)
    (hw : Finsupp.weight om f + (k, s) = (b, d₂)) :
    let F : ℕ → Module.End ℂ V := fun i => ρ.op 5 i
    let hFF : ∀ i j, F i * F j = F j * F i := by
      intro i j
      apply sub_eq_zero.mp
      simp [F, op_comm_end, Fin.sum_univ_eight,
        VOA.AffineSl3.bracketTable]
    (aWord (fun i => ρ.op 3 i) xs *
      Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1 * xx k s)) w ∈
      a2ModeLowerSpan ρ w xs.length b (xs.sum + d₂) xs.sum ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩) := by
  let ys := VOA.DeligneAudit.CLAssembly.lst f
  have hlen : ys.length + k = b := by
    dsimp [ys]
    rw [a2_lst_length]
    simpa using congrArg Prod.fst hw
  have h := a2_f2_explicit_defect_reduces ρ w p q h xs f k s b d₂
    hk hks hw
  have hle :
      gradedLowerModeSpan (fun i => ρ.op 3 i) (fun i => ρ.op 5 i)
        xs ys k (xs.sum + d₂) 1 w ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩) ≤
      a2ModeLowerSpan ρ w xs.length b (xs.sum + d₂) xs.sum ⊔
      a2LeviClosure ρ
        (a2HigherKeySpan ρ w q ⟨xs.length, b, xs.sum + d₂⟩) := by
    rw [← hlen]
    exact sup_le_sup_right (a2_gradedLower_le_mode ρ w xs ys k
      (xs.sum + d₂)) _
  exact hle h

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_gradedLower_le_mode
#print axioms VOA.DeligneAudit.A3Sector.a2ModeLowerSpan_le_key
#print axioms VOA.DeligneAudit.A3Sector.a2_f2_defect_reduces_mode
