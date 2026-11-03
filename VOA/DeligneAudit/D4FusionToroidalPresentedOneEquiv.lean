import VOA.DeligneAudit.D4FusionToroidalPresentedOneBridge
import VOA.DeligneAudit.D4FusionToroidalFinite

/-! Maps between the multiplicity-one toroidal and current presentations. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl

noncomputable section

theorem univOne_syntax :
    ∀ z ∈ JprimeSyntaxE 1,
      evalT univToroidalOne (wUG D4sector.f OneR) z = 0 := by
  intro z hz
  rcases hz with (⟨t, ht, rfl⟩ | ⟨j, N, hj, hjm, _, rfl⟩) | ⟨q, hq, rfl⟩
  · rw [evalT_swT, wordOpT_univ_symbol_one]
    exact (univG_sat D4sector.f OneR).tail t ht
  · omega
  · change evalT univToroidalOne (wUG D4sector.f OneR)
      (swT [(q.1, 0, 0)] - q.2 • swT []) = 0
    rw [map_sub, map_smul, evalT_swT, evalT_swT]
    change univToroidalOne.op q.1 0 0 (wUG D4sector.f OneR) -
      q.2 • wUG D4sector.f OneR = 0
    exact sub_eq_zero.mpr ((univG_sat D4sector.f OneR).eig q hq)

def oneToU : PTE 1 →ₗ[ℂ] OneU :=
  univMapT D4sector.f 1 (JprimeSyntaxE 1)
    univToroidalOne (wUG D4sector.f OneR) univOne_syntax

def oneToP : OneU →ₗ[ℂ] PTE 1 := univMapG presentedOne_sat

theorem oneToU_gen : oneToU (pTE 1) = wUG D4sector.f OneR :=
  univMapT_gen D4sector.f 1 (JprimeSyntaxE 1)
    univToroidalOne (wUG D4sector.f OneR) univOne_syntax

theorem oneToP_gen : oneToP (wUG D4sector.f OneR) = pTE 1 := by
  simpa [oneToP] using (univMapG_wordOp presentedOne_sat [])

theorem oneToU_op (c : Fin 28) (i s : ℕ) (x : PTE 1) :
    oneToU ((ρPTE 1).op c i s x) = univToroidalOne.op c i s (oneToU x) :=
  univMapT_op D4sector.f 1 (JprimeSyntaxE 1)
    univToroidalOne (wUG D4sector.f OneR) univOne_syntax c i s x

theorem oneToP_word (l : List (Ltr 28)) :
    oneToP (wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR)) =
      wordOp presentedCurrentOne l (pTE 1) :=
  univMapG_wordOp presentedOne_sat l

theorem oneToP_op (c : Fin 28) (i : ℕ) (x : OneU) :
    oneToP ((univRepG D4sector.f OneR).op c i x) =
      (ρPTE 1).op c i 0 (oneToP x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb =>
        simpa only [Submodule.Quotient.mk_add, map_add] using
          congrArg₂ (· + ·) ha hb
    | single l k =>
        have hk : Finsupp.single l k = k • UnivG.sw l := by simp [UnivG.sw]
        rw [hk, Submodule.Quotient.mk_smul, map_smul, map_smul, map_smul]
        change k • oneToP (opU D4sector.f OneR (c, i)
          (Submodule.Quotient.mk (UnivG.sw l))) = _
        rw [UnivG.opU_mk, ← wordOp_univG D4sector.f OneR ((c, i) :: l),
          oneToP_word]
        rw [← wordOp_univG D4sector.f OneR l, oneToP_word]
        simp only [wordOp, map_smul, presentedCurrentOne]

theorem oneToP_toroidal_op (c : Fin 28) (i s : ℕ) (x : OneU) :
    oneToP (univToroidalOne.op c i s x) = (ρPTE 1).op c i s (oneToP x) := by
  by_cases hs : s = 0
  · subst s
    simpa [univToroidalOne] using oneToP_op c i x
  · have hs1 : 1 ≤ s := by omega
    simp [univToroidalOne, hs, (ρPTE 1).high_zero c i s hs1]

theorem oneToP_toU_word (l : List (TLtr 28)) :
    oneToP (oneToU (wordOpT (ρPTE 1) l (pTE 1))) =
      wordOpT (ρPTE 1) l (pTE 1) := by
  induction l with
  | nil => simp [oneToU_gen, oneToP_gen, wordOpT]
  | cons x l ih =>
      change oneToP (oneToU ((ρPTE 1).op x.1 x.2.1 x.2.2
        (wordOpT (ρPTE 1) l (pTE 1)))) = _
      rw [oneToU_op, oneToP_toroidal_op]
      exact congrArg ((ρPTE 1).op x.1 x.2.1 x.2.2) ih

theorem oneToU_toP_word (l : List (Ltr 28)) :
    oneToU (oneToP (wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR))) =
      wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR) := by
  induction l with
  | nil => simp [oneToP_gen, oneToU_gen, wordOp]
  | cons x l ih =>
      change oneToU (oneToP ((univRepG D4sector.f OneR).op x.1 x.2
        (wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR)))) = _
      rw [oneToP_op, oneToU_op]
      simpa [univToroidalOne] using
        congrArg ((univRepG D4sector.f OneR).op x.1 x.2) ih

def presentedOneEquiv : PTE 1 ≃ₗ[ℂ] OneU where
  toFun := oneToU
  invFun := oneToP
  left_inv := by
    intro x
    have hx : x ∈ Submodule.span ℂ
        (Set.range fun l : List (TLtr 28) => wordOpT (ρPTE 1) l (pTE 1)) := by
      rw [PTE_cyclic]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact oneToP_toU_word l
    | zero => exact map_zero _
    | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | smul a x _ hx => simpa only [map_smul] using congrArg (a • ·) hx
  right_inv := by
    intro x
    have hx : x ∈ Submodule.span ℂ
        (Set.range fun l : List (Ltr 28) =>
          wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR)) := by
      have htop : Submodule.span ℂ
          (Set.range fun l : List (Ltr 28) =>
            wordOp (univRepG D4sector.f OneR) l (wUG D4sector.f OneR)) = ⊤ :=
        D4FusionContact.Polynomial.universal_word_span D4sector.f OneR
      exact htop.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact oneToU_toP_word l
    | zero => exact map_zero _
    | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | smul a x _ hx => simpa only [map_smul] using congrArg (a • ·) hx
  map_add' := oneToU.map_add
  map_smul' := oneToU.map_smul

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.univOne_syntax
#print axioms VOA.DeligneAudit.Toroidal.oneToP_toU_word
#print axioms VOA.DeligneAudit.Toroidal.oneToU_toP_word
#print axioms VOA.DeligneAudit.Toroidal.presentedOneEquiv
