/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionKernel

/-!
# The universal modules `U_{a,b}`

`U_{a,b}` is the free vector space on loop words modulo the span `J a b` of all commutation
instances and all instances of the `MabRel a b` relations, each with an arbitrary prefix.  Prepending a
letter preserves `J`, so it descends: this is the `sl₃[t]`-action `univRep a b`, with generator
`wU = [[]]` satisfying `MabRel` (`univ_mabRel`).  Every module with `MabRel a b` receives a map
`univMap` sending `[[l]]` to `wordOp ρ l w` (`univMap_mk`), so its degree pieces are images of those
of `U_{a,b}`.
-/

namespace VOA.DeligneAudit.SectorWeyl

open VOA.AffineSl3

noncomputable section

/-- Loop letters. -/
abbrev Ltr := Fin 8 × ℕ

/-- Formal combinations of loop words. -/
abbrev FreeW := List Ltr →₀ ℂ

/-- A basis word. -/
def sw (l : List Ltr) : FreeW := Finsupp.single l 1

/-- Prepending a letter. -/
def consL (x : Ltr) : FreeW →ₗ[ℂ] FreeW := Finsupp.lmapDomain ℂ ℂ (List.cons x)

theorem consL_sw (x : Ltr) (l : List Ltr) : consL x (sw l) = sw (x :: l) := by
  simp [consL, sw, Finsupp.mapDomain_single]

/-- The commutation instance with prefix `p`. -/
def commInst (p s : List Ltr) (x y : Ltr) : FreeW :=
  sw (p ++ x :: y :: s) - sw (p ++ y :: x :: s) -
    ∑ e, bracketTable x.1 y.1 e • sw (p ++ (e, x.2 + y.2) :: s)

/-- The relation tails (applied to the generator, then prefixed). -/
def relTail (a b : ℕ) : Set (List Ltr) :=
  {t | (∃ e r, e.val < 3 ∧ t = [(e, r)]) ∨ (∃ h r, 6 ≤ h.val ∧ 1 ≤ r ∧ t = [(h, r)]) ∨
    t = List.replicate (a + b + 1) (3, 0) ∨ t = List.replicate (a + b + 1) (4, 0) ∨
    t = [(3, a + b)] ∨ t = [(4, a + b)] ∨ t = [(5, 2 * a + b)]}

/-- The generators of `J a b`. -/
def relGen (a b : ℕ) : Set FreeW :=
  {g | ∃ p : List Ltr, (∃ s x y, g = commInst p s x y) ∨ (∃ t ∈ relTail a b, g = sw (p ++ t)) ∨
    (∃ h : Fin 8, 6 ≤ h.val ∧ g = sw (p ++ [(h, 0)]) - ((a + b : ℕ) : ℂ) • sw p)}

/-- The relation subspace. -/
def Jrel (a b : ℕ) : Submodule ℂ FreeW := Submodule.span ℂ (relGen a b)

theorem consL_commInst (x : Ltr) (p s : List Ltr) (y z : Ltr) :
    consL x (commInst p s y z) = commInst (x :: p) s y z := by
  simp [commInst, map_sub, map_sum, map_smul, consL_sw]

theorem consL_mem (a b : ℕ) (x : Ltr) : Jrel a b ≤ (Jrel a b).comap (consL x) := by
  rw [Jrel, Submodule.span_le]
  rintro g ⟨p, ⟨s, y, z, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨h, hh, rfl⟩⟩
  · exact Submodule.subset_span ⟨x :: p, Or.inl ⟨s, y, z, consL_commInst x p s y z⟩⟩
  · refine Submodule.subset_span ⟨x :: p, Or.inr (Or.inl ⟨t, ht, ?_⟩)⟩
    rw [consL_sw]; rfl
  · refine Submodule.subset_span ⟨x :: p, Or.inr (Or.inr ⟨h, hh, ?_⟩)⟩
    rw [map_sub, map_smul, consL_sw, consL_sw]; rfl

/-- The universal module. -/
abbrev UMod (a b : ℕ) := FreeW ⧸ Jrel a b

/-- The action of a letter. -/
def opU (a b : ℕ) (x : Ltr) : UMod a b →ₗ[ℂ] UMod a b :=
  (Jrel a b).mapQ (Jrel a b) (consL x) (consL_mem a b x)

theorem opU_mk (a b : ℕ) (x : Ltr) (l : List Ltr) :
    opU a b x (Submodule.Quotient.mk (sw l)) = Submodule.Quotient.mk (sw (x :: l)) := by
  rw [opU, Submodule.mapQ_apply, consL_sw]

theorem mk_commInst (a b : ℕ) (p s : List Ltr) (x y : Ltr) :
    (Submodule.Quotient.mk (commInst p s x y) : UMod a b) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨p, Or.inl ⟨s, x, y, rfl⟩⟩)

/-- **The universal module is an `sl₃[t]`-module.** -/
def univRep (a b : ℕ) : CurrentModule (bracketTable) (UMod a b) where
  op c r := opU a b (c, r)
  comm c d r s v := by
    induction v using Submodule.Quotient.induction_on with
    | H x =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy =>
          simp only [Submodule.Quotient.mk_add, map_add, Finset.sum_add_distrib, smul_add]
          rw [← hx, ← hy]; abel
      | single l k =>
          have hk : Finsupp.single l k = k • sw l := by simp [sw]
          have h0 := mk_commInst a b [] l (c, r) (d, s)
          rw [← Submodule.mkQ_apply] at h0
          simp only [commInst, List.nil_append, map_sub, map_sum, map_smul,
            Submodule.mkQ_apply] at h0
          rw [hk]
          simp only [Submodule.Quotient.mk_smul, map_smul, opU_mk]
          rw [show (∑ x, bracketTable c d x • k • (Submodule.Quotient.mk (sw ((x, r + s) :: l)) : UMod a b))
              = k • ∑ x, bracketTable c d x • (Submodule.Quotient.mk (sw ((x, r + s) :: l)) : UMod a b) by
            rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _, ← smul_sub]
          congr 1
          exact sub_eq_zero.mp h0

/-- The generator `[[]]`. -/
def wU (a b : ℕ) : UMod a b := Submodule.Quotient.mk (sw [])

theorem wordOp_univ (a b : ℕ) : ∀ l : List Ltr,
    wordOp (univRep a b) l (wU a b) = Submodule.Quotient.mk (sw l)
  | [] => rfl
  | (x :: l) => by
      change opU a b (x.1, x.2) (wordOp (univRep a b) l (wU a b)) = _
      rw [wordOp_univ a b l, opU_mk]

theorem iterate_eq_wordOp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule (bracketTable) V) (x : Ltr) (w : V) :
    ∀ n : ℕ, (ρ.op x.1 x.2)^[n] w = wordOp ρ (List.replicate n x) w
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply', iterate_eq_wordOp ρ x w n]; rfl

theorem mk_tail_zero (a b : ℕ) {t : List Ltr} (ht : t ∈ relTail a b) :
    (Submodule.Quotient.mk (sw t) : UMod a b) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨[], Or.inr (Or.inl ⟨t, ht, rfl⟩)⟩)

/-- **The generator of `U_{a,b}` satisfies `MabRel a b`.** -/
theorem univ_mabRel (a b : ℕ) : MabRel (univRep a b) (wU a b) a b where
  raising e he r := by
    rw [show (univRep a b).op e r (wU a b) = wordOp (univRep a b) [(e, r)] (wU a b) from rfl,
      wordOp_univ]
    exact mk_tail_zero a b (Or.inl ⟨e, r, he, rfl⟩)
  cartan_pos h h6 r hr := by
    rw [show (univRep a b).op h r (wU a b) = wordOp (univRep a b) [(h, r)] (wU a b) from rfl,
      wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inl ⟨h, r, h6, hr, rfl⟩))
  cartan_zero h h6 := by
    rw [show (univRep a b).op h 0 (wU a b) = wordOp (univRep a b) [(h, 0)] (wU a b) from rfl,
      wordOp_univ, wU, ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨[], Or.inr (Or.inr ⟨h, h6, rfl⟩)⟩)
  lowering_f1 := by
    rw [iterate_eq_wordOp (univRep a b) (3, 0), wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inr (Or.inl rfl)))
  lowering_f2 := by
    rw [iterate_eq_wordOp (univRep a b) (4, 0), wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  trunc_f1 := by
    rw [show (univRep a b).op 3 (a + b) (wU a b) = wordOp (univRep a b) [(3, a + b)] (wU a b) from rfl,
      wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  trunc_f2 := by
    rw [show (univRep a b).op 4 (a + b) (wU a b) = wordOp (univRep a b) [(4, a + b)] (wU a b) from rfl,
      wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  trunc_theta := by
    rw [show (univRep a b).op 5 (2 * a + b) (wU a b) =
      wordOp (univRep a b) [(5, 2 * a + b)] (wU a b) from rfl, wordOp_univ]
    exact mk_tail_zero a b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-! ## The universal property -/

section Universal

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V} {w : V}
  {a b : ℕ}

/-- Words applied to `w`, on formal combinations. -/
def univLin (ρ : CurrentModule (bracketTable) V) (w : V) : FreeW →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ (fun l => wordOp ρ l w)

theorem univLin_sw (l : List Ltr) : univLin ρ w (sw l) = wordOp ρ l w := by
  simp [univLin, sw]

theorem univLin_tail (h : MabRel ρ w a b) (p : List Ltr) {t : List Ltr} (ht : t ∈ relTail a b) :
    univLin ρ w (sw (p ++ t)) = 0 := by
  rw [univLin_sw, wordOp_append]
  suffices wordOp ρ t w = 0 by rw [this, wordOp_zero]
  rcases ht with ⟨e, r, he, rfl⟩ | ⟨hh, r, h6, hr, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact h.raising e he r
  · exact h.cartan_pos hh h6 r hr
  · rw [← iterate_eq_wordOp ρ (3, 0)]; exact h.lowering_f1
  · rw [← iterate_eq_wordOp ρ (4, 0)]; exact h.lowering_f2
  · exact h.trunc_f1
  · exact h.trunc_f2
  · exact h.trunc_theta

theorem J_le_ker (h : MabRel ρ w a b) : Jrel a b ≤ LinearMap.ker (univLin ρ w) := by
  rw [Jrel, Submodule.span_le]
  rintro g ⟨p, ⟨s, x, y, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨hh, h6, rfl⟩⟩
  · change univLin ρ w (commInst p s x y) = 0
    simp only [commInst, map_sub, map_sum, map_smul, univLin_sw]
    rw [wordOp_swap ρ p s x y w]
    abel
  · exact univLin_tail h p ht
  · change univLin ρ w (sw (p ++ [(hh, 0)]) - ((a + b : ℕ) : ℂ) • sw p) = 0
    rw [map_sub, map_smul, univLin_sw, univLin_sw, wordOp_append]
    change wordOp ρ p (ρ.op hh 0 w) - _ = 0
    rw [h.cartan_zero hh h6, wordOp_smul, sub_self]

/-- **The universal map** `U_{a,b} → V`, `[[l]] ↦ wordOp ρ l w`. -/
def univMap (h : MabRel ρ w a b) : UMod a b →ₗ[ℂ] V := (Jrel a b).liftQ (univLin ρ w) (J_le_ker h)

theorem univMap_wordOp (h : MabRel ρ w a b) (l : List Ltr) :
    univMap h (wordOp (univRep a b) l (wU a b)) = wordOp ρ l w := by
  rw [wordOp_univ, univMap, Submodule.liftQ_apply, univLin_sw]

theorem map_cycDeg (h : MabRel ρ w a b) (N : ℕ) :
    (cycDeg (univRep a b) (wU a b) N).map (univMap h) = cycDeg ρ w N := by
  rw [cycDeg, cycDeg, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, univMap_wordOp h l⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨_, ⟨l, hl, rfl⟩, (univMap_wordOp h l).symm ▸ rfl⟩

/-- **Universality of dimensions.** -/
theorem finrank_cycDeg_le_univ (h : MabRel ρ w a b) (N : ℕ)
    [FiniteDimensional ℂ (cycDeg (univRep a b) (wU a b) N)] :
    Module.finrank ℂ (cycDeg ρ w N) ≤ Module.finrank ℂ (cycDeg (univRep a b) (wU a b) N) := by
  rw [← map_cycDeg h N]
  exact Submodule.finrank_map_le _ _

end Universal

/-- **The graded characters of the universal modules** `M_{a,b}`. -/
def Mchar (a b : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (Module.finrank ℂ (cycDeg (univRep a b) (wU a b) N) : ℚ)

theorem Mchar_nonneg (a b N : ℕ) : 0 ≤ PowerSeries.coeff N (Mchar a b) := by
  simp [Mchar]

end

end VOA.DeligneAudit.SectorWeyl

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorWeyl.univRep
#print axioms VOA.DeligneAudit.SectorWeyl.univ_mabRel
#print axioms VOA.DeligneAudit.SectorWeyl.finrank_cycDeg_le_univ
end AxiomAudit
