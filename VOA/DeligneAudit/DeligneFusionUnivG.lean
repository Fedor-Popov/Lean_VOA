/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionPBW
import VOA.DeligneAudit.DeligneSectorWeyl

/-!
# Type-generic universal modules (the `DeligneFusionUniv`, for any structure constants)

the `U_{a,b}` (`DeligneFusionUniv`) is built for `sl₃[t]` and the `MabRel a b` relations. Here the
same construction is done for any structure constants `f : Fin n → Fin n → Fin n → ℂ` and any
**relation specification** `R : RelSpec n`: a set of *tail words* `t` (relations `t · w = 0`) and a
set of *eigen-relations* `(h, λ)` (relations `(h ⊗ 1) w = λ w`). Every relation family used in the
squeeze is of this shape: the local Weyl/fusion relations `LocalWeylRelG S m` (`lwSpec S m`,
`localWeylRelG_iff`), and any per-type Ravinder family `M_{a,b}`.

* `UModG f R`, `univRepG f R : CurrentModule f (UModG f R)`, `wUG f R`, `univG_sat`;
* `univMapG` and `finrank_cycDeg_le_univG`: every cyclic module whose generator satisfies `R`
  is bounded degree by degree by `U(R)` (given that the degree pieces of `U(R)` are
  finite-dimensional, `UnivFD`);
* `McharG f R`, `McharG_nonneg`.
-/

namespace VOA.DeligneAudit.UnivG

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

/-- Loop letters. -/
abbrev Ltr (n : ℕ) := Fin n × ℕ

/-- Formal combinations of loop words. -/
abbrev FreeW (n : ℕ) := List (Ltr n) →₀ ℂ

/-- **A relation specification**: tail words killing the generator, and eigen-relations of grade-0
letters. -/
structure RelSpec (n : ℕ) where
  tails : Set (List (Ltr n))
  eig : Set (Fin n × ℂ)

/-- The generator `w` of `ρ` satisfies `R`. -/
structure Sat {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule f V) (w : V)
    (R : RelSpec n) : Prop where
  tail : ∀ t ∈ R.tails, wordOp ρ t w = 0
  eig : ∀ p ∈ R.eig, ρ.op p.1 0 w = p.2 • w

/-- A basis word. -/
def sw (l : List (Ltr n)) : FreeW n := Finsupp.single l 1

/-- Prepending a letter. -/
def consL (x : Ltr n) : FreeW n →ₗ[ℂ] FreeW n := Finsupp.lmapDomain ℂ ℂ (List.cons x)

theorem consL_sw (x : Ltr n) (l : List (Ltr n)) : consL x (sw l) = sw (x :: l) := by
  simp [consL, sw, Finsupp.mapDomain_single]

/-- The commutation instance with prefix `p`. -/
def commInst (p s : List (Ltr n)) (x y : Ltr n) : FreeW n :=
  sw (p ++ x :: y :: s) - sw (p ++ y :: x :: s) - ∑ e, f x.1 y.1 e • sw (p ++ (e, x.2 + y.2) :: s)

/-- The generators of the relation subspace. -/
def relGen (R : RelSpec n) : Set (FreeW n) :=
  {g | ∃ p : List (Ltr n), (∃ s x y, g = commInst f p s x y) ∨ (∃ t ∈ R.tails, g = sw (p ++ t)) ∨
    (∃ q ∈ R.eig, g = sw (p ++ [(q.1, 0)]) - q.2 • sw p)}

/-- The relation subspace. -/
def Jrel (R : RelSpec n) : Submodule ℂ (FreeW n) := Submodule.span ℂ (relGen f R)

theorem consL_commInst (x : Ltr n) (p s : List (Ltr n)) (y z : Ltr n) :
    consL x (commInst f p s y z) = commInst f (x :: p) s y z := by
  simp [commInst, map_sub, map_sum, map_smul, consL_sw]

theorem consL_mem (R : RelSpec n) (x : Ltr n) : Jrel f R ≤ (Jrel f R).comap (consL x) := by
  rw [Jrel, Submodule.span_le]
  rintro g ⟨p, ⟨s, y, z, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · exact Submodule.subset_span ⟨x :: p, Or.inl ⟨s, y, z, consL_commInst f x p s y z⟩⟩
  · refine Submodule.subset_span ⟨x :: p, Or.inr (Or.inl ⟨t, ht, ?_⟩)⟩
    rw [consL_sw]; rfl
  · refine Submodule.subset_span ⟨x :: p, Or.inr (Or.inr ⟨q, hq, ?_⟩)⟩
    rw [map_sub, map_smul, consL_sw, consL_sw]; rfl

/-- **The universal module** `U(R)`. -/
abbrev UModG (R : RelSpec n) := FreeW n ⧸ Jrel f R

/-- The action of a letter. -/
def opU (R : RelSpec n) (x : Ltr n) : UModG f R →ₗ[ℂ] UModG f R :=
  (Jrel f R).mapQ (Jrel f R) (consL x) (consL_mem f R x)

theorem opU_mk (R : RelSpec n) (x : Ltr n) (l : List (Ltr n)) :
    opU f R x (Submodule.Quotient.mk (sw l)) = Submodule.Quotient.mk (sw (x :: l)) := by
  rw [opU, Submodule.mapQ_apply, consL_sw]

theorem mk_commInst (R : RelSpec n) (p s : List (Ltr n)) (x y : Ltr n) :
    (Submodule.Quotient.mk (commInst f p s x y) : UModG f R) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨p, Or.inl ⟨s, x, y, rfl⟩⟩)

/-- **The universal module is a current module.** -/
def univRepG (R : RelSpec n) : CurrentModule f (UModG f R) where
  op c r := opU f R (c, r)
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
          have h0 := mk_commInst f R [] l (c, r) (d, s)
          rw [← Submodule.mkQ_apply] at h0
          simp only [commInst, List.nil_append, map_sub, map_sum, map_smul,
            Submodule.mkQ_apply] at h0
          rw [hk]
          simp only [Submodule.Quotient.mk_smul, map_smul, opU_mk]
          rw [show (∑ x, f c d x • k • (Submodule.Quotient.mk (sw ((x, r + s) :: l)) : UModG f R))
              = k • ∑ x, f c d x • (Submodule.Quotient.mk (sw ((x, r + s) :: l)) : UModG f R) by
            rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _,
            ← smul_sub]
          congr 1
          exact sub_eq_zero.mp h0

/-- The generator `[[]]`. -/
def wUG (R : RelSpec n) : UModG f R := Submodule.Quotient.mk (sw [])

theorem wordOp_univG (R : RelSpec n) : ∀ l : List (Ltr n),
    wordOp (univRepG f R) l (wUG f R) = Submodule.Quotient.mk (sw l)
  | [] => rfl
  | (x :: l) => by
      change opU f R (x.1, x.2) (wordOp (univRepG f R) l (wUG f R)) = _
      rw [wordOp_univG R l, opU_mk]

/-- **The generator of `U(R)` satisfies `R`.** -/
theorem univG_sat (R : RelSpec n) : Sat f (univRepG f R) (wUG f R) R where
  tail t ht := by
    rw [wordOp_univG]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.subset_span ⟨[], Or.inr (Or.inl ⟨t, ht, rfl⟩)⟩)
  eig q hq := by
    rw [show (univRepG f R).op q.1 0 (wUG f R) = wordOp (univRepG f R) [(q.1, 0)] (wUG f R) from
      rfl, wordOp_univG, wUG, ← Submodule.Quotient.mk_smul, ← sub_eq_zero,
      ← Submodule.Quotient.mk_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.subset_span ⟨[], Or.inr (Or.inr ⟨q, hq, rfl⟩)⟩)

/-! ## The universal property -/

section Universal

variable {f} {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule f V} {w : V}
  {R : RelSpec n}

/-- Words applied to `w`, on formal combinations. -/
def univLin (ρ : CurrentModule f V) (w : V) : FreeW n →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ (fun l => wordOp ρ l w)

theorem univLin_sw (l : List (Ltr n)) : univLin ρ w (sw l) = wordOp ρ l w := by
  simp [univLin, sw]

theorem J_le_ker (h : Sat f ρ w R) : Jrel f R ≤ LinearMap.ker (univLin ρ w) := by
  rw [Jrel, Submodule.span_le]
  rintro g ⟨p, ⟨s, x, y, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · change univLin ρ w (commInst f p s x y) = 0
    simp only [commInst, map_sub, map_sum, map_smul, univLin_sw]
    rw [wordOp_swap ρ p s x y w]
    abel
  · change univLin ρ w (sw (p ++ t)) = 0
    rw [univLin_sw, wordOp_append, h.tail t ht, wordOp_zero]
  · change univLin ρ w (sw (p ++ [(q.1, 0)]) - q.2 • sw p) = 0
    rw [map_sub, map_smul, univLin_sw, univLin_sw, wordOp_append]
    change wordOp ρ p (ρ.op q.1 0 w) - _ = 0
    rw [h.eig q hq, wordOp_smul, sub_self]

/-- **The universal map** `U(R) → V`, `[[l]] ↦ wordOp ρ l w`. -/
def univMapG (h : Sat f ρ w R) : UModG f R →ₗ[ℂ] V := (Jrel f R).liftQ (univLin ρ w) (J_le_ker h)

theorem univMapG_wordOp (h : Sat f ρ w R) (l : List (Ltr n)) :
    univMapG h (wordOp (univRepG f R) l (wUG f R)) = wordOp ρ l w := by
  rw [wordOp_univG, univMapG, Submodule.liftQ_apply, univLin_sw]

theorem map_cycDegG (h : Sat f ρ w R) (N : ℕ) :
    (cycDeg (univRepG f R) (wUG f R) N).map (univMapG h) = cycDeg ρ w N := by
  rw [cycDeg, cycDeg, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, univMapG_wordOp h l⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨_, ⟨l, hl, rfl⟩, (univMapG_wordOp h l).symm ▸ rfl⟩

/-- **Universality of dimensions.** -/
theorem finrank_cycDeg_le_univG (h : Sat f ρ w R) (N : ℕ)
    [FiniteDimensional ℂ (cycDeg (univRepG f R) (wUG f R) N)] :
    Module.finrank ℂ (cycDeg ρ w N) ≤ Module.finrank ℂ (cycDeg (univRepG f R) (wUG f R) N) := by
  rw [← map_cycDegG h N]
  exact Submodule.finrank_map_le _ _

end Universal

/-- The degree pieces of `U(R)` are finite-dimensional. -/
def UnivFD (R : RelSpec n) : Prop :=
  ∀ N, FiniteDimensional ℂ (cycDeg (univRepG f R) (wUG f R) N)

/-- **The graded character of `U(R)`.** -/
def McharG (R : RelSpec n) : PowerSeries ℚ :=
  PowerSeries.mk fun N => (Module.finrank ℂ (cycDeg (univRepG f R) (wUG f R) N) : ℚ)

theorem McharG_nonneg (R : RelSpec n) (N : ℕ) : 0 ≤ PowerSeries.coeff N (McharG f R) := by
  simp [McharG]

/-- **The universal bound for `McharG`.** -/
theorem finrank_le_McharG {R : RelSpec n} (hfd : UnivFD f R) {V : Type} [AddCommGroup V]
    [Module ℂ V] {ρ : CurrentModule f V} {w : V} (h : Sat f ρ w R) (N : ℕ) :
    (Module.finrank ℂ (cycDeg ρ w N) : ℚ) ≤ PowerSeries.coeff N (McharG f R) := by
  haveI := hfd N
  simp only [McharG, PowerSeries.coeff_mk]
  exact_mod_cast finrank_cycDeg_le_univG h N

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.univRepG
#print axioms VOA.DeligneAudit.UnivG.univG_sat
#print axioms VOA.DeligneAudit.UnivG.finrank_cycDeg_le_univG
#print axioms VOA.DeligneAudit.UnivG.finrank_le_McharG
end AxiomAudit
