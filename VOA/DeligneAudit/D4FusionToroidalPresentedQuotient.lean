import VOA.DeligneAudit.D4FusionToroidalPresentedCore

/-! The toroidal quotient and its universal property. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
  (S : Set (FreeT n))

abbrev PT' := FreeT n ⧸ JT f m S

def opPT (x : TLtr n) : PT' f m S →ₗ[ℂ] PT' f m S :=
  (JT f m S).mapQ (JT f m S) (consT x) (consT_mem_JT f m S x)

theorem opPT_mk (x : TLtr n) (l : List (TLtr n)) :
    opPT f m S x (Submodule.Quotient.mk (swT l)) =
      Submodule.Quotient.mk (swT (x :: l)) := by
  rw [opPT, Submodule.mapQ_apply, consT_swT]

theorem mk_commBaseT (s : List (TLtr n)) (x y : TLtr n) :
    (Submodule.Quotient.mk (commBaseT (f := f) (m := m) s x y) :
      PT' f m S) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨[], Or.inl ⟨s, x, y, rfl⟩⟩)

theorem mk_highBaseT (s : List (TLtr n)) (x : TLtr n)
    (hx : m ≤ x.2.2) :
    (Submodule.Quotient.mk (highBaseT s x) : PT' f m S) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨[], Or.inr (Or.inl ⟨s, x, hx, rfl⟩)⟩)

theorem mk_syntax (q : FreeT n) (hq : q ∈ S) :
    (Submodule.Quotient.mk q : PT' f m S) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨[], Or.inr (Or.inr ⟨q, hq, rfl⟩)⟩)

def rhoPT : ToroidalModule f m (PT' f m S) where
  op c i s := opPT f m S (c, i, s)
  high_zero c i s hs := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      induction z using Finsupp.induction_linear with
      | zero => simp [opPT]
      | add a b ha hb =>
          simp only [Submodule.Quotient.mk_add, map_add, ha, hb]
      | single l k =>
          have hk : Finsupp.single l k = k • swT l := by simp [swT]
          rw [hk]
          simp only [Submodule.Quotient.mk_smul, map_smul, opPT_mk]
          have hz := mk_highBaseT f m S l (c, i, s) hs
          simpa [highBaseT] using congrArg (k • ·) hz
  comm a b i j r s v := by
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy =>
          simp only [Submodule.Quotient.mk_add, map_add, Finset.sum_add_distrib,
            smul_add]
          by_cases h : r + s < m
          · simp only [if_pos h] at hx hy ⊢
            calc
              _ = ((opPT f m S (a, i, r))
                    ((opPT f m S (b, j, s)) (Submodule.Quotient.mk x)) -
                  (opPT f m S (b, j, s))
                    ((opPT f m S (a, i, r)) (Submodule.Quotient.mk x))) +
                  ((opPT f m S (a, i, r))
                    ((opPT f m S (b, j, s)) (Submodule.Quotient.mk y)) -
                  (opPT f m S (b, j, s))
                    ((opPT f m S (a, i, r)) (Submodule.Quotient.mk y))) := by abel
              _ = _ := by rw [hx, hy]
          · simp only [if_neg h] at hx hy ⊢
            calc
              _ = ((opPT f m S (a, i, r))
                    ((opPT f m S (b, j, s)) (Submodule.Quotient.mk x)) -
                  (opPT f m S (b, j, s))
                    ((opPT f m S (a, i, r)) (Submodule.Quotient.mk x))) +
                  ((opPT f m S (a, i, r))
                    ((opPT f m S (b, j, s)) (Submodule.Quotient.mk y)) -
                  (opPT f m S (b, j, s))
                    ((opPT f m S (a, i, r)) (Submodule.Quotient.mk y))) := by abel
              _ = _ := by rw [hx, hy]; simp
      | single l k =>
          have hk : Finsupp.single l k = k • swT l := by simp [swT]
          have hz := mk_commBaseT f m S l (a, i, r) (b, j, s)
          rw [← Submodule.mkQ_apply] at hz
          simp only [commBaseT, map_sub, Submodule.mkQ_apply] at hz
          rw [hk]
          simp only [Submodule.Quotient.mk_smul, map_smul, opPT_mk]
          rw [show (∑ e, f a b e • k •
              (Submodule.Quotient.mk (swT ((e, i + j, r + s) :: l)) : PT' f m S))
              = k • ∑ e, f a b e •
                (Submodule.Quotient.mk (swT ((e, i + j, r + s) :: l)) : PT' f m S) by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun e _ => smul_comm _ _ _, ← smul_sub]
          by_cases h : r + s < m
          · simp only [if_pos h] at hz
            simp only [if_pos h]
            have hsum :
                (Submodule.Quotient.mk
                  (∑ e, f a b e • swT ((e, i + j, r + s) :: l)) : PT' f m S) =
                  ∑ e, f a b e •
                    (Submodule.Quotient.mk
                      (swT ((e, i + j, r + s) :: l)) : PT' f m S) := by
              change (JT f m S).mkQ (∑ e, f a b e •
                swT ((e, i + j, r + s) :: l)) = _
              simp
            rw [hsum] at hz
            exact congrArg (k • ·) (sub_eq_zero.mp hz)
          · simp only [if_neg h] at hz
            simp only [if_neg h]
            have hz' := sub_eq_zero.mp hz
            rw [hz']
            simp

/-- The class of the empty word. -/
def pPT : PT' f m S := Submodule.Quotient.mk (swT [])

theorem wordOpT_rhoPT (l : List (TLtr n)) :
    wordOpT (rhoPT f m S) l (pPT f m S) =
      Submodule.Quotient.mk (swT l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change opPT f m S x (wordOpT (rhoPT f m S) l (pPT f m S)) = _
      rw [ih, opPT_mk]

theorem PT'_cyclic :
    Submodule.span ℂ (Set.range fun l : List (TLtr n) =>
      wordOpT (rhoPT f m S) l (pPT f m S)) = ⊤ := by
  apply top_unique
  intro v _
  suffices ∀ v : PT' f m S,
      v ∈ Submodule.span ℂ (Set.range fun l : List (TLtr n) =>
        wordOpT (rhoPT f m S) l (pPT f m S)) from this v
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H z =>
    induction z using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => simpa only [Submodule.Quotient.mk_add] using
        Submodule.add_mem _ ha hb
    | single l k =>
        have hk : Finsupp.single l k = k • swT l := by simp [swT]
        rw [hk, Submodule.Quotient.mk_smul]
        apply Submodule.smul_mem
        rw [← wordOpT_rhoPT f m S l]
        exact Submodule.subset_span ⟨l, rfl⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : ToroidalModule f m V) (v : V)

theorem evalT_commBaseT (s : List (TLtr n)) (x y : TLtr n) :
    evalT ρ v (commBaseT (f := f) (m := m) s x y) = 0 := by
  simp only [commBaseT, map_sub, evalT_swT, wordOpT]
  rw [ρ.comm x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2 (wordOpT ρ s v)]
  split_ifs <;> simp [evalT_swT, wordOpT]

theorem evalT_highBaseT (s : List (TLtr n)) (x : TLtr n)
    (hx : m ≤ x.2.2) : evalT ρ v (highBaseT s x) = 0 := by
  simp [highBaseT, evalT_swT, wordOpT, ρ.high_zero x.1 x.2.1 x.2.2 hx]

/-- A target annihilating the syntax receives the unique word evaluation map. -/
theorem JT_le_ker (hS : ∀ q ∈ S, evalT ρ v q = 0) :
    JT f m S ≤ LinearMap.ker (evalT ρ v) := by
  rw [JT, Submodule.span_le]
  rintro z ⟨p, ⟨s, x, y, rfl⟩ | ⟨s, x, hx, rfl⟩ | ⟨q, hq, rfl⟩⟩
  · change evalT ρ v (prefixT p (commBaseT s x y)) = 0
    rw [evalT_prefixT, evalT_commBaseT f m ρ v s x y, wordOpT_zero]
  · change evalT ρ v (prefixT p (highBaseT s x)) = 0
    rw [evalT_prefixT, evalT_highBaseT f m ρ v s x hx, wordOpT_zero]
  · change evalT ρ v (prefixT p q) = 0
    rw [evalT_prefixT, hS q hq, wordOpT_zero]

def univMapT (hS : ∀ q ∈ S, evalT ρ v q = 0) : PT' f m S →ₗ[ℂ] V :=
  (JT f m S).liftQ (evalT ρ v) (JT_le_ker f m S ρ v hS)

theorem univMapT_mk (hS : ∀ q ∈ S, evalT ρ v q = 0) (z : FreeT n) :
    univMapT f m S ρ v hS (Submodule.Quotient.mk z) = evalT ρ v z := by
  exact Submodule.liftQ_apply _ _ _

theorem univMapT_gen (hS : ∀ q ∈ S, evalT ρ v q = 0) :
    univMapT f m S ρ v hS (pPT f m S) = v := by
  rw [pPT, univMapT_mk, evalT_swT]
  rfl

theorem univMapT_op (hS : ∀ q ∈ S, evalT ρ v q = 0)
    (c : Fin n) (i s : ℕ) (z : PT' f m S) :
    univMapT f m S ρ v hS ((rhoPT f m S).op c i s z) =
      ρ.op c i s (univMapT f m S ρ v hS z) := by
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change univMapT f m S ρ v hS
      (opPT f m S (c, i, s) (Submodule.Quotient.mk z)) = _
    rw [opPT, Submodule.mapQ_apply, univMapT_mk, univMapT_mk, evalT_consT]

end

end VOA.DeligneAudit.Toroidal
