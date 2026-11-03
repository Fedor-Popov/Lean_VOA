import VOA.DeligneAudit.DeligneFusionCVFamily
import VOA.DeligneAudit.DeligneFusionUnivG

/-!
# The actual universal modules for the auxiliary A₂ CV family

The generic word-quotient construction applies to CV presentations because
Garland's equivalence replaces each coefficient-sum relation by a single
word `E(1)^s F(0)^(r+s)` on a highest-weight vector. Every relation used here
is therefore homogeneous in current degree. No dimension bound, fusion
identification or additional relation hypothesis enters this construction.
-/

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

/-- The first coordinate of the auxiliary family's highest weight. -/
def lambda1 (ε ν ϱ : Weight) (j : ℕ) : ℕ := ε.1 + 2 * ν.1 + 3 * ϱ.1 + j

/-- The second coordinate of the auxiliary family's highest weight. -/
def lambda2 (ε ν ϱ : Weight) (j : ℕ) : ℕ := ε.2 + 2 * ν.2 + 3 * ϱ.2 + j

/-- The single word equivalent to the Garland coefficient relation. -/
def cvWord (e f : Fin 8) (r s : ℕ) : List (UnivG.Ltr 8) :=
  List.replicate s (e, 1) ++ List.replicate (r + s) (f, 0)

/-- The homogeneous tail words in the auxiliary CV presentation. -/
inductive CVTail (ε ν ϱ : Weight) (j : ℕ) : List (UnivG.Ltr 8) → Prop
  | raising (e : Fin 8) (he : e.val < 3) (k : ℕ) : CVTail ε ν ϱ j [(e, k)]
  | cartan (hh : Fin 8) (hhh : 6 ≤ hh.val) (k : ℕ) (hk : 1 ≤ k) :
      CVTail ε ν ϱ j [(hh, k)]
  | first_nil : CVTail ε ν ϱ j (List.replicate (lambda1 ε ν ϱ j + 1) (3, 0))
  | second_nil : CVTail ε ν ϱ j (List.replicate (lambda2 ε ν ϱ j + 1) (4, 0))
  | first_cv (r s k : ℕ) (hr : 1 ≤ r)
      (hrs : 1 + r * k + T k (parts ϱ.1 ν.1 (ε.1 + j)) ≤ s + r) :
      CVTail ε ν ϱ j (cvWord 0 3 r s)
  | second_cv (r s k : ℕ) (hr : 1 ≤ r)
      (hrs : 1 + r * k + T k (parts ϱ.2 ν.2 (ε.2 + j)) ≤ s + r) :
      CVTail ε ν ϱ j (cvWord 1 4 r s)
  | highest_cv (r s k : ℕ) (hr : 1 ≤ r)
      (hrs : 1 + r * k +
        T k (parts (ϱ.1 + ϱ.2) (ν.1 + ν.2 + j) (ε.1 + ε.2)) ≤ s + r) :
      CVTail ε ν ϱ j (cvWord 2 5 r s)

/-- The auxiliary CV family as a specification for the generic universal module. -/
def cvSpec (ε ν ϱ : Weight) (j : ℕ) : UnivG.RelSpec 8 where
  tails := CVTail ε ν ϱ j
  eig := {q | q = (6, (lambda1 ε ν ϱ j : ℂ)) ∨ q = (7, (lambda2 ε ν ϱ j : ℂ))}

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {j : ℕ}

/-- Evaluating the CV word gives the ordinary Garland operator `X`. -/
theorem wordOp_cvWord (R : CurrentModule bracketTable V) (w : V)
    (e f : Fin 8) (r s : ℕ) :
    wordOp R (cvWord e f r s) w = X (R.op e) (R.op f) r s w := by
  rw [cvWord, wordOp_append, ← iterate_eq_wordOp R (f, 0),
    ← iterate_eq_wordOp R (e, 1)]
  simp only [X, Module.End.pow_apply]

/-- The word specification is exactly the full three-root CV presentation. -/
theorem sat_cvSpec_iff :
    UnivG.Sat bracketTable R w (cvSpec ε ν ϱ j) ↔ CV3Rel R w ε ν ϱ j := by
  constructor
  · intro h
    have hE : ∀ e : Fin 8, e.val < 3 → ∀ k, R.op e k w = 0 :=
      fun e he k => h.tail [(e, k)] (CVTail.raising e he k)
    have hH : ∀ hh : Fin 8, 6 ≤ hh.val → ∀ k, 1 ≤ k → R.op hh k w = 0 :=
      fun hh hhh k hk => h.tail [(hh, k)] (CVTail.cartan hh hhh k hk)
    refine ⟨hE, hH, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.eig (6, (lambda1 ε ν ϱ j : ℂ)) (Or.inl rfl)
    · exact h.eig (7, (lambda2 ε ν ϱ j : ℂ)) (Or.inr rfl)
    · rw [iterate_eq_wordOp R (3, 0)]
      exact h.tail _ CVTail.first_nil
    · rw [iterate_eq_wordOp R (4, 0)]
      exact h.tail _ CVTail.second_nil
    · intro r s k hr hrs
      apply Q_zero_of_X (CVRoots.sl2_first R).hEF (CVRoots.sl2_first R).hHF
        (CVRoots.sl2_first R).hFF (fun q => hE 0 (by decide) q)
        (fun q hq => hH 6 (by decide) q hq) hr
      have ht := h.tail _ (CVTail.first_cv r s k hr hrs)
      rwa [wordOp_cvWord] at ht
    · intro r s k hr hrs
      apply Q_zero_of_X (CVRoots.sl2_second R).hEF (CVRoots.sl2_second R).hHF
        (CVRoots.sl2_second R).hFF (fun q => hE 1 (by decide) q)
        (fun q hq => hH 7 (by decide) q hq) hr
      have ht := h.tail _ (CVTail.second_cv r s k hr hrs)
      rwa [wordOp_cvWord] at ht
    · intro r s k hr hrs
      apply Q_zero_of_X (CVRoots.sl2_highest R).hEF (CVRoots.sl2_highest R).hHF
        (CVRoots.sl2_highest R).hFF (fun q => hE 2 (by decide) q)
        (fun q hq => by simp [hH 6 (by decide) q hq, hH 7 (by decide) q hq]) hr
      have ht := h.tail _ (CVTail.highest_cv r s k hr hrs)
      rwa [wordOp_cvWord] at ht
  · intro h
    refine ⟨?_, ?_⟩
    · intro t ht
      cases ht with
      | raising e he k => exact h.raising e he k
      | cartan hh hhh k hk => exact h.cartan_pos hh hhh k hk
      | first_nil =>
          rw [← iterate_eq_wordOp R (3, 0)]
          exact h.lowering_first
      | second_nil =>
          rw [← iterate_eq_wordOp R (4, 0)]
          exact h.lowering_second
      | first_cv r s k hr hrs =>
          rw [wordOp_cvWord]
          exact X_zero_of_Q (CVRoots.sl2_first R).hEF (CVRoots.sl2_first R).hHF
            (CVRoots.sl2_first R).hFF (fun q => h.raising 0 (by decide) q)
            (fun q hq => h.cartan_pos 6 (by decide) q hq) hr (h.first r s k hr hrs)
      | second_cv r s k hr hrs =>
          rw [wordOp_cvWord]
          exact X_zero_of_Q (CVRoots.sl2_second R).hEF (CVRoots.sl2_second R).hHF
            (CVRoots.sl2_second R).hFF (fun q => h.raising 1 (by decide) q)
            (fun q hq => h.cartan_pos 7 (by decide) q hq) hr (h.second r s k hr hrs)
      | highest_cv r s k hr hrs =>
          rw [wordOp_cvWord]
          exact X_zero_of_Q (CVRoots.sl2_highest R).hEF (CVRoots.sl2_highest R).hHF
            (CVRoots.sl2_highest R).hFF (fun q => h.raising 2 (by decide) q)
            (fun q hq => by
              simp [h.cartan_pos 6 (by decide) q hq, h.cartan_pos 7 (by decide) q hq])
            hr (h.highest r s k hr hrs)
    · rintro q (rfl | rfl)
      · exact h.cartan_first
      · exact h.cartan_second

/-- The actual universal auxiliary CV module. -/
abbrev CVMod (ε ν ϱ : Weight) (j : ℕ) := UnivG.UModG bracketTable (cvSpec ε ν ϱ j)

/-- Its current action is the generic quotient action. -/
def cvUnivRep (ε ν ϱ : Weight) (j : ℕ) : CurrentModule bracketTable (CVMod ε ν ϱ j) :=
  UnivG.univRepG bracketTable (cvSpec ε ν ϱ j)

/-- The universal cyclic generator. -/
def cv_wU (ε ν ϱ : Weight) (j : ℕ) : CVMod ε ν ϱ j :=
  UnivG.wUG bracketTable (cvSpec ε ν ϱ j)

/-- The universal cyclic generator satisfies the actual three-root CV relations. -/
theorem cvUniv_rel (ε ν ϱ : Weight) (j : ℕ) :
    CV3Rel (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) ε ν ϱ j :=
  sat_cvSpec_iff.mp (UnivG.univG_sat bracketTable (cvSpec ε ν ϱ j))

/-- The universal map to any vector satisfying the actual source presentation. -/
def cvMap (h : CV3Rel R w ε ν ϱ j) : CVMod ε ν ϱ j →ₗ[ℂ] V :=
  UnivG.univMapG (sat_cvSpec_iff.mpr h)

/-- The universal map evaluates every word on the target cyclic vector. -/
theorem cvMap_wordOp (h : CV3Rel R w ε ν ϱ j) (l : List (UnivG.Ltr 8)) :
    cvMap h (wordOp (cvUnivRep ε ν ϱ j) l (cv_wU ε ν ϱ j)) = wordOp R l w :=
  UnivG.univMapG_wordOp (sat_cvSpec_iff.mpr h) l

/-- In particular the universal map sends the generator to the given vector. -/
theorem cvMap_generator (h : CV3Rel R w ε ν ϱ j) : cvMap h (cv_wU ε ν ϱ j) = w :=
  cvMap_wordOp h []

/-- Every exact current-degree cyclic piece is the image of the universal one. -/
theorem map_cycDeg (h : CV3Rel R w ε ν ϱ j) (d : ℕ) :
    (cycDeg (cvUnivRep ε ν ϱ j) (cv_wU ε ν ϱ j) d).map (cvMap h) = cycDeg R w d :=
  UnivG.map_cycDegG (sat_cvSpec_iff.mpr h) d

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVUniv.sat_cvSpec_iff
#print axioms VOA.DeligneAudit.A2.CVUniv.cvUniv_rel
#print axioms VOA.DeligneAudit.A2.CVUniv.cvMap
#print axioms VOA.DeligneAudit.A2.CVUniv.map_cycDeg
