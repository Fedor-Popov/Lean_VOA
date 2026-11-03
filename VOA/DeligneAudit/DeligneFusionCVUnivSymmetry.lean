import VOA.DeligneAudit.DeligneFusionCVUnivQuotient
import VOA.DeligneAudit.DeligneFusionCVSymmetry

/-!
# The Dynkin involution on the actual universal CV modules

The checked swap of the three-root presentation gives universal maps in both
directions. Current intertwining and universal word spanning show that their
composites are the identity. Thus swapping both weight coordinates preserves
the actual universal module's dimension, with no finiteness premise.
-/

namespace VOA.DeligneAudit.A2.CVUniv

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVSymmetry

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight} {j : ℕ}

/-- The actual universal map intertwines every current operator. -/
theorem cvMap_op (h : CV3Rel R w ε ν ϱ j) (e : Fin 8) (k : ℕ)
    (v : CVMod ε ν ϱ j) :
    cvMap h ((cvUnivRep ε ν ϱ j).op e k v) = R.op e k (cvMap h v) := by
  have he : (cvMap h).comp ((cvUnivRep ε ν ϱ j).op e k) =
      (R.op e k).comp (cvMap h) := by
    apply LinearMap.ext_on_range (cv_span_top ε ν ϱ j)
    intro l
    change cvMap h (wordOp (cvUnivRep ε ν ϱ j) ((e, k) :: l)
      (cv_wU ε ν ϱ j)) = R.op e k (cvMap h
        (wordOp (cvUnivRep ε ν ϱ j) l (cv_wU ε ν ϱ j)))
    rw [cvMap_wordOp, cvMap_wordOp]
    rfl
  exact congrArg (fun f => f v) he

/-- The universal map from the swapped presentation to the checked pullback
of the original module. -/
def cvSwapMap (ε ν ϱ : Weight) (j : ℕ) :
    CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j →ₗ[ℂ] CVMod ε ν ϱ j :=
  cvMap (cv3Rel_swap (cvUniv_rel ε ν ϱ j))

theorem cvSwapMap_generator (ε ν ϱ : Weight) (j : ℕ) :
    cvSwapMap ε ν ϱ j (cv_wU (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) =
      cv_wU ε ν ϱ j := cvMap_generator _

theorem cvSwapMap_wordOp (ε ν ϱ : Weight) (j : ℕ) (l : List (UnivG.Ltr 8)) :
    cvSwapMap ε ν ϱ j
      (wordOp (cvUnivRep (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) l
        (cv_wU (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j)) =
      wordOp (swapRep (cvUnivRep ε ν ϱ j)) l (cv_wU ε ν ϱ j) :=
  cvMap_wordOp _ l

theorem cvSwapMap_op (ε ν ϱ : Weight) (j : ℕ) (e : Fin 8) (k : ℕ)
    (v : CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) :
    cvSwapMap ε ν ϱ j
      ((cvUnivRep (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j).op e k v) =
      (swapRep (cvUnivRep ε ν ϱ j)).op e k (cvSwapMap ε ν ϱ j v) :=
  cvMap_op _ e k v

/-- Pulling the source current action back a second time cancels the involution. -/
theorem cvSwapMap_twisted_op (ε ν ϱ : Weight) (j : ℕ) (e : Fin 8) (k : ℕ)
    (v : CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) :
    cvSwapMap ε ν ϱ j
      ((swapRep (cvUnivRep (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j)).op e k v) =
      (cvUnivRep ε ν ϱ j).op e k (cvSwapMap ε ν ϱ j v) := by
  change cvSwapMap ε ν ϱ j (swapSign e •
    (cvUnivRep (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j).op (swapIndex e) k v) = _
  rw [map_smul, cvSwapMap_op]
  change swapSign e • (swapSign (swapIndex e) •
    (cvUnivRep ε ν ϱ j).op (swapIndex (swapIndex e)) k (cvSwapMap ε ν ϱ j v)) = _
  have hi : swapIndex (swapIndex e) = e := by fin_cases e <;> rfl
  have hs : swapSign e * swapSign (swapIndex e) = 1 := by
    fin_cases e <;> dsimp [swapSign, swapIndex] <;> norm_num
  rw [smul_smul, hi, hs, one_smul]

theorem cvSwapMap_twisted_wordOp (ε ν ϱ : Weight) (j : ℕ)
    (l : List (UnivG.Ltr 8)) :
    cvSwapMap ε ν ϱ j
      (wordOp (swapRep (cvUnivRep (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j)) l
        (cv_wU (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j)) =
      wordOp (cvUnivRep ε ν ϱ j) l (cv_wU ε ν ϱ j) := by
  induction l with
  | nil => exact cvSwapMap_generator ε ν ϱ j
  | cons x l ih =>
      change cvSwapMap ε ν ϱ j ((swapRep _).op x.1 x.2 _) = _
      rw [cvSwapMap_twisted_op, ih]
      rfl

/-- The two actual universal swap maps are inverse, by word spanning. -/
theorem cvSwapMap_comp (ε ν ϱ : Weight) (j : ℕ) :
    (cvSwapMap ε ν ϱ j).comp
      (cvSwapMap (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) =
      LinearMap.id := by
  apply LinearMap.ext_on_range (cv_span_top ε ν ϱ j)
  intro l
  rw [LinearMap.comp_apply, cvSwapMap_wordOp, cvSwapMap_twisted_wordOp]
  rfl

/-- The actual universal CV modules are linearly equivalent after swapping
both simple-root coordinates in all three weight parameters. -/
def cvSwapEquiv (ε ν ϱ : Weight) (j : ℕ) :
    CVMod ε ν ϱ j ≃ₗ[ℂ] CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j where
  toLinearMap := cvSwapMap (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j
  invFun := cvSwapMap ε ν ϱ j
  left_inv v := congrArg (fun f => f v) (cvSwapMap_comp ε ν ϱ j)
  right_inv v := congrArg (fun f => f v)
    (cvSwapMap_comp (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j)

/-- Swapping the Dynkin coordinates preserves finrank without a finiteness premise. -/
theorem cvSwap_finrank (ε ν ϱ : Weight) (j : ℕ) :
    Module.finrank ℂ (CVMod ε ν ϱ j) =
      Module.finrank ℂ (CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) :=
  (cvSwapEquiv ε ν ϱ j).finrank_eq

/-- Finite-dimensionality transports through the actual swap equivalence. -/
theorem cvSwap_finiteDimensional (ε ν ϱ : Weight) (j : ℕ)
    [FiniteDimensional ℂ (CVMod ε ν ϱ j)] :
    FiniteDimensional ℂ (CVMod (ε.2, ε.1) (ν.2, ν.1) (ϱ.2, ϱ.1) j) :=
  (cvSwapEquiv ε ν ϱ j).finiteDimensional

end

end VOA.DeligneAudit.A2.CVUniv

#print axioms VOA.DeligneAudit.A2.CVUniv.cvSwapMap_comp
#print axioms VOA.DeligneAudit.A2.CVUniv.cvSwapEquiv
#print axioms VOA.DeligneAudit.A2.CVUniv.cvSwap_finrank
