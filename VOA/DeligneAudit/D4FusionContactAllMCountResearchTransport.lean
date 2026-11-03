import VOA.DeligneAudit.D4FusionContactAllMCandidate
import VOA.DeligneAudit.D4FusionContactM2Images

/-! # Boundary two-mode transport for whole grouped current relations

A pair p<q=m-1 carries an exact copy of every two-mode current derivation:
mode zero stays zero and mode one becomes q-p. This is an actual polynomial
intertwiner. No count, normal-form or flatness premise is used.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

structure BoundaryPair (m : ℕ) where
  lower : Fin m
  top : Fin m
  lt : lower.val < top.val
  last : top.val + 1 = m

variable {m : ℕ} (b : BoundaryPair m)

namespace BoundaryPair

def embedMode (a : Fin 2) : Fin m := if a = 0 then b.lower else b.top

def shift (k : Fin 2) : Fin m :=
  if k = 0 then ⟨0,by have := b.top.isLt; omega⟩
  else ⟨b.top.val-b.lower.val,by have := b.top.isLt; omega⟩

def embed (x : Vars 2) : Vars m := (x.1,b.embedMode x.2)

def mapDeriv : Polynomial.DerivIndex → Polynomial.AllM.DerivIndex m
  | .inl (g,k) => .inl (g,b.shift k)
  | .inr (i,k) => .inr (i,b.shift k)

end BoundaryPair

open BoundaryPair

theorem transport_modeX (i : Fin 9) (k a : Fin 2) :
    MvPolynomial.rename b.embed (modeX 2 i (k.val+a.val)) =
      modeX m i ((b.shift k).val+(b.embedMode a).val) := by
  have hp := b.lower.isLt
  have hq := b.top.isLt
  have hlt := b.lt
  have hlast := b.last
  fin_cases k <;> fin_cases a
  · simp [shift,embedMode,embed,modeX,hp]
  · simp [shift,embedMode,embed,modeX,hq]
  · have he : b.top.val-b.lower.val+b.lower.val = b.top.val := by omega
    simp [shift,embedMode,embed,modeX,hq,he]
  · have he : ¬ b.top.val-b.lower.val+b.top.val < m := by omega
    simp [shift,embedMode,modeX,he]

theorem transport_deriv_X (d : Polynomial.DerivIndex) (x : Vars 2) :
    MvPolynomial.rename b.embed (Polynomial.candidateDeriv d (MvPolynomial.X x)) =
      Polynomial.AllM.candidateDeriv m (b.mapDeriv d) (MvPolynomial.X (b.embed x)) := by
  cases d with
  | inl y =>
      obtain ⟨g,k⟩ := y
      simp only [Polynomial.candidateDeriv,Polynomial.AllM.candidateDeriv,mapDeriv,
        g0Deriv,MvPolynomial.mkDerivation_X,g0Image,map_sum,map_smul,embed]
      exact Finset.sum_congr rfl (fun j _ => congrArg (fun z =>
        contactF (zeroIndex g) (radIndex x.1) (radIndex j) • z)
          (transport_modeX b j k x.2))
  | inr y =>
      obtain ⟨i,k⟩ := y
      by_cases hx : x.1 = 8
      · simp only [Polynomial.candidateDeriv,Polynomial.AllM.candidateDeriv,mapDeriv,
          eDeriv,MvPolynomial.mkDerivation_X,eImage,embed,if_pos hx]
        exact transport_modeX b i.castSucc k x.2
      · simp only [Polynomial.candidateDeriv,Polynomial.AllM.candidateDeriv,mapDeriv,
          eDeriv,MvPolynomial.mkDerivation_X,eImage,embed,if_neg hx,map_zero]

/-- The variable intertwiner extends to every polynomial by Leibniz. -/
theorem transport_deriv (d : Polynomial.DerivIndex) (p : MvPolynomial (Vars 2) ℂ) :
    MvPolynomial.rename b.embed (Polynomial.candidateDeriv d p) =
      Polynomial.AllM.candidateDeriv m (b.mapDeriv d) (MvPolynomial.rename b.embed p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.derivation_C]
  | add p q ihp ihq => simp only [map_add,ihp,ihq]
  | mul_X p x ih =>
      rw [map_mul (MvPolynomial.rename b.embed) p (MvPolynomial.X x),
        MvPolynomial.rename_X,(Polynomial.candidateDeriv d).leibniz,
        (Polynomial.AllM.candidateDeriv m (b.mapDeriv d)).leibniz]
      simp only [smul_eq_mul,map_add,map_mul,MvPolynomial.rename_X,ih,transport_deriv_X]

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.transport_modeX
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.transport_deriv
