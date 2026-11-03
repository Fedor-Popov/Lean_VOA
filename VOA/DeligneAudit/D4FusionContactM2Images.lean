import VOA.DeligneAudit.D4FusionContactM2ImagesTable
import VOA.DeligneAudit.D4FusionContactM2WordDerivation

/-! # Actual varIndex and derivation semantics of the sparse certificate -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

noncomputable section

def varIndex (v : Fin 18) : Vars 2 :=
  (⟨v.val / 2,by omega⟩, ⟨v.val % 2,by omega⟩)

def flatten (i : Fin 9) (r : Fin 2) : Fin 18 := ⟨2*i.val+r.val,by omega⟩

@[simp] theorem variable_flatten (i : Fin 9) (r : Fin 2) : varIndex (flatten i r) = (i,r) := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [varIndex,flatten] <;> omega

@[simp] theorem flatten_variable (v : Fin 18) : flatten (varIndex v).1 (varIndex v).2 = v := by
  apply Fin.ext
  simp only [flatten,varIndex]
  omega

def derivationIndex (d : Fin 36) : DerivIndex :=
  if hd : d.val < 20 then
    .inl (⟨d.val / 2,by omega⟩,⟨d.val % 2,by omega⟩)
  else .inr (⟨(d.val-20)/2,by omega⟩,⟨(d.val-20)%2,by omega⟩)

def liftImages (k s : ℕ) (l : SparseRow 9) : List (Fin 18 × ℤ) :=
  if h : k+s < 2 then l.map fun x => (flatten x.1 ⟨k+s,h⟩,x.2) else []

def indexImages : DerivIndex → WordImages
  | .inl (g,k) => fun v => liftImages k.val (varIndex v).2.val (rootImages g (varIndex v).1)
  | .inr (i,k) => fun v => if (varIndex v).1 = 8 then
      liftImages k.val (varIndex v).2.val [(i.castSucc,1)] else []

def images (d : Fin 36) : WordImages := indexImages (derivationIndex d)

def seedWords (j : Fin 7) : Word :=
  [[0,0,0], [0,1], [1,1], [16,16,16,16,16], [16,16,16,17],
    [16,17,17], [17,17,17]].getD j.val []

theorem seedWords_map : ∀ j : Fin 7, (seedWords j).map varIndex = seedList j := by
  decide +kernel

theorem seedWord_mem (j : Fin 7) :
    rowEval varIndex [(seedWords j,1)] ∈ candidateIdeal := by
  simp only [rowEval_cons,rowEval_nil,one_smul,add_zero,seedWords_map]
  exact seed_mem_candidate j

theorem imageEval_lift (k s : ℕ) (l : SparseRow 9) :
    imageEval varIndex (liftImages k s l) =
      (l.map fun x => x.2 • modeX 2 x.1 (k+s)).sum := by
  by_cases h : k+s < 2
  · simp only [liftImages,imageEval,List.map_map,Function.comp_def,
      variable_flatten,modeX,dif_pos h]
  · simp only [liftImages,imageEval,List.map_nil,List.sum_nil,modeX,dif_neg h]
    induction l with
    | nil => rfl
    | cons x l ih =>
        change 0 = x.2 • (0 : MvPolynomial (Vars 2) ℂ) +
          (l.map fun x => x.2 • (0 : MvPolynomial (Vars 2) ℂ)).sum
        rw [zsmul_zero,← ih,add_zero]

theorem indexImages_X (d : DerivIndex) (v : Fin 18) :
    imageEval varIndex (indexImages d v) =
      candidateDeriv d (MvPolynomial.X (varIndex v)) := by
  cases d with
  | inl x =>
      obtain ⟨g,k⟩ := x
      rw [indexImages,imageEval_lift]
      rw [← evalZ_sparse (fun j : Fin 9 => modeX 2 j
        (k.val+(varIndex v).2.val)) (rootImages g (varIndex v).1)]
      simp only [evalZ,candidateDeriv,g0Deriv,MvPolynomial.mkDerivation_X,g0Image]
      change (∑ j : Fin 9, sparse (rootImages g (varIndex v).1) j •
        modeX 2 j (k.val+(varIndex v).2.val)) = _
      apply Finset.sum_congr rfl
      intro j _
      change sparse (rootImages g (varIndex v).1) j •
          modeX 2 j (k.val+(varIndex v).2.val) =
        (fZ br (zeroIndex g) (radIndex (varIndex v).1) (radIndex j) : ℂ) •
          modeX 2 j (k.val+(varIndex v).2.val)
      have hr : zeroIndex g = derivRoot g := rfl
      rw [hr,root_images_Z,Int.cast_smul_eq_zsmul]
  | inr x =>
      obtain ⟨i,k⟩ := x
      by_cases hv : (varIndex v).1 = 8
      · simp only [indexImages,imageEval_lift,List.map_cons,List.map_nil,
          List.sum_cons,List.sum_nil,one_smul,add_zero,candidateDeriv,eDeriv,
          MvPolynomial.mkDerivation_X,eImage,if_pos hv]
      · simp only [indexImages,imageEval,List.map_nil,List.sum_nil,
          candidateDeriv,eDeriv,MvPolynomial.mkDerivation_X,eImage,if_neg hv]

theorem images_X (d : Fin 36) (v : Fin 18) :
    imageEval varIndex (images d v) =
      candidateDeriv (derivationIndex d) (MvPolynomial.X (varIndex v)) := indexImages_X _ _

theorem rowEval_images (d : Fin 36) (l : WordRow) :
    rowEval varIndex (differentiateRow (images d) l) =
      candidateDeriv (derivationIndex d) (rowEval varIndex l) :=
  rowEval_differentiateRow varIndex (images d) _ (images_X d) l

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.images_X
#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.rowEval_images
