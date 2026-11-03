import VOA.DeligneAudit.D4FusionContactM2WordRows
import VOA.DeligneAudit.D4FusionContactPolynomialCandidate

/-! # Exact Leibniz semantics for finite word-row differentiation -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

abbrev WordImages := Fin 18 → List (Fin 18 × ℤ)

def canonicalRow (l : WordRow) : WordRow := l.map fun x => (canonical x.1,x.2)

def prependRow (v : Fin 18) (l : WordRow) : WordRow := l.map fun x => (v::x.1,x.2)

def imageTimes (w : Word) (l : List (Fin 18 × ℤ)) : WordRow :=
  l.map fun x => (x.1::w,x.2)

def differentiateWord (images : WordImages) : Word → WordRow
  | [] => []
  | v::w => imageTimes w (images v) ++ prependRow v (differentiateWord images w)

def differentiateRow (images : WordImages) (l : WordRow) : WordRow :=
  l.flatMap fun x => scaleRow x.2 (canonicalRow (differentiateWord images x.1))

def imageEval {ι : Type} (f : Fin 18 → ι) (l : List (Fin 18 × ℤ)) : MvPolynomial ι ℂ :=
  (l.map fun x => x.2 • MvPolynomial.X (f x.1)).sum

variable {ι : Type} (f : Fin 18 → ι)

theorem rowEval_canonical (l : WordRow) : rowEval f (canonicalRow l) = rowEval f l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change x.2 • polyWord ((canonical x.1).map f) + rowEval f (canonicalRow l) =
        x.2 • polyWord (x.1.map f) + rowEval f l
      rw [polyWord_canonical, ih]

theorem rowEval_prepend (v : Fin 18) (l : WordRow) :
    rowEval f (prependRow v l) = MvPolynomial.X (f v) * rowEval f l := by
  induction l with
  | nil => simp [prependRow]
  | cons x l ih =>
      change x.2 • polyWord ((v::x.1).map f) + rowEval f (prependRow v l) =
        MvPolynomial.X (f v) * (x.2 • polyWord (x.1.map f) + rowEval f l)
      rw [ih]
      simp only [List.map_cons, polyWord, List.prod_cons, mul_add, mul_smul_comm]

theorem rowEval_imageTimes (w : Word) (l : List (Fin 18 × ℤ)) :
    rowEval f (imageTimes w l) = imageEval f l * polyWord (w.map f) := by
  induction l with
  | nil => simp [imageTimes,imageEval]
  | cons x l ih =>
      change x.2 • polyWord ((x.1::w).map f) + rowEval f (imageTimes w l) =
        (x.2 • MvPolynomial.X (f x.1) + imageEval f l) * polyWord (w.map f)
      rw [ih]
      simp only [List.map_cons, polyWord, List.prod_cons, add_mul, smul_mul_assoc]

variable (images : WordImages)
variable (D : Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))
variable (hX : ∀ v, imageEval f (images v) = D (MvPolynomial.X (f v)))

include hX

theorem rowEval_differentiateWord (w : Word) :
    rowEval f (differentiateWord images w) = D (polyWord (w.map f)) := by
  induction w with
  | nil => simp [differentiateWord,polyWord,Derivation.map_one_eq_zero]
  | cons v w ih =>
      rw [differentiateWord, rowEval_append, rowEval_imageTimes, rowEval_prepend, ih, hX]
      change D (MvPolynomial.X (f v)) * polyWord (w.map f) +
        MvPolynomial.X (f v) * D (polyWord (w.map f)) =
        D (MvPolynomial.X (f v) * polyWord (w.map f))
      rw [D.leibniz]
      simp only [smul_eq_mul]
      ring

theorem rowEval_differentiateRow (l : WordRow) :
    rowEval f (differentiateRow images l) = D (rowEval f l) := by
  induction l with
  | nil => simp [differentiateRow]
  | cons x l ih =>
      change rowEval f (scaleRow x.2 (canonicalRow (differentiateWord images x.1)) ++
        differentiateRow images l) = D (x.2 • polyWord (x.1.map f) + rowEval f l)
      rw [rowEval_append, rowEval_scale, rowEval_canonical,
        rowEval_differentiateWord f images D hX, ih, map_add, map_zsmul]

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.rowEval_differentiateRow
