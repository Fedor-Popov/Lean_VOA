import VOA.DeligneAudit.D4FusionContactAllMCountResearchRows
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-! Small reified polynomials with arbitrary variable types. Natural jet ids
are unbounded; no truncation is introduced in the derivative compiler. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReducedRows

abbrev Word (σ : Type*) := List σ
abbrev Row (σ : Type*) := List (Word σ × ℤ)

variable {σ τ : Type*}

def canonical [LinearOrder σ] (w : Word σ) : Word σ := w.insertionSort (· ≤ ·)

def addTerm [DecidableEq σ] (w : Word σ) (z : ℤ) : Row σ → Row σ
  | [] => if z=0 then [] else [(w,z)]
  | (v,c)::l => if w=v then if z+c=0 then l else (v,z+c)::l else (v,c)::addTerm w z l

def collect [DecidableEq σ] : Row σ → Row σ
  | [] => []
  | (w,z)::l => addTerm w z (collect l)

def scale (z : ℤ) (r : Row σ) : Row σ := r.map fun x => (x.1,z*x.2)
def map (f : σ → τ) (r : Row σ) : Row τ := r.map fun x => (x.1.map f,x.2)

def multiplyWord [LinearOrder σ] (w : Word σ) (r : Row σ) : Row σ :=
  r.map fun x => (canonical (x.1++w),x.2)

def mul [LinearOrder σ] (p q : Row σ) : Row σ :=
  p.flatMap fun x => scale x.2 (multiplyWord x.1 q)

def wordDeriv [LinearOrder σ] (step : σ → Row σ) : Word σ → Row σ
  | [] => []
  | i::l => mul (step i) [(l,1)] ++ multiplyWord [i] (wordDeriv step l)

def deriv [LinearOrder σ] (step : σ → Row σ) (r : Row σ) : Row σ :=
  collect (r.flatMap fun x => scale x.2 (wordDeriv step x.1))

variable {A : Type*} [CommRing A] (v : σ → A)

def wordEval (w : Word σ) : A := (w.map v).prod
def eval (r : Row σ) : A := (r.map fun x => x.2 • wordEval v x.1).sum

@[simp] theorem eval_nil : eval v [] = 0 := rfl
@[simp] theorem eval_cons (w : Word σ) (z : ℤ) (r : Row σ) :
    eval v ((w,z)::r) = z • wordEval v w + eval v r := rfl

theorem eval_append (p q : Row σ) : eval v (p++q) = eval v p + eval v q := by
  simp [eval]

theorem eval_scale (z : ℤ) (r : Row σ) : eval v (scale z r) = z • eval v r := by
  induction r with
  | nil => simp [scale]
  | cons x r ih =>
      change (z*x.2) • wordEval v x.1 + eval v (scale z r) =
        z • (x.2 • wordEval v x.1 + eval v r)
      rw [ih,mul_smul,smul_add]

theorem wordEval_canonical [LinearOrder σ] (w : Word σ) :
    wordEval v (canonical w) = wordEval v w := by
  simpa only [canonical,wordEval] using ((List.perm_insertionSort (· ≤ ·) w).map v).prod_eq

theorem eval_addTerm [DecidableEq σ] (w : Word σ) (z : ℤ) (r : Row σ) :
    eval v (addTerm w z r) = z • wordEval v w + eval v r := by
  induction r with
  | nil => by_cases hz : z=0 <;> simp [addTerm,hz]
  | cons x r ih =>
      obtain ⟨u,c⟩ := x
      by_cases hw : w=u
      · subst w
        by_cases hz : z+c=0
        · simp only [addTerm,ite_true,if_pos hz,eval_cons]
          rw [← add_assoc,← add_smul,hz,zero_smul,zero_add]
        · simp only [addTerm,ite_true,if_neg hz,eval_cons,add_smul]
          abel
      · simp only [addTerm,if_neg hw,eval_cons,ih]
        abel

theorem eval_collect [DecidableEq σ] (r : Row σ) : eval v (collect r) = eval v r := by
  induction r with
  | nil => rfl
  | cons x r ih => rw [collect,eval_addTerm,ih,eval_cons]

theorem eval_zero_of_collect [DecidableEq σ] (r : Row σ) (h : collect r = []) : eval v r = 0 := by
  rw [← eval_collect,h,eval_nil]

theorem eval_multiplyWord [LinearOrder σ] (w : Word σ) (r : Row σ) :
    eval v (multiplyWord w r) = eval v r * wordEval v w := by
  induction r with
  | nil => simp [multiplyWord]
  | cons x r ih =>
      change x.2 • wordEval v (canonical (x.1++w)) + eval v (multiplyWord w r) =
        (x.2 • wordEval v x.1 + eval v r) * wordEval v w
      rw [wordEval_canonical,ih]
      simp only [wordEval,List.map_append,List.prod_append,add_mul,smul_mul_assoc]

theorem eval_mul [LinearOrder σ] (p q : Row σ) : eval v (mul p q) = eval v p * eval v q := by
  induction p with
  | nil => simp [mul]
  | cons x p ih =>
      simp only [mul,List.flatMap_cons,eval_append,eval_scale,eval_multiplyWord]
      change x.2 • (eval v q * wordEval v x.1) + eval v (mul p q) = _
      rw [ih,eval_cons,add_mul,smul_mul_assoc,mul_comm (eval v q) (wordEval v x.1)]

theorem eval_map (f : σ → τ) (w : τ → A) (r : Row σ) :
    eval w (map f r) = eval (fun i => w (f i)) r := by
  simp only [map,eval,wordEval,List.map_map,Function.comp_def]

theorem eval_hom {B : Type*} [CommRing B] (f : A →+* B) (r : Row σ) :
    f (eval v r) = eval (fun i => f (v i)) r := by
  simp only [eval,wordEval,map_list_sum,map_list_prod,map_zsmul,List.map_map,Function.comp_def]

section Derivation
variable {K : Type*} [CommRing K] [Algebra K A] [LinearOrder σ]
    (D : Derivation K A A) (step : σ → Row σ)
    (hX : ∀ i, D (v i) = eval v (step i))
include hX

theorem eval_wordDeriv (w : Word σ) : eval v (wordDeriv step w) = D (wordEval v w) := by
  induction w with
  | nil => simp [wordDeriv,wordEval]
  | cons i w ih =>
      rw [wordDeriv,eval_append,eval_mul,eval_cons,eval_nil,one_zsmul,add_zero,
        eval_multiplyWord,ih]
      simp only [wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
      rw [D.leibniz,hX]
      simp only [smul_eq_mul]
      ring

theorem eval_deriv (r : Row σ) : eval v (deriv step r) = D (eval v r) := by
  rw [deriv,eval_collect]
  induction r with
  | nil => simp
  | cons x r ih =>
      rw [List.flatMap_cons,eval_append,eval_scale,eval_wordDeriv v D step hX,ih,
        eval_cons,map_add,map_zsmul]

theorem eval_iterate_deriv (r : Row σ) (k : ℕ) :
    eval v (((deriv step : Row σ → Row σ)^[k]) r) = ((D : A → A)^[k]) (eval v r) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',eval_deriv v D step hX,ih,
      Function.iterate_succ_apply']
end Derivation
/-- Adjacent aggregation is sound even when the input order is arbitrary. -/
def headAdd (w : Word ℕ) (z : ℤ) (r : Row ℕ) : Row ℕ :=
  if z=0 then r else match r with
  | [] => [(w,z)]
  | (u,c)::l => if w=u then if z+c=0 then l else (u,z+c)::l else (w,z)::r

def adjacent : Row ℕ → Row ℕ
  | [] => []
  | (w,z)::l => headAdd w z (adjacent l)

def wordKey (w : Word ℕ) : ℕ := w.foldl (fun a i => 33*a+i+1) 0

def mergeFuel : ℕ → Row ℕ → Row ℕ → Row ℕ
  | 0,p,q => p++q
  | _k+1,[],q => q
  | _k+1,p,[] => p
  | k+1,x::p,y::q =>
      if wordKey x.1 ≤ wordKey y.1 then x::mergeFuel k p (y::q)
      else y::mergeFuel k (x::p) q

def mergeRuns : List (Row ℕ) → List (Row ℕ)
  | [] => []
  | [r] => [r]
  | p::q::rs => mergeFuel (p.length+q.length) p q :: mergeRuns rs

def sortRuns : ℕ → List (Row ℕ) → Row ℕ
  | 0,rs => rs.flatten
  | _k+1,[] => []
  | _k+1,[r] => r
  | k+1,p::q::rs => sortRuns k (mergeRuns (p::q::rs))

def fastSort (r : Row ℕ) : Row ℕ := sortRuns r.length (r.map fun x => [x])

def fastCollect (r : Row ℕ) : Row ℕ := adjacent (fastSort r)

theorem eval_headAdd (v : ℕ → A) (w : Word ℕ) (z : ℤ) (r : Row ℕ) :
    eval v (headAdd w z r) = z • wordEval v w + eval v r := by
  by_cases hz : z=0
  · simp [headAdd,hz]
  · cases r with
    | nil => simp [headAdd,hz]
    | cons x r =>
        obtain ⟨u,c⟩ := x
        by_cases hw : w=u
        · subst w
          by_cases hs : z+c=0
          · simp only [headAdd,if_neg hz,ite_true,if_pos hs,eval_cons]
            rw [← add_assoc,← add_smul,hs,zero_smul,zero_add]
          · simp only [headAdd,if_neg hz,ite_true,if_neg hs,eval_cons,add_smul]
            abel
        · simp only [headAdd,if_neg hz,if_neg hw,eval_cons]

theorem eval_adjacent (v : ℕ → A) (r : Row ℕ) : eval v (adjacent r) = eval v r := by
  induction r with
  | nil => rfl
  | cons x r ih => rw [adjacent,eval_headAdd,ih,eval_cons]

theorem eval_mergeFuel (v : ℕ → A) (k : ℕ) (p q : Row ℕ) :
    eval v (mergeFuel k p q) = eval v p + eval v q := by
  induction k generalizing p q with
  | zero => exact eval_append v p q
  | succ k ih =>
      cases p with
      | nil => simp [mergeFuel]
      | cons x p =>
          cases q with
          | nil => simp [mergeFuel]
          | cons y q =>
              simp only [mergeFuel]
              split_ifs
              · rw [eval_cons,ih]
                exact (add_assoc _ _ _).symm
              · rw [eval_cons,ih]
                exact add_left_comm _ _ _

theorem eval_mergeRuns (v : ℕ → A) (rs : List (Row ℕ)) :
    eval v (mergeRuns rs).flatten = eval v rs.flatten := by
  match rs with
  | [] => rfl
  | [r] => rfl
  | p::q::rs =>
      simp only [mergeRuns,List.flatten_cons,eval_append]
      rw [eval_mergeFuel,eval_mergeRuns v rs]
      abel
termination_by rs.length

theorem eval_sortRuns (v : ℕ → A) (k : ℕ) (rs : List (Row ℕ)) :
    eval v (sortRuns k rs) = eval v rs.flatten := by
  induction k generalizing rs with
  | zero => rfl
  | succ k ih =>
      cases rs with
      | nil => rfl
      | cons p rs =>
          cases rs with
          | nil => simp [sortRuns]
          | cons q rs => rw [sortRuns,ih,eval_mergeRuns]

theorem eval_fastSort (v : ℕ → A) (r : Row ℕ) : eval v (fastSort r) = eval v r := by
  rw [fastSort,eval_sortRuns]
  have h : (r.map fun x => [x]).flatten = r := by
    induction r with
    | nil => rfl
    | cons x r ih => simp [ih]
  rw [h]

theorem eval_fastCollect (v : ℕ → A) (r : Row ℕ) : eval v (fastCollect r) = eval v r := by
  rw [fastCollect,eval_adjacent,eval_fastSort]

theorem eval_zero_of_fastCollect (v : ℕ → A) (r : Row ℕ) (h : fastCollect r = []) :
    eval v r = 0 := by
  rw [← eval_fastCollect,h,eval_nil]

#print axioms eval_deriv
#print axioms eval_zero_of_collect
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReducedRows
