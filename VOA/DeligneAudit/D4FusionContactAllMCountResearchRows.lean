import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! # Light exact integer word cancellation for finite color identities

The checker is sound in every commutative ring and for every variable
assignment. It computes neither a rank nor a polynomial quotient dimension.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Rows

abbrev Word (n : ℕ) := List (Fin n)
abbrev Row (n : ℕ) := List (Word n × ℤ)

variable {n : ℕ}

def canonical (w : Word n) : Word n := w.insertionSort (· ≤ ·)

def addTerm (w : Word n) (z : ℤ) : Row n → Row n
  | [] => if z = 0 then [] else [(w,z)]
  | (v,c)::l => if w = v then
      if z+c = 0 then l else (v,z+c)::l
    else (v,c)::addTerm w z l

def collect : Row n → Row n
  | [] => []
  | (w,z)::l => addTerm w z (collect l)

def scale (z : ℤ) (l : Row n) : Row n := l.map fun x => (x.1,z*x.2)

def map {k : ℕ} (f : Fin n → Fin k) (l : Row n) : Row k :=
  l.map fun x => (x.1.map f,x.2)

def multiply (v : Fin n) (l : Row n) : Row n :=
  l.map fun x => (canonical (x.1 ++ [v]),x.2)

variable {A : Type*} [CommRing A] (b : Fin n → A)

def wordEval (w : Word n) : A := (w.map b).prod

def eval (l : Row n) : A := (l.map fun x => x.2 • wordEval b x.1).sum

@[simp] theorem eval_nil : eval b [] = 0 := rfl

@[simp] theorem eval_cons (w : Word n) (z : ℤ) (l : Row n) :
    eval b ((w,z)::l) = z • wordEval b w + eval b l := rfl

@[simp] theorem eval_append (l r : Row n) : eval b (l++r) = eval b l + eval b r := by
  simp [eval]

theorem eval_scale (z : ℤ) (l : Row n) : eval b (scale z l) = z • eval b l := by
  induction l with
  | nil => simp [scale]
  | cons x l ih =>
      change (z*x.2) • wordEval b x.1 + eval b (scale z l) =
        z • (x.2 • wordEval b x.1 + eval b l)
      rw [ih,mul_smul]
      exact (smul_add z (x.2 • wordEval b x.1) (eval b l)).symm

theorem wordEval_canonical (w : Word n) : wordEval b (canonical w) = wordEval b w :=
  by simpa only [canonical,wordEval] using ((List.perm_insertionSort (· ≤ ·) w).map b).prod_eq

theorem eval_addTerm (w : Word n) (z : ℤ) (l : Row n) :
    eval b (addTerm w z l) = z • wordEval b w + eval b l := by
  induction l with
  | nil => by_cases hz : z=0 <;> simp [addTerm,hz]
  | cons x l ih =>
      obtain ⟨v,c⟩ := x
      by_cases hw : w=v
      · subst w
        by_cases hz : z+c=0
        · simp only [addTerm,ite_true,if_pos hz,eval_cons]
          rw [← add_assoc,← add_smul,hz,zero_smul,zero_add]
        · simp only [addTerm,ite_true,if_neg hz,eval_cons,add_smul]
          abel
      · simp only [addTerm,if_neg hw,eval_cons,ih]
        abel

theorem eval_collect (l : Row n) : eval b (collect l) = eval b l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [collect,eval_addTerm,ih,eval_cons]

theorem eval_zero_of_collect (l : Row n) (h : collect l = []) : eval b l = 0 := by
  rw [← eval_collect,h,eval_nil]

theorem eval_multiply (v : Fin n) (l : Row n) :
    eval b (multiply v l) = eval b l * b v := by
  induction l with
  | nil => simp [multiply]
  | cons x l ih =>
      change x.2 • wordEval b (canonical (x.1 ++ [v])) + eval b (multiply v l) =
        (x.2 • wordEval b x.1 + eval b l) * b v
      rw [wordEval_canonical,ih]
      simp only [wordEval,List.map_append,List.map_cons,List.map_nil,
        List.prod_append,List.prod_cons,List.prod_nil,mul_one,add_mul,smul_mul_assoc]

theorem eval_map {k : ℕ} (f : Fin n → Fin k) (c : Fin k → A) (l : Row n) :
    eval c (map f l) = eval (fun v => c (f v)) l := by
  simp only [map,eval,wordEval,List.map_map,Function.comp_def]

theorem eval_hom {B : Type*} [CommRing B] (f : A →+* B) (l : Row n) :
    f (eval b l) = eval (fun v => f (b v)) l := by
  simp only [eval,wordEval,map_list_sum,map_list_prod,map_zsmul,List.map_map,Function.comp_def]

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Rows

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Rows.eval_zero_of_collect
