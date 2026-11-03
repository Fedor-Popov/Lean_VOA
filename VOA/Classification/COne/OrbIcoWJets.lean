import VOA.Classification.COne.OrbOddZhu

/-! Finite Taylor jets of the actual width-six Benoit--Saint-Aubin recurrence.
All rational computations below use kernel evaluation. A jet is stored with
its constant coefficient first and includes coefficients through order P. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd

abbrev Jet := List ℚ

def jetZero (P : ℕ) : Jet := List.replicate (P+1) 0

def jetCut (P : ℕ) (a : Jet) : Jet :=
  (List.range (P+1)).map fun j => (a[j]?).getD 0

def jetAdd (P : ℕ) (a b : Jet) : Jet := jetCut P (paddL a b)
def jetMul (P : ℕ) (a b : Jet) : Jet := jetCut P (pmulL a b)
def jetScale (c : ℚ) (a : Jet) : Jet := pscaleL c a
def jetSum (P : ℕ) (xs : List Jet) : Jet := xs.foldl (jetAdd P) (jetZero P)

def jetH (P : ℕ) : Jet :=
  (List.range (P+1)).map fun j => if j=0 then 36 else 42*(-1)^j

def jetK (P : ℕ) (self : Bool) : Jet := if self then jetH P else jetZero P

def jetBracket (P : ℕ) (self : Bool) (n q r j : ℕ) : Jet :=
  jetAdd P (jetAdd P (jetScale ((r-j : ℕ)+1) (jetH P))
    (jetScale (-1) (jetK P self))) (jetCut P [(j : ℚ)-2*((n+q : ℕ) : ℚ)])

def jetSource (P : ℕ) (self : Bool) (n r : ℕ) (A : List (List Jet)) : List Jet :=
  (List.range 7).map fun q => jetSum P ((List.range r).map fun j =>
    jetAdd P (jetScale ((-1 : ℚ)^(r-j))
      (jetMul P (jetBracket P self n q r j) ((((A[j]?).getD [])[q]?).getD [])))
      (if r-j=2 ∧ 0<q then (((A[j]?).getD [])[q-1]?).getD [] else jetZero P))

def jetStep (P : ℕ) (self : Bool) (n r : ℕ) (A : List (List Jet)) : List Jet :=
  (jetSource P self n r A).map fun a =>
    jetScale (-1/((r : ℚ)*(13-(r : ℚ)))) (jetMul P [1,1] a)

def jetRows (P : ℕ) (self : Bool) (n : ℕ) : ℕ → List (List Jet)
  | 0 => [(List.range 7).map fun q => if q=0 then jetCut P [1] else jetZero P]
  | r+1 => let A := jetRows P self n r; A ++ [jetStep P self n (r+1) A]

def widthCoefficients (P : ℕ) (self : Bool) (n : ℕ) : List Jet :=
  jetSource P self n 13 (jetRows P self n 12)

end VOA.Classification.COne.OrbIcoW
