/- # Lean implementation and verification of the insert sort algorithm! -/
import Mathlib.Data.Nat.Basic
namespace Notes
variable {α : Type} (f: α → α → Bool) (r : α → α → Prop) [DecidableRel r]

/-
We sort lists of type 'α' using the comparison function 'f' or 'r'.

If 'f a₁ a₂ = true', then this is the "correct" order. Otherwise, it is "incorrect". 

If 'r a₁ a₂' has a proof, then this is the "correct" order. Otherwise, it is "incorrect". 

What are some examples of sorted lists?
- [] should be "sorted"
- for any 'a : α', then '[a]' is sorted
- for any 'a₁ a₂ : α' and any 'as : List α' such that
  'f a₁ a₂ = true' and 'a₂::as' is sorted, then 'a₁::a₂::as' is sorted
-/

inductive Sorted (r : α → α → Prop) : List α → Prop where
  | nil : Sorted r []
  | single {a:α} : Sorted r [a]
  | longer {a₁ a₂ : α} {as : List α} (h : r a₁ a₂) 
    (h' : Sorted r (a₂::as)) : Sorted r (a₁::a₂::as)
  
open Sorted 
example : Sorted (·≤·) [1, 2, 3] := by
  apply longer 
  · simp
  · apply longer
    · simp
    · apply single
  
theorem sorted_tail_of_sorted (a : α) (as : List α)
    (h : Sorted r (a::as)) : Sorted r as := by
  match h with 
  | single => apply nil
  | longer _ h'' => exact h''

/- Insertion Sort Implementation -/
def insert (a : α) (l : List α) : List α :=
  match l with
  | [] => [a]
  | a'::as =>
    if r a a' then a::a'::as else a'::insert a as

@[simp]
theorem len_insert_eq_succ_len {a : α} {l : List α} :
    (insert r a l).length = l.length + 1 := 
  match l with
  | [] => by simp[insert]
  | a'::as =>
    if h : r a a' then by simp [insert, h] else
    by simp [insert, h]; apply len_insert_eq_succ_len

def insertSort (l : List α) : List α := 
  match l with
  | [] => []
  | a::as => insert r a <| insertSort as

-- Check that the implementation works on certain inputs
#eval insertSort (·≤·) [4, 5, 2, 4, 5, 6]
#eval insertSort (fun (b b' : Bool) => b && b') [true, false, false]
#eval insertSort (fun (_ _ ) => false) [4, 5, 2, 4, 5, 6]

/- Establish that the output of insertSort will always match the behavior defined in Sorted, i.e., verify the algorithm -/

class Asymmetric (r : α → α → Prop) where
  asym {a a'} : ¬r a a' → r a' a

open Asymmetric

def Sorted.cons {a : α} {l : List α} (h₁ : Sorted r l)
  (h₂ : l.length > 0) (h₃ : r a l[0]) : Sorted r (a::l) := 
  match h₁ with
  | nil => single
  | single => longer h₃ single
  | longer h h' => longer h₃ <| longer h h' 

theorem ordered_of_sorted {a a' : α} (as : List α)
  (h : Sorted r (a::a'::as)) : r a a' :=
  match h with
  | longer h' _ => h'

theorem ordered_cons_insert_of_unordered {a a' : α} {as : List α}
    (h : Sorted r (a'::as)) (h' : r a' a) : r a' (insert r a as)[0] :=
  match as with 
  | [] => by simpa[insert]
  | a''::as' => 
    if h'' : r a a'' then
    by simpa[insert, h'']
    else
    by simp [insert, h'']; apply ordered_of_sorted r h

theorem insert_sorted_of_sorted {a : α} {l : List α} [Asymmetric r]
    (h : Sorted r l) : Sorted r <| insert r a l :=
  match l with
  | [] => single
  | a'::as =>
    if h' : r a a' then
    by simp[insert, h']; apply longer h' h
    else
    by 
      simp[insert, h']
      apply cons r
      · apply insert_sorted_of_sorted <| sorted_tail_of_sorted r a' as h
      · apply ordered_cons_insert_of_unordered r h 
        · apply asym; simp; assumption

theorem sorted_of_insertSort (l : List α) [Asymmetric r] : 
    Sorted r <| insertSort r l :=
  match l with
  | [] => nil
  | a::as => by
    dsimp [insertSort]
    apply insert_sorted_of_sorted r <| sorted_of_insertSort as 

variable [Trans r r r]

theorem totally_ordered_of_sorted {l : List α} (h : Sorted r l) :
  ∀ {i j : ℕ}, (i < j) → (_: i < l.length) → (_: j < l.length) → r l[i] l[j] := 
  match h with
  | nil => fun _ h' _ => False.elim <| by simp [h'] at h'
  | single => sorry
  | longer h₁ h₂ => sorry