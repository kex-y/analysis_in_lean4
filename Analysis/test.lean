import Lean
open Lean Macro

universes u v

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

notation:50 x " ∉ " s => ¬ x ∈ s

def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
p

class Subset (α : Type u) where
  subset : α → α → Prop

infix:50 " ⊆ " => Subset.subset

class Union (α : Type u) where
  union : α → α → α

infixl:65 " ∪ " => Union.union

class Inter (α : Type u) where
  inter : α → α → α

infixl:70 " ∩ " => Inter.inter

class Sdiff (α : Type u) where
  sdiff : α → α → α

infix:70 " \\ " => Sdiff.sdiff

namespace Set

variable {α : Type u} {β : Type v}

protected def mem (a : α) (s : Set α) :=
s a

instance : Mem α (Set α) :=
⟨Set.mem⟩

protected def subset (s₁ s₂ : Set α) :=
∀ {a}, a ∈ s₁ → a ∈ s₂

instance : Subset (Set α) :=
⟨Set.subset⟩

instance : EmptyCollection (Set α) :=
⟨λ a => false⟩

declare_syntax_cat binderterm -- notation for `a` or `a : A` or `a ∈ S`
syntax ident : binderterm
syntax ident " : " term : binderterm
syntax ident " ∈ " term : binderterm

-- Notation for sets
syntax "⦃ " binderterm " | " term " ⦄" : term

macro_rules
| `(⦃ $x:ident : $t | $p ⦄) => `(setOf (λ ($x:ident : $t) => $p))
| `(⦃ $x:ident | $p ⦄) => `(setOf (λ ($x:ident) => $p))
| `(⦃ $x:ident ∈ $s | $p ⦄) => `(setOf (λ $x => $x ∈ $s ∧ $p))

syntax "∀" binderterm "," term : term
syntax "∃" binderterm "," term : term

macro_rules
| `(∀ $x:ident ∈ $s, $p) => `(∀ $x:ident, $x ∈ $s → $p)
| `(∃ $x:ident ∈ $s, $p) => `(∃ $x:ident, $x ∈ $s ∧ $p)

def univ : Set α := ⦃a | True ⦄

protected def insert (a : α) (s : Set α) : Set α :=
⦃b | b = a ∨ b ∈ s⦄

protected def singleton (a : α) : Set α :=
⦃b | b = a⦄

syntax " ⦃ " term,* " ⦄ " : term

macro_rules
| `(⦃ $elems:term,* ⦄) => do
  let n := elems.elemsAndSeps.size
  if n = 0 then throwUnsupported
  let rec expandSetLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
    match i, skip with
    | 0, _ => result
    | i + 1, true => expandSetLit i false result
    | i + 1, false => expandSetLit i true (← ``(Set.insert $(elems.elemsAndSeps[i]) $result))
  let some hd ← pure $ elems.elemsAndSeps.back? | throwUnsupported
  expandSetLit (n - 1) true (← ``(Set.singleton $hd))
  

@[appUnexpander Set.singleton] def singletonUnexpander : Lean.PrettyPrinter.Unexpander
| `(Set.singleton $a) => `(⦃ $a ⦄)
| _ => throw ()

@[appUnexpander Set.insert]
def insertUnexpander : Lean.PrettyPrinter.Unexpander
| `(Set.insert $a ⦃ $t ⦄) => `(⦃$a, $t⦄)
| `(Set.insert $a ⦃ $ts,* ⦄) => `(⦃$a, $ts,*⦄)
| _ => throw ()

#check ⦃ 3, 2, 1 ⦄ --  ⦃ 3, 2, 1 ⦄  : Set Nat

example : ⦃ 1 ⦄ = ⦃ 2, 2 ⦄ := by
  skip
  -- ⊢  ⦃ 1 ⦄  =  ⦃ 2, 2 ⦄
  admit


example : ⦃1, 2, 3⦄ = ⦃1, 2⦄ := by
  skip
  -- ⊢  ⦃ 1, 2, 3 ⦄  =  ⦃ 1, 2 ⦄ 
  admit