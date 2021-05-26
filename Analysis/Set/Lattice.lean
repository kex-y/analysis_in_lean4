import Analysis.Set.Basic

class hassup (α : Type u) where
  sup : α → α → α

class hasinf (α : Type u) where
  inf : α → α → α

class hasSup (α : Type u) where 
  Sup : Set α → α

class hasInf (α : Type u) where 
  Inf : Set α → α

infix:55 " ⊔ " => hassup.sup
infix:55 " ⊓ " => hasinf.inf
prefix:75 " ⨆ " => hasSup.Sup
prefix:75 " ⨅ " => hasInf.Inf

namespace Set

instance : hasSup (Set α) := { Sup := Union }

instance : hasInf (Set α) := { Inf := Inter }

instance [hasSup α] : hassup α := 
{ sup := λ x y => ⨆ (λ z : α => z = x ∨ z = y) }

instance [hasInf α] : hasinf α := 
{ inf := λ x y => ⨅ (λ z : α => z = x ∨ z = y) }

end Set