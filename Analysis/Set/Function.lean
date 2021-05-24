import Analysis.Set.Basic

namespace Set

def image {α} (s : Set α) (f : α → β) : Set β := { y : β | ∃ x ∈ s, y = f x }

theorem memImage {s : Set α} {f : α → β} (y : β) : 
  y ∈ s.image f ↔ ∃ x ∈ s, y = f x :=  Iff.rfl

theorem memImageOfMem {s : Set α} {f : α → β} {x : α} (hx : x ∈ s) : 
  f x ∈ s.image f := Exists.intro x ⟨hx, rfl⟩

instance [f : Coe α β] : Coe (Set α) (Set β) := 
  ⟨λ S => { y | y ∈ S.image f.coe }⟩

end Set