import Analysis.Set.Basic

namespace Set

def image (f : α → β) (s : Set α) : Set β := { y : β | ∃ x ∈ s, y = f x }

theorem memImage {s : Set α} {f : α → β} (y : β) : 
  y ∈ s.image f ↔ ∃ x ∈ s, y = f x :=  Iff.rfl

theorem memImageOfMem {s : Set α} {f : α → β} {x : α} (hx : x ∈ s) : 
  f x ∈ s.image f := Exists.intro x ⟨hx, rfl⟩

instance [f : Coe α β] : Coe (Set α) (Set β) := 
  ⟨λ S => { y | y ∈ S.image f.coe }⟩

def preimage (f : α → β) (s : Set β) : Set α := { x : α | f x ∈ s }

theorem memPreimage {s : Set β} {f : α → β} {x : α} : 
  x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl

theorem preimageUniv (f : α → β) : univ.preimage f = univ := rfl

theorem preimageMono (f : α → β) {s t : Set β} (hst : s ⊆ t) : 
  s.preimage f ⊆ t.preimage f := 
  λ x hx => hst _ hx

theorem preimageInter (f : α → β) (s t : Set β) : 
  (s ∩ t).preimage f = s.preimage f ∩ t.preimage f := rfl

theorem preimageId (s : Set α) : preimage id s = s := rfl

end Set