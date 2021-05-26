theorem impNot {p q : Prop} : p → ¬ q ↔ ¬ (p ∧ q) := 
  ⟨ λ hpq h => hpq h.1 h.2, λ h hp hq => h <| And.intro hp hq ⟩  

theorem Exists.impNot {p q : α → Prop} : (∃ x, p x → ¬ q x) ↔ ∃ x, ¬ (p x ∧ q x) := by 
  apply Iff.intro
  intro h
  cases h with | intro x hx => 
  { exact ⟨ x, λ hs => hx hs.1 hs.2 ⟩ }
  intro h 
  cases h with | intro x hx => 
  { exact ⟨ x, λ hpx hqx => hx <| And.intro hpx hqx ⟩ }

namespace Classical

theorem contrapositive {p q : Prop} : (¬ q → ¬ p) → p → q := 
  λ hqp hp => match em q with 
    | Or.inl h => h
    | Or.inr h => False.elim <| hqp h hp
  
theorem notNot {p : Prop} : ¬ ¬ p ↔ p := by 
  apply Iff.intro
  { intro hp; cases em p with 
    | inl   => assumption
    | inr h => exact False.elim <| hp h }
  { exact λ hp hnp => False.elim <| hnp hp }

theorem notForall {p : α → Prop} : (¬ ∀ x, p x) → ∃ x, ¬ p x := by 
  { apply contrapositive; intro hx; rw [notNot]; intro x;
    cases em (p x); { assumption }
      { apply False.elim <| hx <| Exists.intro x _; assumption } }  

theorem notAnd {p q : Prop} : p ∧ ¬ q ↔ ¬ (p → q) := by
  apply Iff.intro
  { exact λ h himp => h.2 <| himp h.1 }
  { intro h; apply And.intro;
    { revert h; apply contrapositive; rw [notNot];
      exact λ hnp hp => False.elim <| hnp hp }
    { exact λ hq => h <| λ _ => hq } }

theorem Exists.notAnd {p q : α → Prop} : 
  (∃ x, p x ∧ ¬ q x) ↔ ∃ x, ¬ (p x → q x) := by
  apply Iff.intro
  { intro h;
    let ⟨ x, ⟨ hp, hnq ⟩ ⟩ := h;
    exact Exists.intro x λ h => hnq <| h hp }
  { intro h;
    let ⟨ x, hx ⟩ := h;
    apply Exists.intro x;
    apply And.intro;
    { revert hx; apply contrapositive;
      exact λ hpx hpq => hpq λ hp => False.elim <| hpx hp }
    { intro foo;
      apply hx;
      intro bar;
      assumption; } }

end Classical