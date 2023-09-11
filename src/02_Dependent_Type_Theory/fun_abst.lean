#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x : Nat => x + 5
#check λ x => x + 5

#eval (λ x => x + 5) 10

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x => (g ∘ f) x
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
