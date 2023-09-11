-- general definitions

def double (x : Nat) : Nat :=
  x + x
def double' : Nat → Nat :=
  fun x => x + x
def double'' :=
  λ x : Nat => x + x

#eval double 3
#eval double' 3
#eval double'' 3

def doTwice :=
  λ (f : Nat → Nat) (x : Nat) => (f ∘ f) x

#eval doTwice double 3

def square :=
  λ x : Nat => x * x

def compose :=
  λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => (g ∘ f) x

#eval compose Nat Nat Nat double square 3

-- local definitions

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y
