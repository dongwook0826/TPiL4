-- dependent function(or arrow) type

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
-- (α : Type) must be assumed

#check cons Nat
#check cons Bool
#check cons

#check cons Nat 42 List.nil
#eval  cons Nat 42 List.nil

#check (n : Nat) → Bool -- just Nat → Bool

#check @List.cons
#check List.cons

-- dependent product

section dep_prod
  universe u v

  -- f and g are the same
  
  def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
    ⟨a, b⟩
  
  def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
    Sigma.mk a b

  -- same for h1 and h2

  def h1 (x : Nat) : Nat :=
    (f Type (λ α => α) Nat x).2

  #eval h1 5

  def h2 (x : Nat) : Nat :=
    (g Type (λ α => α) Nat x).2
  
  #eval h2 5

  def h11 (x : Nat) : Nat :=
    (f Type id Nat x).2
  
  #eval h11 42
  #eval @id Nat 42

end dep_prod