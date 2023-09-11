def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F β
#check G α
#check G Nat β

#check Type
#check Type 0 -- these two are the same
#check Type 1
#check Type 2

universe u
def P (α : Type u) : Type u := Prod α α
#check P

def Q.{v} (α : Type v) : Type v := Prod α α
#check Q
