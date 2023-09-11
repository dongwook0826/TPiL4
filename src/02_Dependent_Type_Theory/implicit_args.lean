#check List.cons 0 (List.nil)

def as : List Nat := List.nil
def bs : List Nat := List.cons 42 List.nil

#check List.append as bs
#eval  List.append as bs

-- leaving the argument(s) implicit

universe u

def Lst (α : Type u) : Type u := List α
def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α :=
  List.cons a as
def Lst.nil {α : Type u} : Lst α :=
  List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α :=
  List.append as bs

#check Lst.cons 0 Lst.nil
-- #eval  Lst.cons 0 Lst.nil

def as' : Lst Nat := Lst.nil
def bs' : Lst Nat := Lst.cons 42 Lst.nil

#check Lst.append as bs

def ident {α : Type u} (x : α) := x

section
  -- same as...
  variable {α : Type u}
  variable (x : α)
  def ident' := x
end

#check ident
#check ident 1
#check ident "hello"
#check @ident

#check ident'
#check ident' 1
#check ident' "hello"
#check @ident'

-- some built-in examples

#check List.nil
#check id
#check @List.nil
#check @id
#check (List.nil : List Nat)
#check (id : Nat → Nat)

-- making all the implicit arguments explicit
#check @id Nat
#check @id Bool

#eval @id Nat 42
#eval @id Bool true