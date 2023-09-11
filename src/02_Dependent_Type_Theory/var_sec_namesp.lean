-- variable & section

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #check compose
  #check g (f x)
end useful

-- namespace

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa := f (f a)

    #check fa
    #check ffa
  end Bar

  #check a
  #check f
  #check fa
  #check Foo.fa
end Foo

#check Foo.a
#check Foo.f
#check Foo.Bar.ffa

open Foo
#check a
#check f
#check Bar.ffa

-- namespace example

#check List.nil
#check List.cons
#check List.map

variable (x y : Nat)
def eqxy := x = y
#check x = y
#check eqxy
