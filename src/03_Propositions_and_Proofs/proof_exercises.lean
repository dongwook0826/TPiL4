variable (p q r : Prop)

-- commutativity of ∧ and ∨
theorem and_comm : p ∧ q ↔ q ∧ p :=
  have hlr (p q : Prop) (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
  Iff.intro (hlr p q) (hlr q p)
theorem or_comm : p ∨ q ↔ q ∨ p :=
  have hlr (p q : Prop) (h : p ∨ q) : q ∨ p :=
    h.elim
      (fun hp : p => Or.inr hp)
      (fun hq : q => Or.inl hq)
  Iff.intro (hlr p q) (hlr q p)

-- associativity of ∧ and ∨
theorem and_assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
      ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
theorem or_assoc : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun hpq : p ∨ q =>
          hpq.elim
            (fun hp : p => Or.inl hp)
            (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          hqr.elim
            (fun hq : q => Or.inl (Or.inr hq))
            (fun hr : r => Or.inr hr)))

-- distributivity
theorem and_or_dist : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      h.right.elim
        (fun hq : q => Or.inl ⟨h.left, hq⟩)
        (fun hr : r => Or.inr ⟨h.left, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩)
        (fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩))
theorem or_and_dist : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      h.elim
        (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      h.left.elim
        (fun hp : p => Or.inl hp)
        (fun hq : q =>
          h.right.elim
            (fun hp : p => Or.inl hp)
            (fun hr : r => Or.inr ⟨hq, hr⟩))) 

-- other properties
theorem prop1 : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun (h : p → (q → r)) (hpq : p ∧ q) =>
      (h hpq.left) hpq.right)
    (fun (h : p ∧ q → r) (hp : p) (hq : q) =>
      h ⟨hp, hq⟩)
theorem prop2 : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : p ∨ q → r =>
      ⟨fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq)⟩)
    (fun (h : (p → r) ∧ (q → r)) (hpq : p ∨ q) =>
      hpq.elim
        (fun hp : p => h.left hp)
        (fun hq : q => h.right hq))
theorem prop3 : ¬(p ∨ q) ↔ ¬p ∧ ¬q := -- follows from prop #2
  prop2 p q False
theorem prop4 : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (h : ¬p ∨ ¬q) (hpq : p ∧ q) =>
    h.elim
      (fun hnp : ¬p => hnp hpq.left)
      (fun hnq : ¬q => hnq hpq.right)
theorem prop5 : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p =>
    show False from h.right h.left
theorem prop6 : p ∧ ¬q → ¬(p → q) :=
  fun (h : p ∧ ¬q) (hpq : p → q) =>
    h.right (hpq h.left)
theorem prop7 : ¬p → (p → q) :=
  fun (hnp : ¬p) (hp : p) =>
    absurd hp hnp
theorem prop8 : (¬p ∨ q) → (p → q) :=
  fun (h : ¬p ∨ q) (hp : p) =>
    h.elim
      (fun hnp : ¬p => absurd hp hnp)
      (fun hq : q => hq)
theorem prop9 : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      h.elim
        (fun hp : p => hp)
        False.elim)
    (fun hp : p => Or.inl hp)
theorem prop10 : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => h.right)
    False.elim
theorem prop11 : (p → q) → (¬q → ¬p) :=
  fun (hpq : p → q) (hnq : ¬q) (hp : p) =>
    hnq (hpq hp)
theorem prop12 : ¬(p ↔ ¬p) :=
  have lem (p q : Prop) (h1 : p → p → q) : p → q :=
    fun hp : p => h1 hp hp
  fun h : p ↔ ¬p =>
    have hnp : ¬p := lem p False h.mp
    have hp : p := h.mpr hnp
    hnp hp


-- properties requiring excluded middle
open Classical

variable (p q r s : Prop)

theorem dneg (hnnp : ¬¬p) : p :=
  byContradiction (fun hnp : ¬p => hnnp hnp)
theorem clprop1 : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  fun h : p → r ∨ s =>
    byCases
      (fun hr : r => Or.inl (fun hp : p => hr))
      (fun hnr : ¬r =>
        Or.inr
          (fun hp : p =>
            (h hp).elim
              (fun hr : r => absurd hr hnr)
              (fun hs : s => hs)))
theorem clprop2 : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) =>
    byCases
      (fun hp : p =>
        Or.inr (fun hq : q => h ⟨hp, hq⟩))
      (fun hnp : ¬p => Or.inl hnp)
theorem clprop3 : ¬(p → q) → p ∧ ¬q :=
  have lem (p q : Prop) (h : ¬(¬p ∨ q)) : p ∧ ¬q :=
    ⟨dneg p (fun hnp : ¬p => h (Or.inl hnp)),
      fun hq : q => h (Or.inr hq)⟩
  fun h : ¬(p → q) =>
    lem p q ((prop11 (¬p ∨ q) (p → q) (prop8 p q)) h)
theorem clprop4 : (p → q) → (¬p ∨ q) :=
  fun h : p → q =>
    byCases
      (fun hp : p => Or.inr (h hp))
      (fun hnp : ¬p => Or.inl hnp)
theorem clprop5 : (¬q → ¬p) → (p → q) :=
  fun (h : ¬q → ¬p) (hp : p) =>
    byCases
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd hp (h hnq))
theorem clprop6 : p ∨ ¬p := em p
theorem clprop7 : (((p → q) → p) → p) :=
  have lem := clprop4 (p → q) p
  fun h : ((p → q) → p) =>
    (lem h).elim
      (fun hnpq : ¬(p → q) =>
        (clprop3 p q hnpq).left)
      (fun hp : p => hp)
