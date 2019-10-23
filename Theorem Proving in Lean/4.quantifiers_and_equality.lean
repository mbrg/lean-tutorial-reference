namespace one
    /-
    Prove these equivalences:

    You should also try to understand why the reverse implication is not derivable in the last example.
    -/

    variables (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
        (assume h : ∀ x, p x ∧ q x,
        and.intro
            (assume x : α, show p x, from (h x).left)
            (assume x : α, show q x, from (h x).right))
        (assume h : (∀ x, p x) ∧ (∀ x, q x),
        assume x : α,
        and.intro (h.left x) (h.right x))

    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
        assume h₀ : ∀ x, p x → q x,
        assume h₁ : (∀ x, p x),
        assume x : α,
        have hpx : p x, from h₁ x,
        show q x, from h₀ x hpx

    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
        assume h₀ : (∀ x, p x) ∨ (∀ x, q x),
        assume x : α,
        or.elim h₀
            (assume h₁ : (∀ x, p x), or.intro_left (q x) (h₁ x))
            (assume h₁ : (∀ x, q x), or.intro_right (p x) (h₁ x))

end one

namespace two
    /-
    It is often possible to bring a component of a formula outside a universal quantifier, 
    when it does not depend on the quantified variable. 
    Try proving these (one direction of the second of these requires classical logic):
    -/
    open classical

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    example : α → ((∀ x : α, r) ↔ r) :=
        assume x : α,
        iff.intro
            (assume h : (∀ x : α, r), h x)
            (assume hr : r, assume y : α, hr)

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
        iff.intro
            (assume h : (∀ x, p x ∨ r),
            by_cases
                (assume hr : r, or.intro_right (∀ x, p x) hr)
                (assume nr : ¬r, 
                have h₀ : (∀ x, p x), from 
                    (assume x : α,
                    have h₁ : (p x ∨ r), from h x,
                    or.resolve_right h₁ nr),
                or.intro_left r h₀))
            (assume h : (∀ x, p x) ∨ r,
            or.elim h
                (assume h₀ : ∀ x, p x, 
                assume x : α, or.intro_left r (h₀ x))
                (assume h₀ : r,
                assume x : α, or.intro_right (p x) h₀))

    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
        iff.intro
            (assume h : (∀ x, r → p x),
            assume hr : r,
            (assume x : α, h x hr))
            (assume h : (r → ∀ x, p x),
            assume x : α,
            assume hr : r,
            h hr x)

end two