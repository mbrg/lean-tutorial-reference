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