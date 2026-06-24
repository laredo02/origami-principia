import Mathlib.Tactic
import Mathlib.Logic.ExistsUnique

set_option linter.style.header false
set_option linter.style.longLine false

/-!
  Attempt at formalizing origami in Lean. The goal is two prove that with origami you can:
    - Solve all quadratic, cubic and quartic equations with rational coefficients.
    - Trisect an arbitrary angle.
    - Construct cube roots, including the doubling of a cube.
    - Construct a regular N-gon for N = 2ⁱ 3ʲ (2ᵏ 3ˡ + 1), when the last parentheses is a prime (called a Pierpont Prime).
-/

variable (point line : Type*)

class HasLiesOn where
  lies_on : point → line → Prop

class Incidence extends HasLiesOn point line where
  I₁ : ∀ p₁ p₂, p₁ ≠ p₂ → ∃! l, lies_on p₁ l ∧ lies_on p₂ l
  I₂ : ∀ l, ∃ p₁ p₂, p₁ ≠ p₂ ∧ lies_on p₁ l ∧ lies_on p₂ l
  I₃ : ∃ p₁ p₂ p₃, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
    ∀ l, ¬ (lies_on p₁ l ∧ lies_on p₂ l ∧ lies_on p₃ l)

class HasOrtho where
  ortho : line → line → Prop

export HasOrtho (ortho)

class Orthogonality extends Incidence point line, HasOrtho line where
  symm := ∀ l₁ l₂, ortho l₁ l₂ ↔ ortho l₂ l₁
  P₁ : ∀ p l₁, ∃! l₂, ortho l₁ l₂ ∧ lies_on p l₂
  P₂ : ∀ l₁ l₂, ortho l₁ l₂ → ∃ p, lies_on p l₁ ∧ lies_on p l₂

class HasFolds extends Orthogonality point line where
  fold : line → point → point
  involutory : ∀ l, fold l ∘ fold l = id
  fixed : ∀ (p : point) (l : line), lies_on p l ↔ fold l p = p
  orthogonal_fixed : ∀ l₁ l₂, ortho l₁ l₂ ↔ ∀ p : point, lies_on p l₂ → lies_on (fold l₁ p) l₂

class origami extends HasFolds point line where
  O₁ (p₁ p₂ : point) : p₁ ≠ p₂ → ∃! l : line, lies_on p₁ l ∧ lies_on p₂ l ∧ fold l p₁ = p₁ ∧ fold l p₂ = p₂
  O₂ (p₁ p₂ : point) : ∃! l : line, fold l p₁ = p₂
  O₃ (l₁ l₂ : line) : ∃ l : line, ∀ p, lies_on p l₁ ↔ lies_on (fold l p) l₂
  O₄ (p₁ : point) (l₁ : line) : ∃! l₂, ortho l₁ l₂ ∧ lies_on p₁ l₂
  O₅ (p₁ p₂ : point) (l₁ : line) : ∃ l₂, lies_on (fold l₂ p₁) l₁ ∧ lies_on p₂ l₂
  O₆ (p₁ p₂ : point) (l₁ l₂ : line) : ∃ l, lies_on (fold l p₁) l₁ ∧ lies_on (fold l p₂) l₂
  O₇ (p₁ : point) (l₁ l₂ : line) : ∃ l, lies_on (fold l p₁) l₁ ∧ ortho l l₂

class origami' (lies_on : point → line → Prop) (ortho : line → line → Prop)
    (fold : line → point → point) where
  O₁ (p₁ p₂ : point) : p₁ ≠ p₂ → ∃! l : line, lies_on p₁ l ∧ lies_on p₂ l ∧ fold l p₁ = p₁ ∧ fold l p₂ = p₂
  O₂ (p₁ p₂ : point) : ∃! l : line, fold l p₁ = p₂
  O₃ (l₁ l₂ : line) : ∃ l : line, ∀ p, lies_on p l₁ ↔ lies_on (fold l p) l₂
  O₄ (p₁ : point) (l₁ : line) : ∃! l₂, ortho l₁ l₂ ∧ lies_on p₁ l₂
  O₅ (p₁ p₂ : point) (l₁ : line) : ∃ l₂, lies_on (fold l₂ p₁) l₁ ∧ lies_on p₂ l₂
  O₆ (p₁ p₂ : point) (l₁ l₂ : line) : ∃ l, lies_on (fold l p₁) l₁ ∧ lies_on (fold l p₂) l₂
  O₇ (p₁ : point) (l₁ l₂ : line) : ∃ l, lies_on (fold l p₁) l₁ ∧ ortho l l₂

instance [h : HasFolds point line] : origami point line where
  O₁ p₁ p₂ h_ne := by
    obtain ⟨l, ⟨hl₁, hl₂⟩, l_unique⟩ := h.I₁ p₁ p₂ h_ne
    exact ⟨l, ⟨hl₁, hl₂, (HasFolds.fixed p₁ l).mp hl₁, (HasFolds.fixed p₂ l).mp hl₂⟩, fun m hm => l_unique m ⟨hm.left, hm.right.left⟩⟩
  O₂ p₁ p₂ := sorry
  O₃ l₁ l₂ := sorry
  O₄ := h.P₁
  O₅ p₁ p₂ l₁ := sorry
  O₆ p₁ p₂ l₁ l₂ := sorry
  O₇ p₁ l₁ l₂ := sorry
