import Mathlib.Topology.DiscreteSubset

variable {α : Type*}

def WithTop.toBase [Zero α] (x : WithTop α) : α := WithTop.untop' 0 x

@[simp]
theorem WithTop.toBase_coe [Zero α] (n : α) : WithTop.toBase n = n := rfl

@[simp]
theorem WithTop.toBase_zero [Zero α] : WithTop.toBase (0 : α) = (0 : α) := rfl

@[simp]
theorem WithTop.toBase_top [Zero α] : WithTop.toBase ⊤ = 0 := rfl

@[simp]
theorem WithTop.toBase_eq_zero [Zero α] {n : WithTop α} : WithTop.toBase n = 0 ↔ n = (0 : α) ∨ n = ⊤ := WithTop.untop'_eq_self_iff

@[simp]
theorem coe_toBase_eq_self [Zero α] {n : WithTop α} : WithTop.toBase n = n ↔ n ≠ ⊤ := by
  sorry


/- @**Yaël Dillies** Before I say anything else: thanks for even looking at
this! As I wrote above, I am a newcomer. Trying to get my first non-trivial
theorem formalized, I saw substantial differences between the type `ℕ∞` (which
appears when I take the order of an analytic function) and `WithTop ℤ` (which
appears when I take the order of a meromorphic function).

The type `ℕ∞` has the convenient method `toNat`, which I use all the time.  If I
count right, the file `Mathlib.Data.ENat.Basic` has 15+ statements that allow me
to deal with `toNat`, and many of them are known to the simplifier. -/
