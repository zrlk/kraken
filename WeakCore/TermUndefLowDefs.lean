import WeakCore.TermPiece
import WeakCore.TermCut
import WeakCore.TermCert

/-!
# TermUndefLowDefs: the `SysInvN` clause `UndefLowG`

At a single-word unit of a cell (a `.one` unit of a solid piece), no `undef` message lies above a
defined one: once an address holds a defined value, every later message there is defined.
-/

namespace TermUndefLow
open CoreLang CoreTerm TermRun TermStep TermCut
open WeakMem (Msg Memory Ts AllocLabel)

/-- Offset `o` is a single-word unit of a solid piece of `T` (the form `TermFreeQW`'s `hUL` asks). -/
def OnePc (T : Ty) (o : Nat) : Prop :=
  ∃ b U us i, TermPiece.Piece T b U ∧ accs U = some us ∧ b ≤ o ∧ InAcc us i (o - b) ∧
    ∀ o2, InAcc us i o2 → o2 = o - b

/-- Offset `o` starts a single-word unit of the laid-out cell type `T` (a value, or a slot of a
buffer of literal length). -/
def OneU (T : Ty) (o : Nat) : Prop :=
  (∃ L, accs T = some L ∧ TermFul.OneAt L o) ∨
  (∃ N e L j o', T = .array (.lit N) e ∧ accs e = some L ∧ j < N ∧ o = j * nWords L + o' ∧ TermFul.OneAt L o')

/-- **`UndefLowG`**: at a single-word unit of a cell, a defined message is never followed by an
`undef` one. -/
def UndefLowG (Eg : GEnv) (mem : Memory) : Prop :=
  ∀ l cl, Eg.sto l = some cl → ∀ o, OneU cl.ty o → ∀ (t1 t2 : Ts) (m1 m2 : Msg), t1 < t2 →
    mem[t1]? = some m1 → mem[t2]? = some m2 → m1.loc = ⟨l, o⟩ → m2.loc = ⟨l, o⟩ →
    m1.val ≠ .undef → m2.val ≠ .undef

/-- With no cell, `UndefLowG` is vacuous (the initial `E_g`). -/
theorem undefLow_empty {Eg : GEnv} {mem : Memory} (h : ∀ l, Eg.sto l = none) : UndefLowG Eg mem := by
  intro l cl hl
  rw [h l] at hl
  cases hl

/-- With no message, `UndefLowG` is vacuous (the initial memory, `InitOK`'s `c0.mem = #[]`). -/
theorem undefLow_nil {Eg : GEnv} {mem : Memory} (h : mem = #[]) : UndefLowG Eg mem := by
  intro l cl _ o _ t1 t2 m1 m2 _ h1 _ _ _ _
  subst h
  simp at h1

end TermUndefLow
