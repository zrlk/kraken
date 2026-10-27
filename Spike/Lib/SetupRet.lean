/-
**The setup block's post, named** (`SetupPostS`): the `PostS` of
`scc_rt_main`'s setup call interface (`Spike.Lib.A64.Rt.SetupCallW`,
`Spike.Lib.X64.Rt.SetupCallW`) for any program, generic in the ISA's
register file and the reader of its result registers.

- `RetPlace`: where one source word of the setup block's result lives
  among the result registers: one register, or a locative's two (base and
  offset word, `Scc/LAYOUT.md` §4, as `Scc.Sem.WordPlace` has them);
  `RetPlace.width`, `retWidth`: the registers it takes (`retWidth` of the
  result type's layout is the setup word count `sw`);
- `RetPlace.Rep`: the word representation at a place (`ValRep` for one
  register, `LocRep` for a pair, as `Scc.Sem.WordPlaceRep`);
- `SetupRet`: the result words `ws` at the places `pl`, word by word;
- `SetupPostS`: the source at `ret a`, no word held, `a`'s words `SetupRet`
  of the registers: what `Spike.Lib.SrcCalls.setup_ret_src` reads off the
  source control (with the thread's stack and promises, which the control
  does not carry).

The readers: AArch64 `Rt.rdA64` (`x0` …, `Spike/Lib/Rt/A64SetupRet.lean`),
x86-64 `Rt.rdX64` (`%rax`, `%rdx`, …, `Spike/Lib/Rt/X64SetupRet.lean`);
`hello1Pl`: `hello1.w`'s layout.
-/
import Scc.Sem.Correct
import Spike.Lib.Seg

namespace Spike.Lib.SetupRet

open CoreLang CoreTerm
open Scc.Sem (ValRep LocRep)

/-- **Where a word of the setup block's result lives**: result register
`i`, or a locative's base in register `b` and its offset word in `o`. -/
inductive RetPlace where
  | one (i : Nat)
  | loc (b o : Nat)
  deriving DecidableEq, Repr

/-- The result registers a place takes. -/
def RetPlace.width : RetPlace → Nat
  | .one _ => 1
  | .loc _ _ => 2

/-- The result registers a layout takes: the setup word count. -/
def retWidth (pl : List RetPlace) : Nat := (pl.map RetPlace.width).sum

/-- **`hello1.w`'s `rodata` result layout**: the slice's locative in
registers 0 (base) and 1 (offset word), its length in 2, the count in 3. -/
def hello1Pl : List RetPlace := [.loc 0 1, .one 2, .one 3]

theorem hello1Pl_width : retWidth hello1Pl = 4 := rfl

section Rep

variable {ρ : Type} (lbl : WeakMem.AllocLabel → Option Nat) (rd : Nat → ρ → BitVec 64)

/-- **The word representation at a place** of the registers `r`: one
register holds a word `ValRep` relates, a pair a base and offset word
`LocRep` relates. -/
def RetPlace.Rep (r : ρ) : RetPlace → WeakMem.Val → Prop
  | .one i, x => ValRep lbl x (rd i r).toNat
  | .loc b o, x => LocRep lbl x (rd b r).toNat (rd o r).toNat

/-- **The result words `ws` at the places `pl`** of the registers `r`, word
by word. -/
def SetupRet : List RetPlace → List TermRun.Word → ρ → Prop
  | [], [], _ => True
  | q :: pl, w :: ws, r => RetPlace.Rep lbl rd r q w.val ∧ SetupRet pl ws r
  | _, _, _ => False

/-- **The setup block's post**: the source control at `ret a` with no word
held, `a`'s words at the places `pl` of the registers. -/
def SetupPostS (pl : List RetPlace) (c : Spike.Lib.Ctl) (r : ρ) : Prop :=
  c.hold = none ∧ ∃ (a : At) (t : Ty) (ws : List TermRun.Word), c.term = .ret a ∧
    TermRun.evalAt c.env a = some (t, ws) ∧ SetupRet lbl rd pl ws r

variable {lbl rd}

/-- As many result words as places. -/
theorem SetupRet.length : ∀ {pl : List RetPlace} {ws : List TermRun.Word} {r : ρ},
    SetupRet lbl rd pl ws r → ws.length = pl.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, h => congrArg (· + 1) (SetupRet.length h.2)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- `SetupRet` under another reader and register file agreeing with these
on every result register. -/
theorem SetupRet.of_rd {rd' : Nat → ρ → BitVec 64} {r r' : ρ} (he : ∀ i, rd' i r' = rd i r) :
    ∀ {pl : List RetPlace} {ws : List TermRun.Word}, SetupRet lbl rd pl ws r → SetupRet lbl rd' pl ws r'
  | [], [], h => h
  | q :: _, _ :: _, h => ⟨by cases q <;> simpa [RetPlace.Rep, he] using h.1, SetupRet.of_rd he h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- `SetupPostS` under another reader and register file agreeing with these
on every result register. -/
theorem SetupPostS.of_rd {rd' : Nat → ρ → BitVec 64} {pl : List RetPlace} {c : Spike.Lib.Ctl} {r r' : ρ}
    (he : ∀ i, rd' i r' = rd i r) (h : SetupPostS lbl rd pl c r) : SetupPostS lbl rd' pl c r' := by
  obtain ⟨hh, a, t, ws, ht, he', hs⟩ := h
  exact ⟨hh, a, t, ws, ht, he', hs.of_rd he⟩

end Rep

end Spike.Lib.SetupRet
