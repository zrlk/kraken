import Spike.Lib.Src.NJLC
import Spike.Lib.Src.HeapMem

/-!
**Numbers in the buffers** (ISA-neutral). `xchgAt` binds the old element of
a lane buffer at the walk layout `.leaf none` (`opLit`), so `EnvLit` after it
needs the old word to be a number below `2^64`. The old word is the latest
message of the cell (`src_xchgAt_step`); `HeapLit sm L` says every message of
the source memory at a label in `L` holds such a number.

- (`Spike.Lib.Src.HeapMem`: `HeapLit`, `HasCell`, `cellNum`, `bufWords`, `print`'s
  memory premise `printMem_bufWords`;)
- `heapLit_allocBuf_elem2`: the buffer of a `newBuf` of an `elem2` type
  (zero words `[.num 0]`);
- `isNum_of_heapLit`, `latest_num`: the latest message of a cell at a label
  in `L` read as a word (`⟨m.val, m.view, j⟩`) is a number;
- `isNum_of_envLit_leaf`, `envLit_xchgAt`, `heapLit_xchgAt`: the stored word
  from a leaf, `EnvLit` and `HeapLit` after the exchange.

Not here: that each buffer variable is bound to a locative at a label in `L`
(an environment-side fact the walk keeps with `bufs`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV)
open Scc.Sem.MemRel (SLatest)

/-- **The words of an `elem2` buffer are numbers**: its zero words. -/
theorem allocBufVal_num {τ : Ty} (h : Scc.Lower.elem2 τ = true) (j : Nat) :
    ∃ v, Scc.Sem.allocBufVal (TermRun.zeroWords τ) j = .num v ∧ v < 2 ^ 64 := by
  cases τ <;> simp [Scc.Lower.elem2] at h <;> exact ⟨0, by simp [TermRun.zeroWords, Scc.Sem.allocBufVal, Nat.mod_one]⟩

/-- **`newBuf`'s zero words of an `elem2` type** (`tstep`'s choice). -/
theorem zero_elem2 {τ : Ty} (h : Scc.Lower.elem2 τ = true) :
    (if zeroableIn [] [] τ then TermRun.zeroWords τ else none) = TermRun.zeroWords τ := by
  cases τ <;> simp [Scc.Lower.elem2] at h <;> simp [zeroableIn]

/-- **`HeapLit` after the `newBuf` of an `elem2` type** at a fresh label. -/
theorem heapLit_allocBuf_elem2 {L : WeakMem.AllocLabel → Prop} {lbl : WeakMem.AllocLabel} {n : Nat}
    {τ : Ty} {s : TermRun.St} (h : HeapLit s.mem L) (hf : FreshIn s.mem lbl) (he : Scc.Lower.elem2 τ = true) :
    HeapLit (TermRun.allocBuf lbl n (if zeroableIn [] [] τ then TermRun.zeroWords τ else none) s).1.mem
      (fun l => L l ∨ l = lbl) := by
  rw [zero_elem2 he]; exact heapLit_allocBuf h hf (allocBufVal_num he)

/-! ## Reading a cell -/

/-- **The old word of an exchange is a number**: the latest message `j` of a
cell at a label in `L`, read as `xchgAt` binds it. -/
theorem isNum_of_heapLit {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {j : Nat} {m : WeakMem.Msg} (hm : sm[j]? = some m) (hl : L m.loc.label) :
    IsNum ⟨m.val, m.view, j⟩ :=
  h j m hm hl

/-- **A cell at a label in `L` has a latest message, a number.** -/
theorem latest_num {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {sa : WeakMem.Address} (hc : HasCell sm sa) (hl : L sa.label) :
    ∃ j m, SLatest sm sa j ∧ sm[j]? = some m ∧ IsNum ⟨m.val, m.view, j⟩ := by
  obtain ⟨j, m, n, hj, hm, hn, hlt⟩ := latest_num' h hc hl
  exact ⟨j, m, hj, hm, n, hn, hlt⟩

/-! ## The exchange -/

/-- **The stored word of an exchange is a number** when its atom is at a
`.leaf` of the walk. -/
theorem isNum_of_envLit_leaf {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvLit lits env)
    {v : At} {o : Option Nat} {t : Ty} {w : TermRun.Word} (hsc : InLits lits v)
    (hlit : ∀ n, v = .lit n → n < 2 ^ 64) (hL : Scc.Lower.litAt lits v = .leaf o)
    (he : TermRun.evalAt env v = some (t, [w])) : IsNum w := by
  have hn := (h.evalAt' hsc hlit he).2
  rw [hL] at hn
  exact hn 0 w rfl rfl

/-- **`EnvLit` after an exchange of an `elem2` element**: the old word, a
number, at `.leaf none`. -/
theorem envLit_xchgAt {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvLit lits env)
    {x : String} {u : Ty} {w : TermRun.Word} (hu : Scc.Lower.elem2 u = true) (hw : IsNum w) :
    EnvLit ((x, .leaf none) :: lits) ((x, u, [w]) :: env) := by
  refine h.cons ?_ (NumL.of_all fun w' hw' => by simp only [List.mem_singleton] at hw'; subst hw'; exact hw)
  cases u <;> simp [Scc.Lower.elem2] at hu <;> rfl

/-- **The memory after an exchange keeps `HeapLit`**: the stored word is a
number. -/
theorem heapLit_xchgAt {sm : WeakMem.Memory} {L : WeakMem.AllocLabel → Prop} (h : HeapLit sm L)
    {sa : WeakMem.Address} {wv : TermRun.Word} (hw : IsNum wv) (mv : WeakMem.Ts) :
    HeapLit (sm.push ⟨sa, wv.val, mv⟩) L :=
  heapLit_push h fun _ => hw

end Spike.Lib.LowerNode
