/-
**The packet's slice words at the spawned child's registers** (AArch64): at main's
`clone` (`ClonePreH`) the source's packet is the slice's three words `[b, m, n]` (`SpawnSrcH`), represented by
main's `x9`, `x11`, `x12` (`SlRep`: the buffer's locative at `x9`, its pair's second word `x10 = 0`, `m` at `x11`,
`n` at `x12`), which the child receives as its `w0`, `w2`, `w3` (`Child.clonePreH_child_at`'s words
`⟨x9, x10, x11, x12, x13, x14⟩`). These are the `ValRep` facts the placement of the worker's source at the child's
nodes asks for the slice (`hv0`, `hv1`, `hv2`; the cell's and main's id's are `ChildPrem.hv`, `hvu`).

Note the index: a locative is one represented word (its address), so the buffer `b` is at the child's `w0` (not
`w1`, which holds the pair's `0`); `m` and `n` are at `w2`, `w3`.

- `hv012_of_clone`: at `ClonePreH`, main's one thread `th` and source thread `th0`, the packet's words `[b, m, n]`
  of `SpawnSrcH`, and their `ValRep`s at `x9`, `x11`, `x12`.
- `hv012_of_clone_words`: the same, the three facts at `Child.clonePreH_child_at`'s `Words` (`BitVec.ofNat 64 sl0`
  …) for its `sl0`, `sl2`, `sl3`.
-/
import Spike.Lib.A64HelloClonePreH

namespace Spike.Lib.HelloHv012

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (ValRep)
open Scc.Sem.A64 (abi)
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.HelloPreA (ClonePreH)

/-- **The slice words' representations at main's registers at the clone** (module doc). -/
theorem hv012_of_clone {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (l : WeakMem.AllocLabel)
      (b m n : TermRun.Word), t.1.threads = #[th] ∧ s.ths = #[th0] ∧
      SpawnSrcH l [b, m, n] ⟨th0.term, th0.env, hd⟩ ∧
      ValRep lbl b.val (th.st.st.1.regs.getXReg .X9).toNat ∧ ValRep lbl m.val (th.st.st.1.regs.getXReg .X11).toNat ∧
      ValRep lbl n.val (th.st.st.1.regs.getXReg .X12).toNat := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, hth, hs, -, -, -, -, -, -, h9, -, h11, h12, -, -, -,
    -, -, -, -, -, -, -, -, hS, -, hR, -⟩ := h
  obtain ⟨b, m, n, rfl, hb, hm, hn⟩ := hR.valRep
  exact ⟨th, th0, hd, l, b, m, n, hth, hs, hS, h9 ▸ hb, h11 ▸ hm, h12 ▸ hn⟩

/-- **The slice words at the child's `Words`** (`Child.clonePreH_child_at`'s `⟨ofNat sl0, …, ofNat meW⟩`, with
`sl0 … sl3` main's `x9 … x12`): `hv0` at `w0`, `hv1` at `w2`, `hv2` at `w3`, given the words as numbers below
`2 ^ 64` (they are registers' values). -/
theorem hv012_of_clone_words {lbl : WeakMem.AllocLabel → Option Nat} {b m n : TermRun.Word} {sl0 sl2 sl3 : Nat}
    (hb : ValRep lbl b.val sl0) (hm : ValRep lbl m.val sl2) (hn : ValRep lbl n.val sl3)
    (h0 : sl0 < 2 ^ 64) (h2 : sl2 < 2 ^ 64) (h3 : sl3 < 2 ^ 64) :
    ValRep lbl b.val (BitVec.ofNat 64 sl0).toNat ∧ ValRep lbl m.val (BitVec.ofNat 64 sl2).toNat ∧
      ValRep lbl n.val (BitVec.ofNat 64 sl3).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h3]
  exact ⟨hb, hm, hn⟩

end Spike.Lib.HelloHv012

/-- info: 'Spike.Lib.HelloHv012.hv012_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHv012.hv012_of_clone

/-- info: 'Spike.Lib.HelloHv012.hv012_of_clone_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.HelloHv012.hv012_of_clone_words
