/-
**`byteOut_emit` with its side premises from whole-run facts**, on any ISA:
the consumer's byte step of `print`'s output (`Spike/Lib/ByteOut.lean`)
with `hpriv` from the thread's private keys (`PrivKeys`,
`Spike/Lib/DmemPriv.lean`) and `hnum` from the source's numbers at
`print`'s element loads (`SrcNumSP … PrintLd`, `Spike/Lib/Src/SrcNum2.lean`).

The byte `a` is byte `k` of a label `l` placed at `b` (`ByteOut`'s
witnesses); the source runs locally to `print`'s element load of word
`k / 8` of `l` (`printLd_loadC`), where `SrcNumSP` finds the latest message
a number. That message is in the source memory, so its word is inside `l`
(`MemRel.lbl_mem`): `k < 8 · lsize l`, and the byte is not private
(`PrivKeys.hpriv_of_range`).

- `byteOut_emit_ld`: `byteOut_emit_n` so.
-/
import Spike.Lib.ByteOutPriv
import Spike.Lib.Src.SrcNum2

namespace Spike.Lib.ByteOut

open CoreLang CoreTerm TermRun
open Kraken.Promising
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.DmemPriv
open Spike.Lib.LowerNode (SrcNumSP PrintLd printLd_loadC)
open Scc.Sem.MemRel (SLatest)

/-- **A byte of the output, both sides, from whole-run facts**:
`byteOut_emit_n` with `hpriv` from the thread's private keys (the entry
stack clear of the layout) and `hnum` from the source's numbers at
`print`'s element loads, at a reachable source configuration. -/
theorem byteOut_emit_ld {P : SrcParams} {p : Prog} {I : ISA} {K : Kernel.Abi I} {Λ : Layout} {Ent : Entry}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {t t' : Thread I} {tm : Memory} {A : Arch} {a rd : Nat} {bt : Fin 256} {c1 : Ctl} {Q : Ctl → Prop}
    {s : Cfg} {th : TTh} {tr : List Ev}
    (hP : UsesWc P p) (hnum : SrcNumSP P p PrintLd) (hbo : ByteOut p lbl t.st a c1 Q)
    (hinv : Inv1 Λ lbl lsize ts t tm s.mem) (hwf : Λ.WF) (hrb : Kernel.readByte K A t tm a rd = some (bt, t'))
    (hd : PrivKeys K Λ Ent t.st) (hE : Ent.clear Λ = true) (hre : (source P p).Reach tr s)
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace) :
    Inv1 Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] ∧
          th'.nalloc = th.nalloc := by
  have hn : ∀ (pw wn : Word) (l b m k : Nat), pw.val = .loc ⟨l, 0⟩ 0 → lbl l = some b → a = b + k →
      LocalRun p c1 (PrintSrc.loadC pw wn m k) →
      ∃ j msg n, SLatest s.mem ⟨l, k / 8⟩ j ∧ s.mem[j]? = some msg ∧ msg.val = .num n :=
    fun pw wn l _ m k hpw _ _ hr => hnum tr s th hre hi hp c1 ht.symm he.symm _ l (k / 8) hr (printLd_loadC hpw)
  have hpriv : ∀ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x] := by
    obtain ⟨pw, wn, l, b, m, k, hpw, hl, rfl, hrun, -⟩ := hbo
    obtain ⟨j, msg, -, ⟨⟨msg', hm', hloc⟩, -⟩, -, -⟩ := hn pw wn l b m k hpw hl rfl hrun
    obtain ⟨-, -, hlt⟩ := hinv.mem.lbl_mem msg' (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm'))
    rw [hloc] at hlt
    have hk : k < (lrange lsize l b).size := by
      have h8 : k / 8 < lsize l := hlt
      simp only [lrange]; omega
    exact hd.hpriv_of_range hwf hE (hinv.mem.lbl_range l b hl).2 hk
  exact byteOut_emit_n hP hbo hinv hwf hrb hpriv hi ht he hσ hst hp hx hn

end Spike.Lib.ByteOut
