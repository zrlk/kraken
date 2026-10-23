/-
**`ret0`'s `RuntimeLayout`** (`Spike/Lib/Rt/A64Layout.lean`), built from
the hand facts of `Spike/Lib/A64Ret0Mem.lean` and `Spike/Lib/A64Ret0I.lean`:
the oracle instance of the record, and the check that the record's
generic facts are the hand ones on `ret0`.

- **`ret0L`**: every field from an existing hand lemma (`ret0_pinA` …,
  `ret0Words_entry` …, `pool_fit`, `pool_below`, `rS0_sub`); the only new
  decisions are on literals (the word list, the first stack's alignment).
  So each side condition of the record is satisfiable at `ret0`.
- **Oracle checks**: the record's words are `ret0Words` (`ret0L_words`),
  its frame condition is `ret0F` (`ret0L_F`); the generic `start_segW`
  premises give the hand ones at the hand's types (`ret0L_tcbOk`,
  `ret0L_takeOk`, `ret0L_hfld`, `ret0L_limOk`, `ret0L_arith`), and the
  generic frame lemmas give `ret0F_stable` and `ret0F_takeMem`.
-/
import Spike.Lib.Rt.A64Layout
import Spike.Lib.A64Ret0I

namespace Spike.Lib.A64.Rt.Ret0L

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (pinA pnA stacksA nextA lockA freeNA limA StOk LdOk LimOk OwnAt TcbOk TakeOk
  takeMem)
open Spike.Lib.A64.Flow.Ret0.Mem (labOf ret0Exe ret0End ret0Words ret0F msR ret0_pinA ret0_pnA ret0_stacksA
  ret0_nextA ret0_lockA ret0_freeNA ret0_lays ret0Words_entry ret0Words_pool ret0Words_mapped tcb0 top0)
open Spike.Lib.A64.Flow.Ret0.Inst (ret0Words_small pool_fit pool_below)
open Spike.Lib.A64Consumer (msOf Own Lbl Lsize)
open SccCode (ret0Λ ret0Prog)

/-- **`ret0`'s runtime layout.** -/
def ret0L : RuntimeLayout where
  exe := ret0Exe
  prog := ret0Prog
  Λ := ret0Λ
  lays := ret0_lays
  valid := inferInstance
  pinA := 134217728#64
  pnA := 6291472#64
  stacksA := 268435456#64
  nextA := 6291488#64
  lockA := 6291496#64
  freeNA := 6291504#64
  lab_pin := ret0_pinA
  lab_pn := ret0_pnA
  lab_stacks := ret0_stacksA
  lab_next := ret0_nextA
  lab_lock := ret0_lockA
  lab_freeN := ret0_freeNA
  words_small a ha := ret0Words_small a (by rwa [show rtWordsOf _ _ _ _ _ = ret0Words by decide] at ha)
  words_pool a ha := ret0Words_pool a (by rwa [show rtWordsOf _ _ _ _ _ = ret0Words by decide] at ha)
  words_mapped a ha := ret0Words_mapped (by rwa [show rtWordsOf _ _ _ _ _ = ret0Words by decide] at ha)
  pool_fit := pool_fit
  stacks_al := by decide
  stacks_sub := by
    have h := Spike.Lib.A64.Flow.Ret0.Inst.rS0_sub
    rwa [Spike.Lib.A64.Flow.Ret0.Inst.rS0, Spike.Lib.A64.Flow.Ret0.Inst.labT_stacksA, BitVec.add_zero] at h

/-! ## Oracle checks: the record's facts are the hand ones on `ret0` -/

theorem ret0L_words : ret0L.rtWords = ret0Words := by decide

theorem ret0L_F : rtF ret0L = ret0F := by
  funext m; unfold rtF ret0F; rw [ret0L_words]

theorem ret0L_end : ret0L.endPc = ret0End := rfl

theorem ret0L_ok : Scc.Sem.Entry.linux.Ok ret0L.Λ := by decide

theorem ret0L_entryR : entryR Scc.Sem.Entry.linux = Spike.Lib.A64.Flow.Ret0.Inst.entryR := rfl

theorem ret0L_free {lsize : Lsize} : RtFree ret0L ret0Λ.static lsize := rtFree_none _ fun _ => rfl

example : FStable Spike.Lib.A64.Flow.Ret0.Inst.entryR ret0F := ret0L_F ▸ rtF_stable ret0L ret0L_ok

example {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) {pm : _root_.Mem 64} {m : MachineData}
    (h : ret0F m) : ret0F (takeMem pm rS m) := by
  rw [← ret0L_F] at h ⊢; exact rtF_takeMem ret0L hsub h

/-- **The arithmetic premises** (`ret0_h16`, `ret0_hok`, `ret0_hfit`,
`ret0_hout`) from the record. -/
theorem ret0L_arith : top0.toNat % 16 = 0 ∧ (swR top0 (-80) 0).OK ∧
    (limA (UInt64.ofBitVec tcb0)).toNat + 8 ≤ 2 ^ 64 ∧
    (((limA (UInt64.ofBitVec tcb0)).toNat : Int) + 8 ≤ top0.toNat + -80 ∨
      (top0.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb0)).toNat) := by
  have hp : pinA (labOf ret0Exe) = ret0L.pinA := ret0_pinA
  have hs : stacksA (labOf ret0Exe) = ret0L.stacksA := ret0_stacksA
  simp only [tcb0, top0, hp, hs]
  exact ⟨rt_h16 ret0L, rt_hok ret0L, rt_hfit ret0L, rt_hout ret0L⟩

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {lsize : Lsize}

/-- `ret0_tcbOk` from the record. -/
theorem ret0L_tcbOk
    (hG : G ⟨pnA (labOf ret0Exe), 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hown : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (Ret0.AllocTcb.rmwPc (labOf ret0Exe))
      (pnA (labOf ret0Exe)) 0#64) :
    TcbOk (msR μ rd G own lsize) ret0F ret0Exe ret0End 0#64 := by
  rw [ret0_pnA] at hG hown
  have h := rt_tcbOk (L := ret0L) (μ := μ) (rd := rd) (G := G) (own := own) (lsize := lsize)
    (ret0L_free (lsize := lsize)) hG hown
  rwa [ret0L_F] at h

/-- `ret0_takeOk` from the record. -/
theorem ret0L_takeOk
    (hG1 : G ⟨lockA (labOf ret0Exe), 8⟩ ((1#64).setWidth 128))
    (hG0 : G ⟨lockA (labOf ret0Exe), 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨nextA (labOf ret0Exe), 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (Ret0.StackTake.swpPc (labOf ret0Exe)) (lockA (labOf ret0Exe))
      0#64)
    (hownF : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (Ret0.StackTake.freeNPc (labOf ret0Exe))
      (freeNA (labOf ret0Exe)) 0#64)
    (hownN : OwnAt (msR μ rd G own lsize) ret0Exe ret0End (Ret0.StackTake.nextPc (labOf ret0Exe))
      (nextA (labOf ret0Exe))
      0#64) :
    TakeOk (msR μ rd G own lsize) ret0F ret0Exe ret0End 0#64 := by
  rw [ret0_lockA] at hG1 hG0 hownL
  rw [ret0_nextA] at hGn hownN
  rw [ret0_freeNA] at hownF
  have h := rt_takeOk (L := ret0L) (lsize := lsize) (ret0L_free (lsize := lsize)) hG1 hG0 hGn hownL hownF hownN
  rwa [ret0L_F] at h

/-- `ret0_hfld` from the record. -/
theorem ret0L_hfld
    (hG : ∀ e ∈ Ret0.ThreadInit.fields tcb0 (stacksA (labOf ret0Exe) + 0#64),
      G ⟨tcb0 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128)) :
    ∀ e ∈ Ret0.ThreadInit.fields tcb0 (stacksA (labOf ret0Exe) + 0#64),
      StOk (msR μ rd G own lsize) ret0F ret0Exe ret0End (tcb0 + BitVec.ofNat 64 e.1) e.2 := by
  have hp : pinA (labOf ret0Exe) = ret0L.pinA := ret0_pinA
  have hs : stacksA (labOf ret0Exe) = ret0L.stacksA := ret0_stacksA
  simp only [tcb0, hp, hs] at hG ⊢
  have h := rt_hfld (L := ret0L) (μ := μ) (rd := rd) (own := own) (lsize := lsize) (ret0L_free (lsize := lsize)) hG
  rwa [ret0L_F] at h

/-- `ret0_limOk` from the record. -/
theorem ret0L_limOk {Z : BitVec 64}
    (hroom : ∀ v : Val, G ⟨limA (UInt64.ofBitVec tcb0), 8⟩ v → (v.setWidth 64).toNat ≤ Z.toNat) :
    LimOk (msR μ rd G own lsize) ret0F ret0Exe ret0End (limA (UInt64.ofBitVec tcb0)) Z := by
  have hp : pinA (labOf ret0Exe) = ret0L.pinA := ret0_pinA
  simp only [tcb0, hp] at hroom ⊢
  have h := rt_limOk (L := ret0L) (μ := μ) (rd := rd) (own := own) (lsize := lsize) (ret0L_free (lsize := lsize)) hroom
  rwa [ret0L_F] at h

end Spike.Lib.A64.Rt.Ret0L
