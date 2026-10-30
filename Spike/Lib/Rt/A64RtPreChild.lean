/-
**Main's runtime facts at its `clone`** (AArch64, wake's spawn): the
instance of `Spike.Lib.WakePreA.ClonePre`'s parameter `X`, after the
second thread's setup (`scc_rt_thread_reserve`, `scc_rt_alloc_tcb` at the
header `q.h`, the TCB's id store, the second `scc_rt_thread_init`).

- `r1Of`: the second take's range `⟨stacks + 16384, 16384⟩`.
- `tidA`: the TCB's id word `tcb + 56`.
- `NthOk`: `scc_rt_nthreads` holds `n` in main's own map.
- `TcbArea`: the second TCB's words (header, id, `scc_rt_thread_init`'s six
  fields) the runtime's, mapped for a write, every value runtime memory may
  hold there allowed (`G`), and at the limit word `tcb + 8` only values at
  most `r1`'s base plus 4096.
- `PreChild`: `x3` the TCB, `NthOk 1` (the counter starts at `0` in `.bss`; the reserve returns `1`, the TCB id), `scc_rt_stack_next` at `32768` in
  the own map, `TcbArea`.
- `preChild_hlim`: the stub's limit premise (`childStub_hlim_stk`) from
  `TcbArea`.
-/
import Spike.Lib.Rt.A64RtChildPrem
import Spike.Lib.Rt.A64RtTcbG
import Spike.Lib.Rt.A64RtReserve
import Spike.Lib.Rt.A64RtTi

namespace Spike.Lib.A64.Rt.PreChild

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.Handover (handed childAfter)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (tcbA)
open Spike.Lib.A64.Flow.Ret0 (stacksA nextA)
open Spike.Lib.A64.Rt (TcbGG hdrA tcbOf)
open Spike.Lib.A64.Rt.Reserve (ntA)

/-- **The second take's range**: the 16 KiB after main's. -/
def r1Of (lab : Label → Int64) : Range := ⟨(stacksA lab + 16384#64).toNat, 16384⟩

/-- **The TCB's id word** (`Scc.IR.Tcb`'s `tid` at 56). -/
abbrev tidA (lab : Label → Int64) (q : TcbGG) : BitVec 64 := tcbOf lab q + 56#64

/-- **The thread counter** holds `n` in the own map at `s`. -/
def NthOk (own : Own) (lab : Label → Int64) (n : BitVec 64) (s : State) : Prop :=
  (⟨ntA lab, 8⟩, n.setWidth 128) ∈ own s

/-- **The second TCB's words**: its header, id and `scc_rt_thread_init`'s
six fields the runtime's (`rt`), mapped for a write (`mp`), the values the
second thread's setup writes allowed (`G`), and at the limit word only
values at most `r1`'s base plus 4096 (`lim`, the child's prologue check). -/
structure TcbArea (ms : MemSide isaLSE2) (lab : Label → Int64) (q : TcbGG) : Prop where
  rt : ∀ a ∈ hdrA lab q :: tidA lab q :: Ti.tiAddrs (tcbOf lab q), ms.rt a.toNat
  mp : ∀ a ∈ hdrA lab q :: tidA lab q :: Ti.tiAddrs (tcbOf lab q), ms.mp ⟨a, 8⟩ true
  mpR : ms.mp ⟨tcbOf lab q + 8#64, 8⟩ false
  hdrG : ms.G ⟨hdrA lab q, 8⟩ ((q.h ||| 1#64 <<< 36).setWidth 128)
  tidG : ms.G ⟨tidA lab q, 8⟩ ((1#64 : BitVec 64).setWidth 128)
  fldG : ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields (tcbOf lab q) (stacksA lab + 16384#64),
    ms.G ⟨tcbOf lab q + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128)
  lim : ∀ v : Val, ms.G ⟨tcbOf lab q + 8#64, 8⟩ v → (v.setWidth 64).toNat ≤ (r1Of lab).lo + 4096

/-- **Main's runtime facts at its `clone`** (`ClonePre`'s `X`): `x3` the
second TCB, the thread counter at 1 (from `0`, `.bss`) and `scc_rt_stack_next` at `32768` in
the own map, the TCB's words (`TcbArea`). -/
def PreChild (ms : MemSide isaLSE2) (own : Own) (lab : Label → Int64) (q : TcbGG) (s : State) : Prop :=
  (s.st.1.regs.getXReg .X3).toBitVec = tcbOf lab q ∧ NthOk own lab 1#64 s ∧
    (⟨nextA lab, 8⟩, (32768#64 : BitVec 64).setWidth 128) ∈ own s ∧ TcbArea ms lab q

/-- **The child stub's limit premise from `TcbArea`**: with `tls` the TCB,
`r1 = r1Of lab` not wrapping, and the limit word off `r1`. -/
theorem preChild_hlim {ms : MemSide isaLSE2} {lab : Label → Int64} {q : TcbGG} (hA : TcbArea ms lab q)
    {x : Scc.Sem.Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {lo : Int}
    (hh : handed x tid ((r1Of lab).lo + (r1Of lab).size) = some (tid, r1Of lab))
    (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) (hsz : -lo ≤ (r1Of lab).size)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8) :
    ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 (tcbOf lab q).toNat →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, Spike.Lib.A64.Flow.DFrame
          ({ base := BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter Scc.Sem.A64.abi x tid t ((r1Of lab).lo + (r1Of lab).size) (tcbOf lab q).toNat).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤
          (BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤
          (BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - (48 : Int64).toBitVec -
            (32 : Int64).toBitVec).toNat := by
  have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
    show (stacksA lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have e8 : tcbOf lab q + 8#64 = BitVec.ofNat 64 ((tcbOf lab q).toNat + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h8 : (BitVec.ofNat 64 ((tcbOf lab q).toNat + 8)).toNat = (tcbOf lab q).toNat + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrt := hA.rt (tcbOf lab q + BitVec.ofNat 64 (8 * 1)) (by simp [Ti.tiAddrs])
  have hmp := hA.mpR
  have hG := hA.lim
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from rfl, e8, h8] at hrt
  rw [e8] at hmp hG
  exact Spike.Lib.A64.Rt.childStub_hlim_stk (stk := (stacksA lab).toNat) (by rw [r1Of, ← hlo1]; rfl) hh hbd hsz
    htls hout hrt hmp fun v hv => by have := hG v hv; omega

end Spike.Lib.A64.Rt.PreChild
