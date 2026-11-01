/-
**The child's TCB limit word from the second TCB's words** (AArch64, rows hlim-a .. hlim-e under
`Hello.SegR.ChildPrem`'s `hlimT`/`hlimW`): with the clone's thread pointer `tls` the second TCB
`tcbOf lab q` and its words the runtime's (`Rt.PreChild.TcbArea`, at any memory side), the handed range the
runtime's second take `r1Of lab`, `HelloChildHlim.hlim_stack`'s five premises on `tls` hold (the twin of
`Rt.PreChild.preChild_hlim`).

- `tcb_hlim`: `tls + 16 ≤ 2 ^ 64`, the TCB off `r1Of lab`, the limit word `tls + 8` the runtime's, mapped
  for reading, every value runtime memory may hold there at most `r1Of lab`'s top less `176`.
- `hbd_of`: at a runtime layout whose second take `r1Of` is inside the stack pool, the stacks do not wrap.
- `childHlim_tcb`: `ChildPrem.hlimT` and `hlimW` at the clone's `stack`, from the clone's held list, the
  handed range `r1c = r1Of L.lab` inside the pool, and the TCB facts (`HelloChildHlim.hlim_stack` after
  `tcb_hlim`).
-/
import Spike.Lib.Rt.A64RtPreChild
import Spike.Lib.Rt.A64Layout
import Spike.Lib.A64HelloChildHlim

namespace Spike.Lib.HelloChildTcb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64.Flow.Ret0 (stacksA)
open Spike.Lib.A64.Rt (TcbGG tcbOf)
open Spike.Lib.A64.Rt.PreChild (r1Of TcbArea)

/-- **The five limit-word premises from `TcbArea`** at `tls = tcbOf lab q`, `r1 = r1Of lab`: the TCB's
first two words in the address space (`htls`) and off `r1` (`hout`), the stacks' area in the address space
(`hbd`). -/
theorem tcb_hlim {ms : MemSide isaLSE2} {lab : Label → Int64} {q : TcbGG} (hA : TcbArea ms lab q) {tls : Nat}
    (htq : tls = (tcbOf lab q).toNat) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8) :
    tls + 16 ≤ 2 ^ 64 ∧ (tls + 16 ≤ (r1Of lab).lo ∨ (r1Of lab).lo + (r1Of lab).size ≤ tls + 8) ∧
      ms.rt (tls + 8) ∧ ms.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false ∧
      ∀ v : Val, ms.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v →
        (v.setWidth 64).toNat + 176 ≤ (r1Of lab).lo + (r1Of lab).size := by
  subst htq
  have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
    show (stacksA lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz : (r1Of lab).size = 16384 := rfl
  have e8 : tcbOf lab q + 8#64 = BitVec.ofNat 64 ((tcbOf lab q).toNat + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h8 : (BitVec.ofNat 64 ((tcbOf lab q).toNat + 8)).toNat = (tcbOf lab q).toNat + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrt := hA.rt (tcbOf lab q + BitVec.ofNat 64 (8 * 1)) (by simp [Spike.Lib.A64.Rt.Ti.tiAddrs])
  have hmp := hA.mpR
  have hG := hA.lim
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from rfl, e8, h8] at hrt
  rw [e8] at hmp hG
  refine ⟨htls, by omega, hrt, hmp, fun v hv => ?_⟩
  have := hG v hv
  omega

/-- **The stacks do not wrap** at a runtime layout whose second take is inside the stack pool (the twin of
`WakeHClW.hbd_W` at any layout). -/
theorem hbd_of (L : Spike.Lib.A64.Rt.RuntimeLayout) (hsub : (r1Of L.lab).Sub L.Λ.stackPool) :
    (stacksA L.lab).toNat + 32768 < 2 ^ 64 := by
  have hs := L.stacks_sub
  have hf := L.pool_fit
  have hlabS : stacksA L.lab = L.stacksA := L.lab_stacks
  obtain ⟨-, h2⟩ := hsub
  obtain ⟨-, h4⟩ := hs
  simp only [r1Of, hlabS, BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  simp only at h4
  rw [hlabS]
  omega

open Spike.Lib.A64.Flow (tcbA DFrame)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.Child (wcJE Words)
open Scc.Sem.Kernel (KState)
open Spike.Lib.Handover (childAfter)

/-- **`ChildPrem.hlimT` and `hlimW` at the clone's `stack` from the second TCB's words**: the handed range
`r1c` the layout's second take inside the pool (row 5j-misc-r1), ending at `stack` and held first for `tid`
(`HelloSpawnR.PreRH`'s `top`, `held`), the thread pointer `tls` the second TCB with its words the runtime's
and its first two words in the address space and off `r1c` (row clone-tls-TcbArea). -/
theorem childHlim_tcb (L : Spike.Lib.A64.Rt.RuntimeLayout) {r1c r0 : Range} {stack tls : Nat} {x : KState}
    {tid : Nat} {t : Thread isaLSE2} {ms : MemSide isaLSE2} {q : TcbGG}
    (hsub : r1c.Sub L.Λ.stackPool) (hr1 : r1c = r1Of L.lab) (hst : r1c.lo + r1c.size = stack)
    (hheld : x.held = [(tid, r1c), (tid, r0)])
    (hA : TcbArea ms L.lab q) (htq : tls = (tcbOf L.lab q).toNat) (htls : (tcbOf L.lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf L.lab q).toNat + 16 ≤ (stacksA L.lab).toNat + 16384 ∨
      (stacksA L.lab).toNat + 32768 ≤ (tcbOf L.lab q).toNat + 8) :
    (∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter Scc.Sem.A64.abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 stack - (80 : Int64).toBitVec).toNat) ∧
    ∀ {c0 : Spike.Lib.Ctl} {w : Words} x29 ra σ c, wcJE c0 w x29 ra (BitVec.ofNat 64 tls) σ c →
      σ.regs.SP.toBitVec = BitVec.ofNat 64 stack - (80 : Int64).toBitVec →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, DFrame (childR stack (-272)) (childAfter Scc.Sem.A64.abi x tid t stack tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat := by
  subst hr1
  have hbd := hbd_of L hsub
  have hlo1 : (r1Of L.lab).lo = (stacksA L.lab).toNat + 16384 := by
    show (stacksA L.lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz : (r1Of L.lab).size = 16384 := rfl
  obtain ⟨ha, hb, hc, hd, he⟩ := tcb_hlim hA htq hbd htls hout
  exact HelloChildHlim.hlim_stack hst hheld (by omega) (by omega) ha hb hc hd he

end Spike.Lib.HelloChildTcb

/-- info: 'Spike.Lib.HelloChildTcb.tcb_hlim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildTcb.tcb_hlim

/-- info: 'Spike.Lib.HelloChildTcb.hbd_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildTcb.hbd_of

/-- info: 'Spike.Lib.HelloChildTcb.childHlim_tcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildTcb.childHlim_tcb
