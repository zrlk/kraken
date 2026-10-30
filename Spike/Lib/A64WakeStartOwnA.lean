/-
**The start chain's owned words at wake.w's global map** (AArch64): `Rt.TcbOkA`'s and `Rt.TakeOkA`'s `own` fields (the word an
`ldadd`/`swp`/`ldr` reads, owned at the node's states) at a memory side
whose owned words are `ownG` (`hown`), when the callee's frame lies off the
stack pool (`spPool`'s negation at the node's `sp`). There `ownG` is `ownW`
at the pc's phase (`ownG_W`), and `phW`'s pins give the values.

- `tcbOkA_ownG`: `scc_rt_alloc_tcb`'s counter add at `n0 = 0` (`phW = 13`
  at the `ldadd`: the counter `0`).
- `takeOkA_ownG`: `scc_rt_stack_take`'s lock `swp` (`phW = 12`: `0`), free
  count load (always `0`) and next offset add (`phW = 12`: `0`) at `k0 = 0`.
-/
import Spike.Lib.A64WakeOwnGEq
import Spike.Lib.A64WakeStart
import Spike.Lib.Rt.A64OwnA

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout TcbOkA TakeOkA)
open Spike.Lib.A64.Flow.Ret0 (pnA lockA freeNA nextA StOk LdOk)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {ms : Spike.Lib.MemSide isaLSE2} {F0 F : MachineData → Prop}
  {R : Region}

/-- A node state's `sp` is its region's address at the node's `sp` offset. -/
private theorem at_sp {n : Spike.Lib.A64.Flow.ND} {s : State} {c : Ctl}
    (h : Spike.Lib.A64.Flow.At L.exe L.endPc R F n s c) :
    s.st.1.regs.SP.toBitVec = R.addr n.o.sp ∧ s.st.2 = n.pc := by
  obtain ⟨-, -, -, hpc, σ, hA, -, -⟩ := h
  exact ⟨by rw [hA.regs]; exact hA.so.sp, hpc⟩

/-- **A pc `lab l + 4 k` lies between labels `l₁`, `l₂`**: decided on
`codeT` (`h`, no address in the text), the labels resolved (`hlab`). -/
private theorem inPc_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {l l₁ l₂ : Label} {k : Nat}
    (h : ((codeT lo wakeProg l).bind fun x => (codeT lo wakeProg l₁).bind fun x₁ =>
      (codeT lo wakeProg l₂).map fun x₂ => decide (x₁ ≤ x + 4 * k ∧ x + 4 * k < x₂ ∧ x₂ < 2 ^ 64)) = some true)
    {s : State} (hs : pcOf s = (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat) : inPc L l₁ l₂ s := by
  rw [codeT_eq] at h
  cases e : codeOf lo wakeProg l <;> cases e₁ : codeOf lo wakeProg l₁ <;>
    cases e₂ : codeOf lo wakeProg l₂ <;> simp only [e, e₁, e₂, Option.bind_none,
      Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, decide_eq_true_eq] at h
  rename_i x x₁ x₂
  have hl : ∀ {l : Label} {y : Nat}, codeOf lo wakeProg l = some y → y < 2 ^ 64 →
      (L.lab l).toBitVec.toNat = y := fun hy hy' => by
    rw [hlab _ _ hy]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy']
  unfold inPc
  rw [hs, pc_eq hlab e, hl e₁ (by omega), hl e₂ h.2.2, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h.1, h.2.1⟩

/-- **`ownG` is `ownW` at a runtime pc off the pool**: in
`scc_rt_alloc_tcb` or `scc_rt_thread_init` .. `scc_rt_stack_release`, `sp`
off the stack pool. -/
private theorem ownG_off (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hin : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨
      inPc L "scc_rt_thread_init" "scc_rt_stack_release" s)
    (hoff : ¬ (L.Λ.stackPool.lo < s.st.1.regs.SP.toBitVec.toNat ∧
      s.st.1.regs.SP.toBitVec.toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    ownG L a s = ownW L a (phW (pcOf s)) :=
  ownG_W hlab (Or.inl ⟨hin, hoff⟩)

/-- **`scc_rt_alloc_tcb`'s counter at `n0 = 0`, owned at the `ldadd`
node's states** under `ownG`, its frame (`R`'s `-192`) off the pool. -/
theorem tcbOkA_ownG (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hown : ∀ s, ms.own s = ownG L a s)
    {g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hnext : StOk ms F0 L.exe L.endPc (pnA L.lab) (0#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-192)).toNat ∧
      (R.addr (-192)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TcbOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  refine ⟨hnext, fun s c h => ?_⟩
  obtain ⟨hsp, hpc⟩ := at_sp h
  have hp : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.AllocTcb.lenL + Int64.ofNat (4 * 37)).toBitVec.toNat := by
    show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
  have e : ownG L a s = ownW L a (phW (pcOf s)) :=
    ownG_off hlab (.inl (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
  rw [hown, e, hp,
    ph_pinW hΛ hlab (l := Spike.Lib.A64.Flow.Ret0.AllocTcb.lenL) (k := 37) (v := 13) (by decide)]
  rw [show pnA L.lab = L.pnA from L.lab_pn]
  simp [ownW, Spike.Lib.A64.PhRec.ownOf]

/-- **`scc_rt_stack_take`'s three own-word accesses at `k0 = 0`, owned at
their nodes' states** under `ownG`, its frame (`R`'s `-208`) off the pool. -/
theorem takeOkA_ownG (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hown : ∀ s, ms.own s = ownG L a s)
    {g : Spike.Lib.A64.Flow.Ret0.StackTake.G} {c0 : Ctl}
    (hlock1 : StOk ms F0 L.exe L.endPc (lockA L.lab) 1#64) (hfreeN : LdOk ms F0 L.exe L.endPc (freeNA L.lab))
    (hlock0 : StOk ms F0 L.exe L.endPc (lockA L.lab) 0#64)
    (hnext : StOk ms F0 L.exe L.endPc (nextA L.lab) (0#64 + Spike.Lib.A64.Flow.Ret0.StackTake.size0))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-208)).toNat ∧
      (R.addr (-208)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TakeOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  refine ⟨hlock1, hfreeN, hlock0, hnext, fun b s c h => ?_, fun b s c h => ?_, fun b s c h => ?_⟩
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.spinL + Int64.ofNat (4 * 2)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e, hp,
      ph_pinW hΛ hlab (l := Spike.Lib.A64.Flow.Ret0.StackTake.spinL) (k := 2) (v := 12) (by decide)]
    rw [show lockA L.lab = L.lockA from L.lab_lock]
    simp [ownW, Spike.Lib.A64.PhRec.ownOf]
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.lockedL + Int64.ofNat (4 * 1)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e]
    rw [show freeNA L.lab = L.freeNA from L.lab_freeN]
    simp [ownW, Spike.Lib.A64.PhRec.ownOf]
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.bumpL + Int64.ofNat (4 * 11)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e, hp,
      ph_pinW hΛ hlab (l := Spike.Lib.A64.Flow.Ret0.StackTake.bumpL) (k := 11) (v := 12) (by decide)]
    rw [show nextA L.lab = L.nextA from L.lab_next]
    simp [ownW, Spike.Lib.A64.PhRec.ownOf]

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.tcbOkA_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.tcbOkA_ownG

/-- info: 'Spike.Lib.A64.WakePh.takeOkA_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.takeOkA_ownG
