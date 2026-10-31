/-
**The start chain's owned words at wake.w's global map** (x86-64; twin of
`Spike/Lib/A64WakeStartOwnA.lean`): `Rt.TcbOkA`'s and `Rt.TakeOkA`'s `own`
fields (the word a `lock xadd`/`xchg`/`mov` reads, owned at the node's
states) at a memory side whose owned words are `ownG` (`hown`), when the
callee's frame lies off the stack pool (`spPool`'s negation at the node's
`%rsp`). There `ownG` is `ownW` at the pc's phase (`ownG_W`), and `phW`'s
values give the words.

- `tcbOkA_ownG`: `scc_rt_alloc_tcb`'s counter add at `n0 = 0` (`phW = 13`
  at the `lock xadd`, `.len` + 158: the counter `0`).
- `takeOkA_ownG`: `scc_rt_stack_take`'s lock `xchg` (`.spin14` + 11,
  `phW = 12`: `0`), free count load (`.locked15` + 4, always `0`) and next
  offset store (`.bump` + 56, `phW = 12`: `0`) at `k0 = 0`.

Where x86-64 differs from AArch64: the pcs are the label plus a byte offset
(`AllocTcb.rmwPc`, `StackTake.swpPc`/`freeNPc`/`nextPc`), not `4 * k`; the
frame's offsets are x86-64's (`AllocTcb.oI`'s `-184`, `StackTake.oI`'s
`-200`, for A64's `-192`, `-208`); the phase at a pc is decided at `phC` on the
resolved label (`phAt`) instead of through A64's `phPins` table (`ph_pinW`),
which has no x86-64 wake.w twin.
-/
import Spike.Lib.X64WakeOwnGEq
import Spike.Lib.Rt.X64OwnA
import Spike.Lib.X64SpAgree

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout TcbOkA TakeOkA)
open Spike.Lib.X64.Flow.Ret0 (pnA lockA freeNA nextA StOk LdOk)
open Spike.Lib (Region)

variable {L : RuntimeLayout} {a : BitVec 64} {ms : Spike.Lib.MemSide isa} {F0 F : MachineData → Prop}
  {R : Region}

/-- A node state's `%rsp` is its region's address at the node's `%rsp`
offset. -/
private theorem at_sp {n : Spike.Lib.X64.ND} {s : State} {c : Ctl}
    (h : Spike.Lib.X64.At L.exe L.endPc R F n s c) :
    s.st.1.regs.rsp.toBitVec = R.addr n.o.sp ∧ s.st.2 = n.pc := by
  obtain ⟨-, -, -, hpc, σ, hA, -, -⟩ := h
  exact ⟨Spike.Lib.X64ConsumerA.rsp_of_abs hA, hpc⟩

/-- A resolved label's value. -/
private theorem labN' (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (hy : codeLabel lo wakeCells l = some y) (hy' : y < 2 ^ 64) : (L.lab l).toBitVec.toNat = y := by
  rw [hlab _ _ hy]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy']

/-- **A pc `lab l + k` lies between labels `l₁`, `l₂`**: decided on
`codeT` (`h`, no address in the text), the labels resolved (`hlab`). -/
private theorem inPc_of (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {l l₁ l₂ : Label} {k : Nat}
    (h : ((codeT lo wakeCells l).bind fun x => (codeT lo wakeCells l₁).bind fun x₁ =>
      (codeT lo wakeCells l₂).map fun x₂ => decide (x₁ ≤ x + k ∧ x + k < x₂ ∧ x₂ < 2 ^ 64)) = some true)
    {s : State} (hs : pcOf s = (L.lab l + Int64.ofNat k).toBitVec.toNat) : inPc L l₁ l₂ s := by
  rw [codeT_eq] at h
  cases e : codeLabel lo wakeCells l <;> cases e₁ : codeLabel lo wakeCells l₁ <;>
    cases e₂ : codeLabel lo wakeCells l₂ <;> simp only [e, e₁, e₂, Option.bind_none,
      Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, decide_eq_true_eq] at h
  rename_i x x₁ x₂
  unfold inPc
  rw [hs, pc_eq hlab e, labN' hlab e₁ (by omega), labN' hlab e₂ h.2.2, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h.1, h.2.1⟩

/-- **`phW` at a pc `lab l + k`**: decided at `phC` on `codeT` (`h`), the
label resolved (`hlab`). -/
private theorem phAt (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {l : Label} {k v : Nat} (h : (codeT lo wakeCells l).map (fun x => phC ((x + k) % 2 ^ 64)) = some v) :
    phW (L.lab l + Int64.ofNat k).toBitVec.toNat = v := by
  rw [codeT_eq] at h
  cases e : codeLabel lo wakeCells l <;> simp only [e, Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h
  rw [pc_eq hlab e, phW_eq, h]

/-- **`ownG` is `ownW` at a runtime pc off the pool**: in
`scc_rt_alloc_tcb` or `scc_rt_thread_init` .. `scc_rt_stack_release`,
`%rsp` off the stack pool. -/
private theorem ownG_off (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {s : State}
    (hin : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨
      inPc L "scc_rt_thread_init" "scc_rt_stack_release" s)
    (hoff : ¬ (L.Λ.stackPool.lo < s.st.1.regs.rsp.toBitVec.toNat ∧
      s.st.1.regs.rsp.toBitVec.toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    ownG L a s = ownW L a (phW (pcOf s)) :=
  ownG_W hlab (Or.inl ⟨hin, hoff⟩)

/-- **`scc_rt_alloc_tcb`'s counter at `n0 = 0`, owned at the `lock xadd`
node's states** under `ownG`, its frame (`R`'s `-184`) off the pool. -/
theorem tcbOkA_ownG
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hown : ∀ s, ms.own s = ownG L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hnext : StOk ms F0 (pnA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.tcbLen))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-184)).toNat ∧
      (R.addr (-184)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TcbOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  refine ⟨hnext, fun s c h => ?_⟩
  obtain ⟨hsp, hpc⟩ := at_sp h
  have hp : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.AllocTcb.lenL + Int64.ofNat 158).toBitVec.toNat := by
    show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
  have e : ownG L a s = ownW L a (phW (pcOf s)) :=
    ownG_off hlab (.inl (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
  rw [hown, e, hp, phAt hlab (l := Spike.Lib.X64.Flow.Ret0.AllocTcb.lenL) (k := 158) (v := 13)
    (by decide +kernel)]
  rw [show pnA L.lab = L.pnA from L.lab_pn]
  simp [ownW, Spike.Lib.X64.PhRec.ownOf]

/-- **`scc_rt_stack_take`'s three own-word accesses at `k0 = 0`, owned at
their nodes' states** under `ownG`, its frame (`R`'s `-200`) off the
pool. -/
theorem takeOkA_ownG
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hown : ∀ s, ms.own s = ownG L a s)
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 : Ctl}
    (hlock1 : StOk ms F0 (lockA L.lab) 1#64) (hfreeN : LdOk ms F0 (freeNA L.lab))
    (hlock0 : StOk ms F0 (lockA L.lab) 0#64)
    (hnext : StOk ms F0 (nextA L.lab) (0#64 + Spike.Lib.X64.Flow.Ret0.StackTake.size0))
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-200)).toNat ∧
      (R.addr (-200)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)) :
    TakeOkA ms F0 L.exe L.endPc R F ⟨g, 0#64, c0⟩ := by
  refine ⟨hlock1, hfreeN, hlock0, hnext, fun b s c h => ?_, fun b s c h => ?_, fun b s c h => ?_⟩
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.spinL + Int64.ofNat 11).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e, hp, phAt hlab (l := Spike.Lib.X64.Flow.Ret0.StackTake.spinL) (k := 11) (v := 12)
      (by decide +kernel)]
    rw [show lockA L.lab = L.lockA from L.lab_lock]
    simp [ownW, Spike.Lib.X64.PhRec.ownOf]
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.lockedL + Int64.ofNat 4).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e]
    rw [show freeNA L.lab = L.freeNA from L.lab_freeN]
    simp [ownW, Spike.Lib.X64.PhRec.ownOf]
  · obtain ⟨hsp, hpc⟩ := at_sp h
    have hp : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.bumpL + Int64.ofNat 56).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    have e : ownG L a s = ownW L a (phW (pcOf s)) :=
      ownG_off hlab (.inr (inPc_of hlab (by decide +kernel) hp)) (by rw [hsp]; exact hoff)
    rw [hown, e, hp, phAt hlab (l := Spike.Lib.X64.Flow.Ret0.StackTake.bumpL) (k := 56) (v := 12)
      (by decide +kernel)]
    rw [show nextA L.lab = L.nextA from L.lab_next]
    simp [ownW, Spike.Lib.X64.PhRec.ownOf]

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcbOkA_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbOkA_ownG

/-- info: 'Spike.Lib.X64.WakePh.takeOkA_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.takeOkA_ownG
