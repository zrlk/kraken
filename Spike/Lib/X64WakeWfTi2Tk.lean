/-
**The second take's counters at `h1`'s memory side** (x86-64; twin of
`Spike/Lib/A64WakeWfTi2Tk.lean`): the premise `htk` of `WakeTi2Hat.hti_W`
(`Rt.TakeOkA` of `scc_rt_stack_take` called from the second
`scc_rt_thread_init`, `k0 = 16384`) at `Ly := RuntimeLayout.ofPlaceWX hp i`
and `ms1 := WakeH1Inv.ms1W asm hp i E cT ls0 l b n []`.

The counters `lockA`, `freeNA`, `nextA` are runtime words (`words_mapped`),
in `.data` or `pinned` (so the runtime's at `ms1`, `Ti2Fld.rt_dp`), none of
`GOf2`'s pinned words (the first limit word by A8's `tcbSep`, `ctr_neW`; the
second by `hctr2`), unmapped under `F` (`hFr`). The take's nodes run on the
first stack (`hbase`: `%rsp` in the pool), where `ms1`'s owned words
`ownGXW` contain `ownG`, which is `own2b` at `ph2b` (`ownG_2b`): the lock `0`
and the next offset `16384` at phase `12` (`take2Tab`'s pins).

- `ctr_st`, `ctr_ld`: a counter's store and load facts.
- `htk2_W`: `hti_W`'s `htk`.
- `at_sp`, `inPc_of`, `addr_box`, `sp_of`, `mem_ownGXW`: private copies of
  the start chain's node-state facts.

Where this differs from AArch64: the pcs are the label plus a byte offset
(`StackTake.swpPc`'s `.spin14 + 11`, `freeNPc`'s `.locked15 + 4`,
`nextPc`'s `.bump + 56`), not `4 * k`; the frames are x86-64's (the
thread-init callee at `-72`, `-248`, `8`; the take at `-48`, `-200`, `8`; the
take's `%rsp` at `R.addr (-320)`, the first stack's top at `R.base + 64`, for
A64's `-80`/`-256`, `-208`, `-336` and `48`); `ms1`'s owned words are
`ownGXW` (`ownG` with the appended words), not `ownG`; the store/load facts
come from `Ret0.StOk`/`LdOk`'s four/three fields with the `mp` pair built
from `words_mapped`, as on AArch64; `ctr_ne` is `PlaceWX.ctr_neW`.

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeHatA
import Spike.Lib.X64WakeOwnGEq
import Spike.Lib.X64WakeOwnT2
import Spike.Lib.X64WakeTake2
import Spike.Lib.Rt.X64OwnA
import Spike.Lib.X64StartOfPlaceW
import Spike.Lib.X64SpAgree
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.X64WakeWfTi2Fld

namespace Spike.Lib.X64.WakePh.Ti2Tk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open Spike.Lib.X64.Flow.WakeWc (t2 tiQ)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.Rt.PhOfTab (ph_of_factOk)
open Spike.Lib.X64WakeGOf2 (lim2A gOf2_ne)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.HeapLand (AllocLand)

/-- A node state's `%rsp` is its region's address at the node's `%rsp`
offset. -/
private theorem at_sp {L : RuntimeLayout} {ep : Int64} {R : Region} {F : MachineData → Prop}
    {n : Spike.Lib.X64.ND} {s : State} {c : Ctl} (h : Spike.Lib.X64.At L.exe ep R F n s c) :
    s.st.1.regs.rsp.toBitVec = R.addr n.o.sp ∧ s.st.2 = n.pc := by
  obtain ⟨-, -, -, hpc, σ, hA, -, -⟩ := h
  exact ⟨Spike.Lib.X64ConsumerA.rsp_of_abs hA, hpc⟩

/-- **A pc `lab l + k` lies between labels `l₁`, `l₂`**: decided on
`codeT` (`h`, no address in the text), the labels resolved (`hlab`). -/
private theorem inPc_of {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {l l₁ l₂ : Label} {k : Nat}
    (h : ((codeT lo wakeCells l).bind fun x => (codeT lo wakeCells l₁).bind fun x₁ =>
      (codeT lo wakeCells l₂).map fun x₂ => decide (x₁ ≤ x + k ∧ x + k < x₂ ∧ x₂ < 2 ^ 64)) = some true)
    {s : State} (hs : pcOf s = (L.lab l + Int64.ofNat k).toBitVec.toNat) : inPc L l₁ l₂ s := by
  rw [codeT_eq] at h
  cases e : codeLabel lo wakeCells l <;> cases e₁ : codeLabel lo wakeCells l₁ <;>
    cases e₂ : codeLabel lo wakeCells l₂ <;> simp only [e, e₁, e₂, Option.bind_none,
      Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq, decide_eq_true_eq] at h
  rename_i x x₁ x₂
  have hl : ∀ {l : Label} {y : Nat}, codeLabel lo wakeCells l = some y → y < 2 ^ 64 →
      (L.lab l).toBitVec.toNat = y := fun hy hy' => by
    rw [hlab _ _ hy]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy']
  unfold inPc
  rw [hs, pc_eq hlab e, hl e₁ (by omega), hl e₂ h.2.2, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h.1, h.2.1⟩

/-- A frame address `R.addr k` near `R`'s base, `R.base + 64` the first
stack's top: no wrap. -/
private theorem addr_box {L : RuntimeLayout} {R : Region} (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384)
    {k : Int} (h1 : -336 ≤ k) (h2 : k ≤ 0) : ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The take's nodes' `%rsp` on the first stack**: `R`'s `-72` callee's
`-48` callee at `-200` is `R.addr (-320)`, inside the pool (`hbase`). -/
private theorem sp_of {L : RuntimeLayout} {ep : Int64} {R : Region} {F : MachineData → Prop}
    {n : Spike.Lib.X64.ND} {s : State} {c : Ctl} (hb : R.base.toNat + 64 = L.stacksA.toNat + 16384)
    (h : Spike.Lib.X64.At L.exe ep ((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8) F n s c)
    (hn : n.o.sp = -200) : spPool L s ∧ s.st.2 = n.pc := by
  obtain ⟨hsp, hpc⟩ := at_sp h
  refine ⟨?_, hpc⟩
  have hB := addr_box hb (k := -320) (by decide) (by decide)
  have hs := L.stacks_sub
  have e : ((R.callee (-72) (-248) 8).callee (-48 - 0) (-200) 8).addr n.o.sp = R.addr (-320) := by
    rw [hn, Spike.Lib.Region.callee_addr, Spike.Lib.Region.callee_addr]; rfl
  unfold spPool
  rw [hsp, e]
  simp only [Scc.Sem.Range.Sub] at hs
  omega

/-- A word owned under `ownG` is owned under `ownGXW`. -/
private theorem mem_ownGXW {L : RuntimeLayout} {a : BitVec 64} {s : State} {x : Loc × Val}
    (h : x ∈ ownG L a s) : x ∈ ownGXW L a s :=
  List.mem_append_left _ (List.mem_append_left _ h)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)
  {F : MachineData → Prop} {ep : Int64}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

set_option hygiene false in
/-- The end of text. -/
local notation "eR" => WakeH1Inv.endR hp i

/-- **A store to a runtime word at `ms1`** off `GOf2`'s pinned words. -/
theorem ctr_st (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) {a v : BitVec 64} (ha : a ∈ (Ly).rtWords)
    (h1 : a ≠ (Ly).pinA + 16#64) (h2 : a ≠ lim2A Ly) : Ret0.StOk ms1 F a v :=
  ⟨Ti2Fld.rt_dp asm hp i E cT ls0 l b n hstat hland (by simpa using ((Ly).words_mapped _ ha).2.2 0 (by decide)),
    ⟨((Ly).words_mapped _ ha).1, fun _ j hj =>
      (((Ly).words_mapped _ ha).2.2 j (by simpa [Scc.Sem.Kernel.locBytes] using hj)).elim (.inl ·)
        (fun h => .inr (.inr h))⟩,
    .inr (gOf2_ne h1 h2 _), fun m hm => hFr m hm _ ha⟩

/-- **A load of a runtime word at `ms1`.** -/
theorem ctr_ld (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) {a : BitVec 64} (ha : a ∈ (Ly).rtWords) :
    Ret0.LdOk ms1 F a :=
  ⟨Ti2Fld.rt_dp asm hp i E cT ls0 l b n hstat hland (by simpa using ((Ly).words_mapped _ ha).2.2 0 (by decide)),
    ⟨((Ly).words_mapped _ ha).2.1, fun h => nomatch h⟩, fun m hm => hFr m hm _ ha⟩

/-- **`hti_W`'s `htk`**: the second take's lock, free count and next offset
(`k0 = 16384`) at `ms1`, owned at their nodes' states on the first stack. -/
theorem htk2_W (hpg : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) {R : Region}
    (hbase : R.base.toNat + 64 = (Ly).stacksA.toNat + 16384)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2A Ly)
    (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) :
    ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-72) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
      Spike.Lib.X64.Rt.TakeOkA ms1 F (Ly).exe eR (R'.callee (-48 - 0) (-200) 8) F'
        (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g') := by
  intro c0 R' F' _ hR g g'
  subst hR
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hp)
  have hlk : (Ly).lockA ≠ (Ly).pinA + 16#64 := Spike.Lib.PlaceWX.ctr_neW hp i (by simp)
  have hnx : (Ly).nextA ≠ (Ly).pinA + 16#64 := Spike.Lib.PlaceWX.ctr_neW hp i (by simp)
  refine ⟨?_, ?_, ?_, ?_, fun b' s c h => ?_, fun b' s c h => ?_, fun b' s c h => ?_⟩
  · rw [(Ly).lab_lock]
    exact ctr_st asm hp i E cT ls0 l b n hstat hland hFr (Ly).lock_mem hlk (hctr2 _ (by simp))
  · rw [(Ly).lab_freeN]
    exact ctr_ld asm hp i E cT ls0 l b n hstat hland hFr (Ly).freeN_mem
  · rw [(Ly).lab_lock]
    exact ctr_st asm hp i E cT ls0 l b n hstat hland hFr (Ly).lock_mem hlk (hctr2 _ (by simp))
  · rw [(Ly).lab_next]
    exact ctr_st asm hp i E cT ls0 l b n hstat hland hFr (Ly).next_mem hnx (hctr2 _ (by simp))
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Ret0.StackTake.spinL + Int64.ofNat 11).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGXW (Ly) (ntA (Ly).lab) s
    apply mem_ownGXW
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), hq,
      ph_of_factOk hlab (take2_fact hΛ (f := .ph Spike.Lib.X64.Rt.Code.Take.spinL 11 12)
        (by simp [take2Tab, Spike.Lib.X64.Rt.takeTkRows])),
      (Ly).lab_lock]
    simp [own2b, ownV]
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Ret0.StackTake.lockedL + Int64.ofNat 4).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGXW (Ly) (ntA (Ly).lab) s
    apply mem_ownGXW
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), (Ly).lab_freeN]
    simp [own2b, ownV]
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Ret0.StackTake.bumpL + Int64.ofNat 56).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownGXW (Ly) (ntA (Ly).lab) s
    apply mem_ownGXW
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), hq,
      ph_of_factOk hlab (take2_fact hΛ (f := .ph Spike.Lib.X64.Rt.Code.Take.bumpL 56 12)
        (by simp [take2Tab, Spike.Lib.X64.Rt.takeTkRows])),
      (Ly).lab_next]
    simp [own2b, ownV]

end Place

end Spike.Lib.X64.WakePh.Ti2Tk


/-- info: 'Spike.Lib.X64.WakePh.Ti2Tk.htk2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Tk.htk2_W
