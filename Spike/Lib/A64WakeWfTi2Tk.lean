/-
**The second take's counters at `h1`'s memory side** (AArch64): the
premise `htk` of `WakeTi2Hat.hti_W` (`Rt.TakeOkA` of `scc_rt_stack_take`
called from the second `scc_rt_thread_init`, `k0 = 16384`) at
`Ly := RuntimeLayout.ofPlaceW hp i` and `ms1 := WakeH1Inv.ms1W hp i E cT
ls0 l b n []`.

The counters `lockA`, `freeNA`, `nextA` are runtime words (`words_mapped`),
in `.data` or `pinned` (so the runtime's at `ms1`, `Ti2Fld.rt_dp`), none of
`GOf2`'s pinned words (the first limit word by A8's `tcbSep`, the second by
`hctr2`), unmapped under `F` (`hFr`). The take's nodes run on the first
stack (`hbase`: `sp` in the pool), where `ms1`'s owned words `ownG` are
`own2b` at `ph2b` (`ownG_2b`), the lock `0` and the next offset `16384` at
phase `12` (`take2Tab`'s pins).

- `ctr_ne`, `ctr_st`, `ctr_ld`: a counter's store and load facts.
- `htk2_W`: `hti_W`'s `htk`.
- `at_sp`, `inPc_of`, `addr_box`, `sp_of`: private copies of the start
  chain's node-state facts.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeWfTi2Fld
import Spike.Lib.A64WakeOwnGEq
import Spike.Lib.A64WakeTake2
import Spike.Lib.Rt.A64OwnA
import Spike.Lib.WakeFinalCAO

namespace Spike.Lib.A64.WakePh.Ti2Tk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.WakeWc (t2 tiQ)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64.Rt.PhOfTab (ph_of_factOk)
open Spike.Lib.WakeGOf2 (lim2A gOf2_ne)
open Spike.Lib.HeapLand (AllocLand)

/-- A node state's `sp` is its region's address at the node's `sp` offset. -/
private theorem at_sp {L : RuntimeLayout} {ep : Int64} {R : Region} {F : MachineData → Prop} {n : ND} {s : State}
    {c : Ctl} (h : At L.exe ep R F n s c) : s.st.1.regs.SP.toBitVec = R.addr n.o.sp ∧ s.st.2 = n.pc := by
  obtain ⟨-, -, -, hpc, σ, hA, -, -⟩ := h
  exact ⟨by rw [hA.regs]; exact hA.so.sp, hpc⟩

/-- **A pc `lab l + 4 k` lies between labels `l₁`, `l₂`**: decided on
`codeT` (`h`, no address in the text), the labels resolved (`hlab`). -/
private theorem inPc_of {L : RuntimeLayout} (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
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

/-- A frame address `R.addr k` near `R`'s base, `R.base + 48` the first
stack's top: no wrap. -/
private theorem addr_box {L : RuntimeLayout} {R : Region} (hb : R.base.toNat + 48 = L.stacksA.toNat + 16384) {k : Int}
    (h1 : -336 ≤ k) (h2 : k ≤ 0) : ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have hB := R.base.isLt
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Spike.Lib.Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The take's nodes' `sp` on the first stack**: `R`'s `-80` callee's
`-48` callee at `-208` is `R.addr (-336)`, inside the pool (`hbase`). -/
private theorem sp_of {L : RuntimeLayout} {ep : Int64} {R : Region} {F : MachineData → Prop} {n : ND} {s : State}
    {c : Ctl} (hb : R.base.toNat + 48 = L.stacksA.toNat + 16384)
    (h : At L.exe ep ((R.callee (-80) (-256) 0).callee (-48) (-208) 0) F n s c) (hn : n.o.sp = -208) :
    spPool L s ∧ s.st.2 = n.pc := by
  obtain ⟨hsp, hpc⟩ := at_sp h
  refine ⟨?_, hpc⟩
  have hB := addr_box hb (k := -336) (by decide) (by decide)
  have hs := L.stacks_sub
  have e : ((R.callee (-80) (-256) 0).callee (-48) (-208) 0).addr n.o.sp = R.addr (-336) := by
    rw [hn, Spike.Lib.Region.callee_addr, Spike.Lib.Region.callee_addr]; rfl
  unfold spPool
  rw [hsp, e]
  simp only [Scc.Sem.Range.Sub] at hs
  omega

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)
  {F : MachineData → Prop} {ep : Int64}

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W hp i E cT ls0 l b n []

/-- **The counters are not the first limit word** (A8's `tcbSep`). -/
theorem ctr_ne {a : BitVec 64} (ha : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA]) :
    a ≠ (Ly).pinA + 16#64 := by
  rintro rfl
  exact Scc.Cert.Rt.A64.tcbSep_of_wordsOk
    (Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (Spike.Lib.PlaceW.rtWordsOk_link_of_placeW i hp)) 2 (by decide) ha

/-- **A store to a runtime word at `ms1`** off `GOf2`'s pinned words. -/
theorem ctr_st (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) {a v : BitVec 64} (ha : a ∈ (Ly).rtWords)
    (h1 : a ≠ (Ly).pinA + 16#64) (h2 : a ≠ lim2A Ly) : Ret0.StOk ms1 F (Ly).exe ep a v :=
  ⟨Ti2Fld.rt_dp hp i E cT ls0 l b n hstat hland (by simpa using ((Ly).words_mapped _ ha).2.2 0 (by decide)),
    ⟨((Ly).words_mapped _ ha).1, fun _ j hj =>
      (((Ly).words_mapped _ ha).2.2 j (by simpa [Scc.Sem.Kernel.locBytes] using hj)).elim (.inl ·)
        (fun h => .inr (.inr h))⟩,
    .inr (gOf2_ne h1 h2 _), fun m hm => hFr m hm _ ha⟩

/-- **A load of a runtime word at `ms1`.** -/
theorem ctr_ld (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) {a : BitVec 64} (ha : a ∈ (Ly).rtWords) :
    Ret0.LdOk ms1 F (Ly).exe ep a :=
  ⟨Ti2Fld.rt_dp hp i E cT ls0 l b n hstat hland (by simpa using ((Ly).words_mapped _ ha).2.2 0 (by decide)),
    ⟨((Ly).words_mapped _ ha).2.1, fun h => nomatch h⟩, fun m hm => hFr m hm _ ha⟩

/-- **`hti_W`'s `htk`**: the second take's lock, free count and next offset
(`k0 = 16384`) at `ms1`, owned at their nodes' states on the first stack. -/
theorem htk2_W (hpg : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = Spike.Lib.A64.WakePh.lo) {R : Region}
    (hbase : R.base.toNat + 48 = (Ly).stacksA.toNat + 16384)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ lim2A Ly)
    (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) :
    ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-80) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
      Spike.Lib.A64.Rt.TakeOkA ms1 F (Ly).exe (WakeSpawnR.endR hp i) (R'.callee (-48) (-208) 0) F'
        (Ret0.tiTake (tiQ (t2 (Ly).lab) c0 g) g') := by
  intro c0 R' F' _ hR g g'
  subst hR
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hp i l x (by rw [hlo, hpg]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  have hlk : (Ly).lockA ≠ (Ly).pinA + 16#64 := ctr_ne hp i (by simp)
  have hnx : (Ly).nextA ≠ (Ly).pinA + 16#64 := ctr_ne hp i (by simp)
  refine ⟨?_, ?_, ?_, ?_, fun b' s c h => ?_, fun b' s c h => ?_, fun b' s c h => ?_⟩
  · rw [(Ly).lab_lock]
    exact ctr_st hp i E cT ls0 l b n hstat hland hFr (Ly).lock_mem hlk (hctr2 _ (by simp))
  · rw [(Ly).lab_freeN]
    exact ctr_ld hp i E cT ls0 l b n hstat hland hFr (Ly).freeN_mem
  · rw [(Ly).lab_lock]
    exact ctr_st hp i E cT ls0 l b n hstat hland hFr (Ly).lock_mem hlk (hctr2 _ (by simp))
  · rw [(Ly).lab_next]
    exact ctr_st hp i E cT ls0 l b n hstat hland hFr (Ly).next_mem hnx (hctr2 _ (by simp))
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.A64.Rt.Code.Take.spinL + Int64.ofNat (4 * 2)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownG (Ly) (ntA (Ly).lab) s
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), hq,
      ph_of_factOk hlab (take2_fact hΛ (f := .ph Spike.Lib.A64.Rt.Code.Take.spinL 2 12) (by simp [take2Tab])),
      (Ly).lab_lock]
    simp [own2b, ownV]
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.A64.Rt.Code.Take.lockedL + Int64.ofNat (4 * 1)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownG (Ly) (ntA (Ly).lab) s
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), (Ly).lab_freeN]
    simp [own2b, ownV]
  · obtain ⟨hsp, hpc⟩ := sp_of hbase h rfl
    have hq : pcOf s = ((Ly).lab Spike.Lib.A64.Rt.Code.Take.bumpL + Int64.ofNat (4 * 11)).toBitVec.toNat := by
      show s.st.2.toBitVec.toNat = _; rw [hpc]; rfl
    show _ ∈ ownG (Ly) (ntA (Ly).lab) s
    rw [ownG_2b hlab (.inl ⟨inPc_of hlab (by decide +kernel) hq, hsp⟩), hq,
      ph_of_factOk hlab (take2_fact hΛ (f := .ph Spike.Lib.A64.Rt.Code.Take.bumpL 11 12) (by simp [take2Tab])),
      (Ly).lab_next]
    simp [own2b, ownV]

end Place

/-- **Non-vacuity at wake's certificate**: `htk2_W` and the field lemmas
instantiate at `placeW_cert` with the program (`outLit_prog`), the counter
item (`ctrZ_cert`) and the static labels (`hstat_cert`) discharged; the
layout facts left as hypotheses. -/
example (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry) (cT : Loc)
    (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat) {F : MachineData → Prop}
    {R : Region}
    (hlo : (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hbase : R.base.toNat + 48 = (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).stacksA.toNat + 16384)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i) m)
    (hctr2 : ∀ a ∈ [(RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).pnA,
      (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).lockA,
      (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).freeNA,
      (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).nextA],
        a ≠ lim2A (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i))
    (hpin2 : (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).Λ.pinned.lo +
        (RuntimeLayout.ofPlaceW Spike.Lib.WakeFinalCAO.placeW_cert i).Λ.pinned.size)
    (hland : AllocLand (WakeOD.arW Spike.Lib.WakeFinalCAO.placeW_cert i).heap
      (WakeOD.arW Spike.Lib.WakeFinalCAO.placeW_cert i).cells b n) : True := by
  have := htk2_W Spike.Lib.WakeFinalCAO.placeW_cert i E cT ls0 l b n Spike.Lib.WakeSpawnRP.outLit_prog hlo hbase
    hFr hctr2 Spike.Lib.WakeFinalCAO.hstat_cert hland
  have := Ti2Fld.hoffT2_W Spike.Lib.WakeFinalCAO.placeW_cert i hpin2 Spike.Lib.WakeFinalCAO.ctrZ_cert
  trivial

/-- info: 'Spike.Lib.A64.WakePh.Ti2Tk.htk2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htk2_W

end Spike.Lib.A64.WakePh.Ti2Tk
