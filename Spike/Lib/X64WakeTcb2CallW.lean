/-
**wc_main's second `scc_rt_alloc_tcb` call block inside the global
owned-words map** (x86-64; twin of `Spike/Lib/A64WakeTcb2CallW.lean`): the
block `tcb2Call` at `.x19` (`Spike/Lib/X64WakeTcb2Call.lean`) inside
`SFactsSt2` at `ownG` (`tcb2Call_ownG`), proved at the first instance's
constant owned words `ownW L a 16` (`blk_switch2`) and moved to `ownG`,
which picks them at the block's pcs (the final `ownW (phW pc)` branch,
`phW = 16`) and at the callee's entry on a pool stack
(`own2a (ph2a 4198992)`, `own1_own2a_ph`); and the outside move retargeted
to any range (`tcbWG_takeK`), so one `K := PhRec.K L rS'` serves the whole
segment.

- `takeK_none`, `blkW_takeK`, `nodeW_takeK`, `tcbWG_takeK`: no take move
  at one range is none at any other.
- `blkPh_const_of`: `blkPh` at a constant phase map from the block's pcs'
  `okPc`.
- `blk_switch2`: any covered `ret`-free block, after the take, at the
  constant instance `o`, inside `SFactsSt2` at a map agreeing with `o`.
- `BandSp3`: **main's frame at `.x19` on a pool stack** (the hypothesis
  `WcMid` supplies from main's frame facts): `BandA` of the callee's region
  `R.callee (-72) (-184) 8`.
- `sp3_facts`, `lab_sp3`, `own_sp3`, `own_fn`: `ownG` is `ownW L a 16` at
  the block's pcs and at the callee's entry.
- `tcb2Call_ownG`: the result; `tcb2W_ownGK`: the callee's at the same `K`.

**Unlike AArch64**: the names keep A64's `sp3` though the block is at
`.Lwc_main.x19` (`lab_sp3` is `.x19`'s address, `4203349`); the block has 4
cells (`movq`, `movq`, `movq`, `call`; A64's 5), its pcs `.x19 + cellOff`;
the callee's region is `R.callee (-72) (-184) 8` (based at the pushed
return address, `oC`; A64's `R.callee (-80) (-192) 0`); the block's bounds
are `hlo3 : R.lo ≤ -72`, `hhi : 16 ≤ R.hi` (A64's `-80`, `0`); no `hal`;
`tcb2W_ownGK` takes `tcb2W_ownG`'s x86-64 premises (`hlo' : R.lo ≤ -184`,
`hhi : 8 ≤ R.hi`, the return to `.Lwc_main.x20`).
-/
import Spike.Lib.X64WakeTcb2W

namespace Spike.Lib.X64.WakePh.Tcb2CallW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq code_field okPcOf)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts)
open Spike.Lib.X64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW AS SO cellOff okBlk)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TakeK StackM)
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Call tcb2Call_ok tcb2Call_pc wake_tcb2CallIn tcb2CallIn wcN3)
open Spike.Lib.X64.WakePh.Tcb2W (BandA PcA good2a_of blkW_toSt2 tcb_labs)

/-! ### The outside move at any range -/

section TakeK

variable {W : Frag isa} {a : Int64} {rS rS' : Range} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **No take move at `rS` is none at `rS'`**: a take moves any state at
its pc. -/
theorem takeK_none {s : State} (h : ∀ s', ¬ TakeK a rS s s') : ∀ s', ¬ TakeK a rS' s s' :=
  fun _ hk => let ⟨pm, _⟩ := hk.2; h _ ⟨hk.1, pm, rfl⟩

/-- A block's obligations at the take of any range. -/
theorem blkW_takeK {n : ND} {blk : List (Directive × Nat)} (h : BlkW W (TakeK a rS) exe endPc R F n blk) :
    BlkW W (TakeK a rS') exe endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1, takeK_none r.2⟩

/-- A node's obligations at the take of any range. -/
theorem nodeW_takeK {n : ND} (h : NodeW W (TakeK a rS) exe endPc R F n) : NodeW W (TakeK a rS') exe endPc R F n :=
  fun s c hA => ⟨(h s c hA).1, takeK_none (h s c hA).2⟩

/-- **`scc_rt_alloc_tcb`'s node obligations at the take of any range**
(`tcb2W_ownG`'s at `PhRec.K L rS'`). -/
theorem tcbWG_takeK {q : Spike.Lib.X64.Rt.TcbGG}
    (h : ∀ i, Spike.Lib.X64.Rt.TcbWG W (TakeK a rS) exe endPc R F q i) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG W (TakeK a rS') exe endPc R F q i := by
  intro i
  have h := h i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TcbWG] at h ⊢ <;> first | exact blkW_takeK h | exact nodeW_takeK h

end TakeK

/-! ### A covered block at a constant instance, moved to an agreeing map -/

/-- **`blkPh` at a constant phase map**: every directive classified, every
pc of the block off the sites. -/
theorem blkPh_const_of {okPc : Nat → Bool} {lab : Label → Int64} {pc ra : Int64} {blk : List (Directive × Nat)}
    (hc : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hok : ∀ k < blk.length, okPc (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true) :
    Spike.Lib.X64Consumer.blkPh okPc (fun _ => 0) (fun _ => false) lab pc ra blk = true := by
  unfold Spike.Lib.X64Consumer.blkPh
  refine List.all_eq_true.mpr fun k hk => ?_
  have hk' := List.mem_range.mp hk
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hc _ (List.getElem_mem hk'))
  rw [List.getElem?_eq_getElem hk']
  simp only [hok k hk', hd, beq_self_eq_true, Bool.true_and]
  simp

/-- **A covered `ret`-free block across instances**: as `call_switch2` for
any block, its pcs off the sites (`hpc`), after the take, proved at the
constant instance `o` and moved to `own'`, which agrees with `o` at the
block's states and their successors (`hag`). -/
theorem blk_switch2 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own own' : Spike.Lib.X64Consumer.Own}
    {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (o : List (Loc × Val)) {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)}
    {l : Label} {off : Nat} {lo hi : Int} (hb : Scc.Cert.Rt.X64.blockAtB cells l off blk = true)
    (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hcl : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hpc : ∀ k < blk.length, okPc (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS))
    (hag : BlkW (fun s _ => own' s = o ∧ ∀ s', StSucc μ s s' → own' s' = o) (fun _ _ => False) exe endPc R
      (fun m => F m ∧ StackM rS m) n blk) :
    BlkW (fun s _ => SFactsSt2 Λ μ own' s) K exe endPc R (fun m => F m ∧ StackM rS m) n blk := by
  have h := Spike.Lib.X64.Rt.blkW_post (Λ := Λ) (rS := rS) (lbl := lbl) (F := F)
    (Spike.Lib.X64.Rt.InstOk.const hI o True) hb he hok hR hlo hhi hC (ra := 0)
    (dead := fun _ => false) (by rw [he]; exact blkPh_const_of hcl hpc)
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl) hsub hSM
  exact Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (blkW_toSt2 h) hag

/-! ### `ownG` at the block's pcs and at the callee's entry -/

/-- **Main's frame at `.x19` on a pool stack**: `scc_rt_alloc_tcb`'s frame
`[-184, 8]` around `%rsp = R.addr (-72)` at its entry (`wc_main`'s region
`R`, its 64-byte frame and the pushed return address) in the pool's band.
`WcMid` supplies it from main's frame facts. -/
abbrev BandSp3 (L : RuntimeLayout) (R : Region) : Prop := BandA L (R.callee (-72) (-184) 8)

/-- The block's pcs at the canonical base: their values, the phase `16`,
off the sites, at most 18 bytes on. -/
theorem sp3_facts : ∀ k < 4,
    (Int64.ofNat 4203349 + Int64.ofNat (cellOff tcb2Call k)).toBitVec.toNat = 4203349 + cellOff tcb2Call k ∧
    phC (4203349 + cellOff tcb2Call k) = 16 ∧ okC (4203349 + cellOff tcb2Call k) = true ∧
    cellOff tcb2Call k ≤ 18 := by decide +kernel

variable {L : RuntimeLayout}

/-- `.x19` at the canonical base. -/
theorem lab_sp3 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label ".Lwc_main.x19" = Int64.ofNat 4203349 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- **`ownG` at the block's pcs** is `ownW L a 16` (no range of `ownG`'s
holds, `phW = 16`). -/
theorem own_sp3 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {s : State} {k : Nat} (hk : k < 4)
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label ".Lwc_main.x19" + Int64.ofNat (cellOff tcb2Call k)) :
    ownG L a s = ownW L a 16 := by
  have hp : pcOf s = 4203349 + cellOff tcb2Call k := by
    unfold pcOf; rw [hs, lab_sp3 hlab]; exact (sp3_facts k hk).1
  have hc := (sp3_facts k hk).2.2.2
  obtain ⟨e1, e2, e3, e4, e5, -, e7, e8, e9⟩ := labs_eq hlab (L := L)
  rw [ownG_W hlab (.inr (.inr ⟨?_, ?_, ?_, ?_⟩)), hp, phW_eq, (sp3_facts k hk).2.1] <;> unfold inPc <;> omega

/-- **`ownG` at the callee's entry**, `%rsp` at `R.addr (-72)` on a pool
stack: `own2a (ph2a 4198992)`, the first instance's `ownW L a 16`. -/
theorem own_fn (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {R : Region} (hb : BandSp3 L R) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.AllocTcb.fnL)
    (hsp : s.st.1.regs.rsp.toBitVec = R.addr (-72)) : ownG L a s = ownW L a 16 := by
  obtain ⟨eFn, -, -, -, -, -⟩ := tcb_labs hlab (L := L)
  have hp : pcOf s = 4198992 := by unfold pcOf; rw [hs, eFn]; rfl
  have hg := good2a_of hlab hb (s := s) (by rw [hs, eFn]; decide)
    ⟨0, by decide, by decide, by rw [hsp, Region.callee_addr]; rfl⟩
  rw [ownG_2a hlab hg, hp, ← own1_own2a_ph, phW_eq, allocTcb2_ph.1]

/-! ### The block -/

/-- **The second call's block at `.x19` inside `SFactsSt2` at `ownG`**,
after the take (`hsub`, `hSM` at main's range `rS`), at the outside move of
any range `rS'`: `blk_switch2` at the first instance (`instOkW`, constant
`ownW L a 16`), `ownG` agreeing there at the block's pcs (`own_sp3`) and at
the callee's entry (`own_fn`, main's frame on a pool stack `hb`). -/
theorem tcb2Call_ownG (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0) {J : AS → Prop}
    {R : Region} (hR : R.OK) (hlo3 : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    (hb : BandSp3 L R) {F : MachineData → Prop} {rS : Range} (rS' : Range)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS')
      L.exe L.endPc R (fun m => F m ∧ StackM rS m) (wcN3 L.lab J c0) tcb2Call := by
  obtain ⟨-, -, -, -, -, eSite⟩ := tcb_labs hlab (L := L)
  have e3 := lab_sp3 hlab (L := L)
  have hin := hp ▸ wake_tcb2CallIn
  simp only [tcb2CallIn, Bool.and_eq_true] at hin
  have hlen : tcb2Call.length = 4 := by decide
  refine blk_switch2 (instOkW hp hlo a (fun _ => True) hsite (rS := rS')) (ownW L a 16) hin.1
    (ofNat_zero' _) tcb2Call_ok hR hlo3 hhi (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
    (by decide +kernel) (fun k hk => ?_) hsub hSM ?_
  · show okPcOf lo wakeCells L.Λ
      ((_root_.Executable.labels L.exe).label ".Lwc_main.x19" + Int64.ofNat (cellOff tcb2Call k)).toBitVec.toNat
        = true
    rw [okPc_eq hΛ, e3, (sp3_facts k (hlen ▸ hk)).1]; exact (sp3_facts k (hlen ▸ hk)).2.2.1
  refine Spike.Lib.X64ConsumerA.BlkW.leaf (code_field L.lays rfl hin.1 (ofNat_zero' _)) tcb2Call_ok hR hlo3 hhi
    ?_ ?_ ?_
  · intro x hx k hk
    rw [hsite, show L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 from eSite] at hx
    cases hx
    show ((_root_.Executable.labels L.exe).label ".Lwc_main.x19" + Int64.ofNat (cellOff tcb2Call k)).toBitVec.toNat
      ≠ _
    rw [e3, (sp3_facts k (hlen ▸ hk)).1]
    have : (Int64.ofNat 4200277).toBitVec.toNat = 4200277 := rfl
    omega
  · intro σ c hJ k hk s m hA he hn hs
    exact own_sp3 hlab (hlen ▸ hk) (by rw [hs]; rfl)
  · intro σ c hJ k hk s m hA he hn hs
    rcases Nat.lt_or_ge (k + 1) 4 with hk1 | hk1
    · rw [Spike.Lib.X64.arun_pc _ tcb2Call_ok (by rw [hlen]; exact hk1)] at hs
      exact own_sp3 hlab hk1 (by rw [hs]; rfl)
    · have ht : tcb2Call.take (k + 1) = tcb2Call := List.take_of_length_le (by omega)
      rw [ht] at hA hs
      obtain ⟨h1, h2⟩ := tcb2Call_pc (_root_.Executable.labels L.exe).label
        ((_root_.Executable.labels L.exe).label ".Lwc_main.x19") σ
      refine own_fn hlab hb (by rw [hs]; exact h1) ?_
      have e := Spike.Lib.X64ConsumerA.rsp_of_abs hA
      rw [show (wcN3 L.lab J c0).pc = (_root_.Executable.labels L.exe).label ".Lwc_main.x19" from rfl,
        show (wcN3 L.lab J c0).o = Tcb2Call.oW from rfl, h2] at e
      rw [hs]; exact e

/-- **`tcb2W_ownG` at the outside move of any range `rS'`** (`tcbWG_takeK`):
the callee's node obligations at `PhRec.K L rS'`, its frame condition still
main's range `rS`. -/
theorem tcb2W_ownGK (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64) {rS : Range}
    (rS' : Range)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hb : BandA L R) (g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G) (hra : g.ra = (L.lab ".Lwc_main.x20").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true
      ⟨Spike.Lib.X64.Rt.hdrA L.lab (Tcb2Call.tcb2Q g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (Tcb2Call.tcb2Q g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s)
      (Spike.Lib.X64.PhRec.K L rS') L.exe L.endPc R (fun m => F m ∧ StackM rS m) (Tcb2Call.tcb2Q g c0) i :=
  tcbWG_takeK (Tcb2W.tcb2W_ownG hp hlo a hsite hΛ hlab hsep hhdr hC0 hR hlo' hhi hb g hra hmP hmH hunP hunH
    hsub hSM)

end Spike.Lib.X64.WakePh.Tcb2CallW

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.takeK_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.takeK_none

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.blkW_takeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.blkW_takeK

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.nodeW_takeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.nodeW_takeK

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.tcbWG_takeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.tcbWG_takeK

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.blkPh_const_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.blkPh_const_of

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.blk_switch2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.blk_switch2

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.sp3_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.sp3_facts

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.lab_sp3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.lab_sp3

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.own_sp3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.own_sp3

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.own_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.own_fn

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.tcb2Call_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.tcb2Call_ownG

/-- info: 'Spike.Lib.X64.WakePh.Tcb2CallW.tcb2W_ownGK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2CallW.tcb2W_ownGK
