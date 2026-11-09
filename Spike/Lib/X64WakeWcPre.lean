/-
**wake.w's `wc_main` up to the allocator's return** (x86-64; twin of
`Spike/Lib/A64WakeWcPre.lean`, the pre-spawn consumer), inside `W`, in any
valid layout of `wakeCells` (`Spike/Lib/X64WakeCode.lean`), from checks
decided once on the cells (`decide +kernel`). The wake twin of
`X64Hello1Rodata.hello1_rodata_pre_segW`.

    wc_main:          pushq %rbp; movq %rsp, %rbp; … subq $64, %rsp
                      movq %rdi, -8(%rbp)              (the prologue, wcPro)
    .Lwc_main.entry:  movq $256, %rdi; movq $1, %rsi; movq $2, %rdx
                      call scc_rt_alloc                (wcE)
    .Lwc_main.x0:                                     -- the exit `wX .x18`

The region `R` is `wc_main`'s as handed over at the call
(`X64WakeMain.wR`): based at the return address's cell, so the saved
`%rbp` is at `-8`, main's `ThreadId` (`%rdi`) at `-16`, `%rsp` at `-72`
past the prologue (`oWR`), the pushed `.x18` at `-80`, the allocator's
region `R.callee (-80) (-160) 8` (`wAR`). From the box's store on
(`X64WakeWcSp0`) the nodes are in the frame based at the saved `%rbp`
(`WcClone.oW`), `R.fp (-8)` (`X64AtRebase.At.rebase`).

- `wake_alloc`: the allocator's code in `wakeCells`;
- `wcPro`, `wake_wcPro`: `wc_main`'s stack-checked prologue (frame 64, the
  limit at `%fs:8`, `%rdi` at `-8(%rbp)`);
- `wcE`, `wcEIn`, `wake_wcEIn`: `.entry` (the allocation's arguments, the
  call), `.x18` 26 bytes after it;
- `oWR`, `wcJ`, `wN`, `wX`, `wAR`, `WcCtx`, `WcPreW`: the body's offsets,
  `wc_main`'s frame record and saved `ThreadId`, its nodes and exits up to
  the allocator's return, the allocator's region and call context,
  `wc_main`'s states inside `W`;
- `AGB`: the allocator's ghost at a box allocation;
- `call_nd_FWKL`: `call_nd_FWK` with the callee's cells at the return;
- `wake_wc_pre_segW`: the segment from `wc_main`'s entry to the allocator's
  return at `.x18` or its heap abort. The source is at a box allocation of
  one object of two units with header `256` (`hq`: wake.w's
  `let o = new z`, `Call.OKB`); the allocator's return keeps the hold, the
  source's `new` being the box's store at `.x18` (`Out.newStore`).
-/
import Spike.Lib.X64Hello1Rodata
import Spike.Lib.X64AllocBox
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.X64.Alloc (Call AllocW Jfull)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The checks -/

theorem wake_alloc : Alloc.allocIn SccCode.wakeCells = true := by decide +kernel

/-- `wc_main`'s prologue: frame 64, `%rdi` (main's `ThreadId`) at `-8(%rbp)`. -/
abbrev wcPro : Bool := prologueIn SccCode.wakeCells "wc_main" ".Lwc_main.chk" ".Lwc_main.entry" 64 8
  ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)]

theorem wake_wcPro : wcPro = true := by decide +kernel

/-- `wc_main`'s `.entry` block: the allocation's arguments, the call. -/
def wcE : List (Directive × Nat) := (parse("movq $256, %rdi
movq $1, %rsi
movq $2, %rdx
call scc_rt_alloc")).zip [7, 7, 7, 5]

/-- `wc_main`'s body offsets from the return address's base: `%rsp` at the
frame's base, `%rbp` at the saved `%rbp`. -/
abbrev oWR : SO := ⟨-72, [(.rbp, -8)]⟩

block_spec wcE (-240) 8 oWR wcE

/-- **`wc_main`'s entry block in `cells`**, `.x18` right after the call. -/
def wcEIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.entry" 0 wcE && labelGapB cells ".Lwc_main.entry" ".Lwc_main.x0" 26

theorem wake_wcEIn : wcEIn SccCode.wakeCells = true := by decide +kernel

/-! ## Nodes -/

/-- The allocator's ghost at a box allocation: a call with its premises. -/
abbrev AGB (ms : MemSide isa) (lab : Label → Int64) : Type := {q : Call // q.OKB ms lab}

/-- **`wc_main`'s frame** as some entry state of `J0` left it: the return
address, the caller's `%rbp`, the saved `%rdi` (main's `ThreadId`). -/
def wcJ (J0 : AS → Ctl → Prop) (σ : AS) (c : Ctl) : Prop :=
  ∃ σe, J0 σe c ∧ σ.slot 0 = σe.slot 0 ∧ σ.slot (-8) = σe.regs.rbp.toBitVec ∧
    σ.slot (-16) = σe.regs.rdi.toBitVec

/-- `wc_main`'s nodes up to the call. -/
inductive WN where
  | e | call

/-- `wc_main`'s exits up to the allocator's return. -/
inductive WX where
  | x18 | abort

section Wc

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 : AS → Ctl → Prop)

/-- **The nodes**: `.entry` (`%rbp` at the saved `%rbp`) and the
allocator's entry with its arguments, the return address `.x18` pushed. -/
def wN : WN → ND
  | .e => ⟨lab ".Lwc_main.entry", oWR, Hello1.wJ R (wcJ J0)⟩
  | .call => ⟨lab "scc_rt_alloc", ⟨-80, []⟩, fun σ c => wcJ J0 σ c ∧ σ.regs.get64 .rbp = R.addr (-8) ∧
      σ.regs.rdi.toBitVec = 256#64 ∧ σ.regs.rsi.toBitVec = 1#64 ∧ σ.regs.rdx.toBitVec = 2#64 ∧
      σ.slot (-80) = (lab ".Lwc_main.x0").toBitVec⟩

/-- **The exits**: the allocator's return at `.x18` (its return's facts,
the frame record and `%rbp` kept), and its heap abort (the return address
`.Lscc_rt_alloc.full + 12` its `call scc_rt_abort` pushed, at `-240`). -/
def wX : WX → ND
  | .x18 => ⟨lab ".Lwc_main.x0", ⟨-72, []⟩, fun σ c => ∃ q : AGB ms lab, wcJ J0 σ q.1.c0 ∧
      σ.regs.get64 .rbp = R.addr (-8) ∧ (Alloc.EB lab ms q.1 .ret).J σ c⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-240, []⟩, fun σ c => σ.regs.rdi.toBitVec = 2#64 ∧
      σ.slot (-240) = (lab ".Lscc_rt_alloc.full" + 12).toBitVec ∧
      ∃ q : AGB ms lab, Jfull ms q.1 c ∧ ∃ σe, J0 σe q.1.c0⟩

end Wc

/-- The allocator's region at the call: based at the pushed return address
(`-80`), its frame of 160 below, the return address cell above. -/
abbrev wAR (R : Region) : Region := R.callee (-80) (-160) 8

/-- **The allocator's call context in `wc_main`'s region `R`** at the
memory `m` (`Hello1.RdCtx` at the call's `-80`). -/
def WcCtx (ms : MemSide isa) (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-80, []⟩ mC σC ∧ (wN lab R Jc .call).J σC c ∧ (Alloc.N lab ms q .e).J (enter (-80) σC) c ∧
    CKept R (-80) (-160) 8 mC m

/-- **`wc_main`'s states up to the allocator's return inside `W`**, none
moved by `K`: its prologue's, the entry block's, and the allocator's in its
region (`Hello1.RdPreW` at frame 64). -/
structure WcPreW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 Jc : AS → Ctl → Prop) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 64 8
    ".Lwc_main.stk" 5 9 3 6 4 [(.rdi, -8, 4)] J0
  e : BlkW W K exe endPc R F (wN (_root_.Executable.labels exe).label R J0 .e) wcE
  alloc : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label →
    q.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x0").toBitVec →
    AllocW ms q W K exe endPc (wAR R)
      (fun m => F m ∧ CallerCells R (-80) (-160) 8 m ∧ WcCtx ms (_root_.Executable.labels exe).label R Jc q m)

/-- `wc_main` up to the allocator's return is inside the trivial
predicate, with no outside moves. -/
theorem WcPreW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 Jc : AS → Ctl → Prop} :
    WcPreW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Jc :=
  ⟨XProW.triv, BlkW.triv, fun q _ _ => Alloc.AllocW.triv ms q⟩

/-! ## A call node keeping the callee's cells -/

section CallL

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- **`call_nd_FWK` with the callee's cells at the return**: the same node,
`hret` also given the landing state's slots inside the callee's region as
the callee's exit state's (`leave`'s). A callee that does not return (the
allocator's heap abort, `call scc_rt_abort` pushing its return address in
its own frame) hands its words there to the caller's exit. -/
theorem call_nd_FWKL {KC : Prop} {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
        (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
            Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      (∀ k, (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σx.slot (k - (nC.o.sp - e0))) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F₂ N E) := by
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the caller's cells outside the callee's region, as in `m0`
  let Kept : MachineData → MachineData → Prop := fun m0 m =>
    ∀ k, R.Off k → ¬ R'.Off (k - kb) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  refine SegW.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegW.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G)
        (fun _ h => h.1) rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c ⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, hM⟩
      obtain ⟨mC, σC, cC, g⟩ := G
      simp only at hDF hAC hJC hJE hJx hAx hpc
      have hAR : Abs R ⟨kb + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kb σC σx) := by
        refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
        · intro r k' hr
          obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
          have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
        · by_cases hin : R'.Off (k - kb)
          · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
            refine ⟨j, ?_, ?_⟩
            · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
            · simp only [leave]; rw [ite_eq_left hin]; exact hv
          · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
            refine ⟨j, ?_, ?_⟩
            · rw [hDF k hk hin]
              exact hj
            · simp only [leave]; rw [ite_eq_right hin]; exact hv
      have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
        (fun k hin => by simp only [leave]; exact ite_eq_left hin)
      have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
      rw [hs]
      rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
      · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hD hM)⟩
      · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hD hM)⟩
    · exact SegW.empty fun s c ⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

end CallL

section WcFn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` up to the allocator's return is one segment inside `W`**
in any valid layout of `wakeCells`: from its entry (invariant `J0`, `%rsp`
at the region's offset 0, the return address there, the limit word's facts
for its frame of 64 below the saved `%rbp`, `hlim`) to the allocator's
return at `.x18` or its heap abort. The source at the entry is at a box
allocation the allocator's premises hold for (`Call.OKB`: wake.w's
`let o = new z`, after `let z = zero int`), with header `256`, one object
of two units (`hq`); the counter and the headers it may store are unmapped
in private memory under `F` (`hmem`). The allocator's return keeps the hold
recording the counter's old value (`Alloc.EB`): the source's `new`
(`TermRun.alloc`) is taken at `.x18`'s `movq %rax, (%rcx)`, the box's store
(`Out.newStore`, `Alloc.newStore_ndW`). Its states lie in `W`, none moved
by `K` (`hW`). -/
theorem wake_wc_pre_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi)
    {J0 : AS → Ctl → Prop} (hW : WcPreW W K exe endPc R F ms J0 J0)
    (hlim : ∀ σ c, J0 σ c → LimOk ms F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hq : ∀ σ c, J0 σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (wX ms (_root_.Executable.labels exe).label R J0 y) s c) := by
  have hin := wake_wcEIn
  simp only [wcEIn, Bool.and_eq_true] at hin
  obtain ⟨h0, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e26 : lab ".Lwc_main.x0" = lab ".Lwc_main.entry" + Int64.ofNat 26 := label_labelGapB hp hgap
  refine SegW.seq (prologue_seg_ofW hp hend wake_wcPro (nb := ⟨lab ".Lwc_main.entry", oWR, wcJ J0⟩)
    (by decide) hF hR
    (by show R.lo ≤ -8 - (64 : Int64).toInt; rw [show (64 : Int64).toInt = 64 from rfl]; omega) (by omega)
    (by decide) rfl (by show SO.le oWR (oF 64) = true; decide) hW.pro ?_)
    ((fn_segW (N := wN lab R J0) (E := wX ms lab R J0) (fun i => ?_) WN.e).mono_pre
      fun _ _ h => Hello1.At.reg_addr (r := .rbp) (k := -8) rfl h)
  · intro σ c hJ
    have hl := hlim σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_, ?_, ?_⟩⟩⟩
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    · rw [hs]; simp [xStSlots, xS1, upd_apply]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  cases i
  case e =>
    refine seg_ndW (by simp [wcE]) wcE_ok hF hR hlo hhi (code_field hp hend h0 (ofNat_zero' _)) hW.e
      fun σ c hJ => ⟨c, .refl c, .inl ⟨WN.call, ?_, ?_, ?_⟩⟩
    · simp only [wN]; rw [wcE_run]
    · simp only [wN]; rw [wcE_run]; rfl
    · simp only [wN] at hJ ⊢
      rw [wcE_run]
      obtain ⟨⟨σe, hJe, h0', h8, h16⟩, hb⟩ := hJ
      refine ⟨⟨σe, hJe, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [upd_apply]; exact h0'
      · simp only [upd_apply]; exact h8
      · simp only [upd_apply]; exact h16
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; exact hb
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · simp [Reg64s.set64]
      · rw [e26]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add]
        rfl
  case call =>
    refine call_nd_FWKL (KC := False) (e0 := 0) (lo' := -160) (hi' := 8) (M := fun _ => True)
      (Ne := fun g : AGB ms lab => Alloc.N lab ms g.1 .e) (Ex := fun g : AGB ms lab => Alloc.EB lab ms g.1)
      hR hF (by show R.lo ≤ -80 - 0 + -160; omega) (by decide) (by show (-80 : Int) - 0 < R.hi; omega)
      (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-80 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, -, -, -, h80⟩, ⟨-, -, hra, -⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_main.x0").toBitVec := by
          rw [← hra, ← h80]; rfl
        exact (Alloc.seg_allocBW hp hend wake_alloc hF' hR' hlo' hhi' g.2
          (fun a ha m hm => hmem g.1 g.2 a ha m (hFF m hm))
          (Hello1.allocW_mono (hW.alloc g.1 g.2 hr) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩)).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨σe, hJe, -, -, -⟩, -, h0, h1, h2, -⟩
      obtain ⟨q, hok, hc, hh, hk, hu⟩ := hq σe c hJe
      exact ⟨⟨{ q with fp := σC.regs.rbp.toBitVec, ra := σC.slot (-80 - 0 + 0) },
        ⟨{ hok.toS with }, hok.newOk, hok.term, hok.ev, hok.one⟩⟩, rfl,
        hc.symm, rfl, rfl, h0.trans hh.symm, h1.trans hk.symm, h2.trans hu.symm⟩
    · rintro g y σC c σx c' σR ⟨⟨σe, hJe, h0', h8, h16⟩, hb, -, -, -, h80⟩ ⟨hc, hfp, hra, -⟩ hx hreg - - hsl
        hin
      cases y
      · refine .inr ⟨WX.x18, ?_, by show SO.le ⟨-72, []⟩ ⟨-80 - 0 + 8, []⟩ = true; decide, g,
          ⟨σe, hc ▸ hJe, ?_, ?_, ?_⟩, ?_, ?_⟩
        · show lab ".Lwc_main.x0" = Int64.ofBitVec g.1.ra
          rw [← hra]
          show _ = Int64.ofBitVec (σC.slot (-80 - 0 + 0))
          rw [show (-80 : Int) - 0 + 0 = -80 by decide, h80, int64_ofBitVec_toBitVec]
        · rw [hsl 0 ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), h0']
        · rw [hsl (-8) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), h8]
        · rw [hsl (-16) ⟨by decide, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega),
            h16]
        · simp only [Alloc.EB] at hx
          obtain ⟨-, -, -, -, -, hbx⟩ := hx
          rw [← hb]
          simp only [Reg64s.get64]
          rw [hreg, hbx, ← hfp]; rfl
        · simp only [Alloc.EB] at hx ⊢
          rw [hreg]; exact hx
      · obtain ⟨h2, hfull, hs⟩ := hx
        refine .inr ⟨WX.abort, rfl, by show SO.le ⟨-240, []⟩ ⟨-80 - 0 + -160, []⟩ = true; decide, ?_, ?_,
          g, hfull, σe, hc ▸ hJe⟩
        · show σR.regs.rdi.toBitVec = 2#64
          rw [hreg]; exact h2
        · show σR.slot (-240) = _
          rw [hin (-240) (by simp only [Region.Off, Region.callee, wN]; omega)]
          exact hs

end WcFn

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_alloc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_pre_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_pre_segW
