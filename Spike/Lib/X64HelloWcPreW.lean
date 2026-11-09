/-
**hello.w's `wc_main` before `.x24` inside `SFactsSt2` at `ownGH`: the label-relative checks and the block/node
movers** (x86-64; the twin of `Spike/Lib/A64HelloWcPreW.lean`, at `helloCells` the twin of x86-64 wake's
`X64WakeFree` and `X64WakeWcPreW` and of `X64WakeWcPreWN.nodeW_wcG`). A block or a node of `wc_main` before
`.x24` is proved at the first instance (`instOkH`, owned words `ownH L a (phH pc)`, no take phase) and moved to
`ownGH`, which picks `ownH` at every pc off its four ranges (`GoodWH`'s last disjunct).

The pcs are checked by the kernel against helloCells' labels, with no absolute address in this file. wake's
program-independent pieces are reused: `WcW.blkW_mapC`, `WcW.nodeW_mapC`, `WcW.succ_pc`, `WcW.c0N`,
`Tcb2W.blkW_toSt2`, `Tcb2W.nodeW_toSt2`, `Tcb2W.nodeW_ownCongr2`.

- `cvH`, `inCvH`, `freeNH`, `freeAtH`, `freeBlkH`, `lab_cvH`, `freeAt_pcH`, `freeAt_labH`, `freeBlk_pcH`,
  `freeLabsH`: the label-relative checks.
- `goodW_of_freeNH`, `site_ne_of_freeNH`: `GoodWH` and off the take site.
- `blkAgreeWH`, `nodeAgreeWH`: a block's (a node's) agreement with `ownH`.
- `wcTabWH`, `wcFactsWH`, `wcW_factH`: the blocks' phase facts at `phH` (frame 128, five argument spills).
- `blkW_wcGH`, `nodeW_wcGH`: a block (a node) of `wc_main` before `.x24` inside `SFactsSt2` at `ownGH`.

## Differences from the AArch64 version

- Offsets are bytes and cells sized (as in `X64WakeFree`): `freeAtH l os` checks the pcs `lab l + o` for the
  byte offsets `o ∈ os` (AArch64's `freeAtH l k n`, the `n` pcs `lab l + 4 (k + j)`), `freeBlkH l k blk` a
  block's pcs; `blkW_wcGH` takes `freeBlkH l k blk` and has no `hal`; `nodeAgreeWH`/`nodeW_wcGH` are at a cell
  of size `z` off `syscall` (AArch64: `4`, off `svc`; wake's `succ_pc` replaces `succ_pc4`).
- `ownGH`'s third range is `.Lwc_main.x2`–`.Lwc_main.stk` (AArch64's `.sp4`–`.stack_grow`), so the blocks
  covered are those before `.x24`: the prologue (`xHead`, `xLea`, the limit's load as a 9-byte `step`, `xCmp`,
  `xFr` with the five spills), the entry block, `.x22`'s block, the box's store (one 3-byte `step`), the
  reserve's call; there is no fence (scc's `# fence st` emits no code under TSO). The `.x23` block
  (`X64HelloWcSp3.tcb2CallH`) is R3's `X64HelloTcb2CallW`.
- The import is `X64HelloWcSp0` and wake's generic movers, not the hello TCB call's W-module (AArch64:
  `A64HelloTcb2CallW`): nothing here reads it.
-/
import Spike.Lib.X64HelloWcSp0
import Spike.Lib.X64HelloOwnGAgree
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeWcPreWN

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk blockAtB code_field pcAt)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk)
open Spike.Lib.X64.Rt.PhOfTab (pcAt_eq blkPh_of_factOk)
open Kraken.Promising.Lower.X64 (CellAt)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh (inPc)
open Spike.Lib.X64.WakePh.WcW (blkW_mapC nodeW_mapC succ_pc c0N)

/-! ## The label-relative checks -/

/-- A label's address in helloCells at the canonical base (`0` if absent). -/
def cvH (l : Label) : Nat := (codeLabel lo helloCells l).getD 0

/-- `x` in `[cvH l₁, cvH l₂)`. -/
def inCvH (l₁ l₂ : Label) (x : Nat) : Bool := cvH l₁ ≤ x && x < cvH l₂

/-- **A pc where `ownGH` picks `ownH` whatever the state**: off `ownGH`'s four ranges, and off the take site. -/
def freeNH (x : Nat) : Bool :=
  !inCvH "scc_rt_alloc_tcb" "scc_rt_thread_reserve" x && !inCvH "scc_rt_thread_init" "scc_rt_stack_release" x &&
    !inCvH ".Lwc_main.x2" ".Lwc_main.stk" x && !inCvH "scc_rt_abort" "scc_rt_thr_worker" x &&
    x != cvH Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The pcs `lab l + o` for the byte offsets `o ∈ os` are free.** -/
def freeAtH (l : Label) (os : List Nat) : Bool :=
  os.all fun o => match pcAt (codeLabel lo helloCells) l o with
    | some t => freeNH t
    | none => false

/-- **A block's pcs from `lab l + k` are free.** -/
def freeBlkH (l : Label) (k : Nat) (blk : List (Directive × Nat)) : Bool :=
  freeAtH l ((List.range blk.length).map fun j => k + cellOff blk j)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- A label of helloCells read through `L.lab`. -/
theorem lab_cvH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (hs : (codeLabel lo helloCells l).isSome = true) (hb : cvH l < 2 ^ 64) : (L.lab l).toBitVec.toNat = cvH l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have e : cvH l = x := by simp [cvH, hx]
  rw [e] at hb ⊢
  rw [hlab l x hx]
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- **The pcs `freeAtH` checks**, read through `L.lab`. -/
theorem freeAt_pcH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {os : List Nat} (h : freeAtH l os = true) {o : Nat} (ho : o ∈ os) :
    freeNH (L.lab l + Int64.ofNat o).toBitVec.toNat = true := by
  have h1 := List.all_eq_true.mp h o ho
  revert h1
  cases ht : pcAt (codeLabel lo helloCells) l o with
  | none => intro h1; cases h1
  | some t => intro h1; rw [pcAt_eq hlab ht]; exact h1

/-- **`freeAtH` at a label.** -/
theorem freeAt_labH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    (h : freeAtH l [0] = true) : freeNH (L.lab l).toBitVec.toNat = true := by
  have := freeAt_pcH hlab h (List.mem_singleton.mpr rfl)
  rwa [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this

/-- **The pcs `freeBlkH` checks**, read through `L.lab`. -/
theorem freeBlk_pcH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {k : Nat} {blk : List (Directive × Nat)} (h : freeBlkH l k blk = true) {j : Nat} (hj : j < blk.length) :
    freeNH (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := by
  have := freeAt_pcH hlab h (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  rwa [Int64.ofNat_add, ← Int64.add_assoc] at this

/-- The labels `freeNH` reads are helloCells', below `2 ^ 64`. -/
theorem freeLabsH :
    [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init", "scc_rt_stack_release",
      ".Lwc_main.x2", ".Lwc_main.stk", "scc_rt_abort", "scc_rt_thr_worker",
      Spike.Lib.X64.Flow.Ret0.StackTake.siteL].all
      (fun l => (codeLabel lo helloCells l).isSome && decide (cvH l < 2 ^ 64)) = true := by
  unfold cvH; rw [← codeT_eq]; decide +kernel

/-- **At a free pc `ownGH` picks `ownH`.** -/
theorem goodW_of_freeNH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (h : freeNH (pcOf s) = true) : GoodWH L s := by
  have hl : ∀ l ∈ [("scc_rt_alloc_tcb" : Label), "scc_rt_thread_reserve", "scc_rt_thread_init",
      "scc_rt_stack_release", ".Lwc_main.x2", ".Lwc_main.stk", "scc_rt_abort",
      "scc_rt_thr_worker", Spike.Lib.X64.Flow.Ret0.StackTake.siteL], (L.lab l).toBitVec.toNat = cvH l := by
    intro l hl
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact lab_cvH hlab this.1 this.2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hl
  simp only [freeNH, inCvH, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, Nat.not_le, Nat.not_lt] at h
  refine .inr (.inr ⟨?_, ?_, ?_, ?_⟩) <;> unfold inPc <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8] <;> omega

/-- **A free pc is off the take site.** -/
theorem site_ne_of_freeNH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {x : Nat} (h : freeNH x = true) : x ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have := List.all_eq_true.mp freeLabsH Spike.Lib.X64.Flow.Ret0.StackTake.siteL (by simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rw [lab_cvH hlab this.1 this.2]
  simp only [freeNH, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-! ## A block's agreement -/

section Agree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`ownGH` agrees with `ownH` on a covered block at free pcs**: its pcs (`hin`) and the pc its run ends at
(`hlast`) free, the take site `L`'s. -/
theorem blkAgreeWH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hsite : μ.site .take = some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hin : ∀ k < blk.length, freeNH (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk := by
  refine hagWH hlab hcode hok hR hlo hhi (fun x hx k hk => ?_) (fun σ c _ k hk s m _ _ _ hs => ?_)
    (fun σ c hJ k hk s m _ _ _ hs => ?_)
  · rw [hsite] at hx; cases hx
    exact site_ne_of_freeNH hlab (hin k hk)
  · exact goodW_of_freeNH hlab (by unfold pcOf; rw [hs]; exact hin k hk)
  · refine goodW_of_freeNH hlab ?_
    unfold pcOf; rw [hs]
    rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
    · rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk1]; exact hin (k + 1) hk1
    · rw [List.take_of_length_le (by omega)]; exact hlast σ c hJ

end Agree

/-! ## The blocks' phase facts -/

/-- **`wc_main`'s blocks before `.x24`**: the prologue's four blocks and its limit load, the entry block,
`.x22`'s block, the box's store, the reserve's call. -/
def wcTabWH : List PhFact :=
  [.blk "wc_main" 0 Spike.Lib.X64.Flow.xHead none none,
   .blk ".Lwc_main.chk" 0 (Spike.Lib.X64.Flow.xLea 128 5) none none,
   .step ".Lwc_main.chk" 5 9,
   .blk ".Lwc_main.chk" 14 (Spike.Lib.X64.Flow.xCmp ".Lwc_main.stk" 3 6) none none,
   .blk ".Lwc_main.chk" 23
     (Spike.Lib.X64.Flow.xFr 128 7 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)])
     none none,
   .blk ".Lwc_main.entry" 0 Spike.Lib.X64.Flow.HelloWc.wcEH none none,
   .blk ".Lwc_main.x0" 0 Spike.Lib.X64.Flow.HelloWc.wcS0H none none,
   .step ".Lwc_main.x0" 15 3,
   .blk ".Lwc_main.x0" 18 Spike.Lib.X64.Flow.HelloWc.resBH none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem wcFactsWH : wcTabWH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

/-- **A fact of `wcTabWH` at `phH`.** -/
theorem wcW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ wcTabWH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp wcFactsWH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-! ## A block inside `SFactsSt2` at `ownGH` -/

/-- **A covered `ret`-free block of `wc_main` before `.x24` inside `SFactsSt2` at `ownGH`**, at the outside move
of any range `rS`: `blkW_pre` at the first instance with no take phase (`instOkH`), the source control replaced
by `X64Consumer.c0` (`cfacts_c0`: the state facts do not read it), moved to `ownGH` (`blkAgreeWH`) at its free
pcs (`hfree`) and free end (`hlast`), its phase fact `hf` from `wcTabWH`. -/
theorem blkW_wcGH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}
    {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk none none ∈ wcTabWH) (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hfree : freeBlkH l k blk = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.X64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (wcW_factH hΛ hf)
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := code_field L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeBlk_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-! ## A node's agreement -/

section NAgree

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {n : ND}

/-- **`ownGH` agrees with `ownH` at a node** whose pc and next pc are free (`hf0`, `hfz`), each of its states at
a cell of size `z` off `syscall` whose leaves are `z` bytes on (`hstep`). -/
theorem nodeAgreeWH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : μ.site .take = some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {z : Nat}
    (hf0 : freeNH n.pc.toBitVec.toNat = true) (hfz : freeNH (n.pc + Int64.ofNat z).toBitVec.toNat = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  have hpc : s.st.2 = n.pc := hAt.2.2.2.1
  have hp0 : pcOf s = n.pc.toBitVec.toNat := by unfold pcOf; rw [hpc]
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hAt
  refine ⟨⟨ownGH_W hlab (goodW_of_freeNH hlab (by rw [hp0]; exact hf0)), fun s' h => ?_⟩, fun _ h => h⟩
  have hns : ∀ x, μ.site .take = some x → pcOf s ≠ x := by
    intro x hx; rw [hsite] at hx; cases hx; rw [hp0]; exact site_ne_of_freeNH hlab hf0
  have e := succ_pc hc hd hex hl hns h
  refine ownGH_W hlab (goodW_of_freeNH hlab ?_)
  unfold pcOf; rw [e, hpc]; exact hfz

end NAgree

/-! ## A node at `ownGH` from the instance's -/

section Move

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {TkW : Nat → Prop}
  {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node of `wc_main` inside `SFactsSt2` at `ownGH`** from the instance's `SFacts` at `c0N n` (`h`), its pc
and next pc free (`hf0`, `hfz`), each state at a cell of size `z` off `syscall` whose leaves are `z` bytes on
(`hstep`). -/
theorem nodeW_wcGH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {K : State → State → Prop} {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS
      (fun s => TkW (phH (pcOf s))) lbl s c) K L.exe L.endPc R F (c0N n)) {z : Nat}
    (hf0 : freeNH n.pc.toBitVec.toNat = true) (hfz : freeNH (n.pc + Int64.ofNat z).toBitVec.toNat = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n := by
  have hag := nodeAgreeWH (a := a) (n := c0N n) (exe := L.exe) (endPc := L.endPc) (R := R) (F := F) hlab hsite
    hf0 hfz fun s c ⟨h1, h2, h3, h4, σ, hA, hF, _, c', hJ⟩ => hstep s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  have h2 := Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Move

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.freeLabsH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.freeLabsH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.goodW_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.goodW_of_freeNH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.wcFactsWH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.wcFactsWH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.blkW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.blkW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.nodeW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.nodeW_wcGH
