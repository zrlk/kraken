/-
**`wc_main` from `.x20` to its `clone` inside `SFactsSt2` at wake.w's
global owned-words map `ownG`** (x86-64; twin of
`Spike/Lib/A64WakeWcSp4W.lean`): the `SFactsSt2` component of the
pre-spawn chain's `W` at `WcSp4W`'s nodes (`X64WakeWcSp4Seg`).

Each block and row is proved at a constant instance (`InstOk.const` of
`instOkW`, owned words `o`, no take phase, `X64Consumer.c0` for the source
control: the state facts do not read it) and moved to `ownG`, which is `o`
at every pc of the block and at its successors:

- `.x20` to the call (`x20A`, the tid store, `initCall`): `wc_main`'s range
  `[.x20, .x21)`, where `ownG` is `own2a (ph2a pc) = own2a 0`;
- `scc_rt_thread_init`'s entry (`nI`, its first instruction `pushq %rbp`)
  on a pool stack: `own2b (ph2b pc) = own2b 12 = own2a 0` (`own2a0_eq`);
- `.x21` to the `syscall` (`x21A`, the fence, `cloneLd`, the two flag rows,
  `nrB`): `[.x21, .stk)`, where `ownG` is `own2b (ph2b pc) = own2b 0`.

The pcs and phases are decided by the kernel at the canonical base (`hlab`).

Open premises of `wcSp4W_wcG` (none proved here; the dischargers are
the pre-spawn chain's `h1`, `X64WakeWcInv.H1Stmt`, at `WcMidW.sp4`, as on
AArch64):
- `hband : BandTi L R`: `wc_main`'s frame on a pool stack at the call
  (`%rsp = R.addr (-72)` past the `call`, `R.addr (-80)` past the callee's
  `pushq`): from main's frame facts (h1).
- `htidW`: the tid word `t + 56` mapped for writing, unmapped in private
  memory under `F`, off `own2a L a 0` (a runtime word of the second TCB):
  from the TCB in the pool (h1, as `wake_wc_sp4_segW`'s `htid`).

- `tiPush`, `wake_tiPush`: `scc_rt_thread_init`'s first instruction.
- `x20_facts`, `x21_facts`, `ti_facts`, `lab_x20`, `lab_x21`, `lab_ti`,
  `lab_site`, `okP_x20`, `okP_x21`: the pcs and phases at the canonical
  base.
- `own_x20`, `own_x21`, `own_ti`, `own2a0_eq`: `ownG` at the pcs; `BandTi`,
  `spPool_of`: the call on a pool stack.
- `agreeBlk`, `blk_c`, `blk_at`, `node_c`: the generic moves.
- `n20_wcG` … `nI_wcG` (before the call), `n21_wcG` … `nr_wcG` (the
  clone's), `wcCloneW_wcG`; `wcSp4W_wcG`: the result.

**Where this differs from AArch64**: offsets are bytes (`cellOff`, the
node rows of sizes `4`, `3`, `2`, `3`); there is no `hal`; the fence is
`mfence` (`nodeW_mfence_pre`; A64's `dmb`) and the clone's flags are two
`xorl` rows (`nodeW_fi_pre`), so `WcSp4W` has ten obligations (A64's seven:
its clone part is three nodes); `WcSp4W` carries the clone as one field
(`WcCloneW`, `wcCloneW_wcG`); the callee's entry is entered through a
one-cell block `pushq %rbp` at `oC` (the pushed return address at `-72`;
A64's `sub sp, sp, #48` at `oW`), so the band is `[-80, -72]` (A64's
`[-128, -80]`); the frame bounds are `R.lo ≤ -80`, `16 ≤ R.hi` (A64's
`-128`, `0`); `ownG` at the callee's entry is `own2b 12` directly (A64
moves it to `own2a 0` there; here `own2a0_eq` is used at the call's end).
-/
import Spike.Lib.X64WakeWcSp4Seg
import Spike.Lib.X64WakeWcPreWI

namespace Spike.Lib.X64.WakePh.WcSp4W

open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB codeT_eq code_field okPcOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts K0)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At AS SO Abs arun cellOff okBlk CodeAt bAddr mB eaddr_mB agrees_of_decls stDir)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.WakePh.WcSp4 (x20L x20A initCall x20A_ok initCall_ok x20A_run initCall_run wcN20p wcNI oC)
open Spike.Lib.X64.WakePh.WcClone (oW x21L x21A cloneLd nrB x21A_ok cloneLd_ok nrB_ok x21A_run cloneLd_run
  nrB_run wcN21 wcNf wcNa wcNd wcN10 wcNr WcCloneW)
open Spike.Lib.X64.WakePh.WcW (c0N c0N_cfacts blkW_mapC nodeW_mapC nodeW_mfence_pre)
open Spike.Lib.X64.Flow.WakeWc (WcSp4W aN kOf)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees exec_mfence op64)

/-! ## `scc_rt_thread_init`'s first instruction -/

/-- `scc_rt_thread_init`'s first instruction (`tiPro`'s first cell), from
the call node's offsets `oC`. -/
def tiPush : List (Directive × Nat) := (parse("pushq %rbp")).zip [1]

block_spec tiPush (-80) 16 oC tiPush

theorem wake_tiPush : blockAtB wakeCells "scc_rt_thread_init" 0 tiPush = true := by decide +kernel

/-! ## The pcs at the canonical base -/

/-- `.x20`'s 25 bytes: their values, `ph2a` `0`, off the sites. -/
theorem x20_facts : ∀ k < 25, (Int64.ofNat 4203410 + Int64.ofNat k).toBitVec.toNat = 4203410 + k ∧
    ph2aC (4203410 + k) = 0 ∧ okC (4203410 + k) = true := by decide +kernel

/-- `.x21`'s 47 bytes (to the `syscall`): their values, `ph2b` `0`, off the sites. -/
theorem x21_facts : ∀ k < 47, (Int64.ofNat 4203435 + Int64.ofNat k).toBitVec.toNat = 4203435 + k ∧
    ph2bC (4203435 + k) = 0 ∧ okC (4203435 + k) = true := by decide +kernel

/-- `scc_rt_thread_init`'s first two pcs: their values, `ph2b` `12`, the first off the sites. -/
theorem ti_facts : (Int64.ofNat 4199545 + Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat = 4199545 ∧
    (Int64.ofNat 4199545 + 1).toBitVec.toNat = 4199546 ∧ ph2bC 4199545 = 12 ∧ ph2bC 4199546 = 12 ∧
    okC 4199545 = true := by decide +kernel

/-- The take site at the canonical base. -/
theorem site_toNat : (Int64.ofNat 4200277).toBitVec.toNat = 4200277 := rfl

theorem snd_of {s : State} {m : MachineData} {p : Int64} (h : s.st = (m, p)) : s.st.2 = p := by rw [h]

/-- A block of wakeCells in a layout of them. -/
theorem onProg {L : RuntimeLayout} (hp : L.prog = wakeCells) {l : Label} {k : Nat} {blk : List (Directive × Nat)}
    (h : blockAtB wakeCells l k blk = true) : blockAtB L.prog l k blk = true := by
  rw [hp]; exact h

variable {L : RuntimeLayout} {a : BitVec 64}

theorem lab_x20 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label x20L = Int64.ofNat 4203410 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_x21 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label x21L = Int64.ofNat 4203435 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_ti (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label "scc_rt_thread_init" = Int64.ofNat 4199545 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_site (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- `okPc` at `.x20`'s pcs. -/
theorem okP_x20 (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {j : Nat} (hj : j < 25) :
    okPcOf lo wakeCells L.Λ ((_root_.Executable.labels L.exe).label x20L + Int64.ofNat j).toBitVec.toNat = true := by
  rw [okPc_eq hΛ, lab_x20 hlab, (x20_facts j hj).1]; exact (x20_facts j hj).2.2

/-- `okPc` at `.x21`'s pcs. -/
theorem okP_x21 (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {j : Nat} (hj : j < 47) :
    okPcOf lo wakeCells L.Λ ((_root_.Executable.labels L.exe).label x21L + Int64.ofNat j).toBitVec.toNat = true := by
  rw [okPc_eq hΛ, lab_x21 hlab, (x21_facts j hj).1]; exact (x21_facts j hj).2.2

/-! ## `ownG` at the pcs -/

/-- The two second instances' owned words at the second switch. -/
theorem own2a0_eq (L : RuntimeLayout) (a : BitVec 64) : own2a L a 0 = own2b L a 12 := by
  have h := own2a_own2b_ph L a
  have h1 : ph2a 4203430 = 0 := by rw [ph2a_eq]; unfold ph2aC; rw [threadInit2_ph.1]
  have h2 : ph2b 4199545 = 12 := by rw [ph2b_eq]; unfold ph2bC; rw [threadInit2_ph.2.2]
  rwa [h1, h2] at h

/-- **`ownG` at `.x20`'s pcs** is `own2a L a 0`. -/
theorem own_x20 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 25) (hs : s.st.2 = (_root_.Executable.labels L.exe).label x20L + Int64.ofNat k) :
    ownG L a s = own2a L a 0 := by
  have hp : pcOf s = 4203410 + k := by unfold pcOf; rw [hs, lab_x20 hlab]; exact (x20_facts k hk).1
  obtain ⟨-, -, -, -, e5, e6, -, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2a L s := .inr (.inl (by unfold inPc; rw [e5, e6, hp]; omega))
  rw [ownG_2a hlab hg, hp, ph2a_eq, (x20_facts k hk).2.1]

/-- **`ownG` at `.x21`'s pcs to the `syscall`** is `own2b L a 0`. -/
theorem own_x21 (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 47) (hs : s.st.2 = (_root_.Executable.labels L.exe).label x21L + Int64.ofNat k) :
    ownG L a s = own2b L a 0 := by
  have hp : pcOf s = 4203435 + k := by unfold pcOf; rw [hs, lab_x21 hlab]; exact (x21_facts k hk).1
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inr (.inl (by unfold inPc; rw [e6, e7, hp]; omega))
  rw [ownG_2b hlab hg, hp, ph2b_eq, (x21_facts k hk).2.1]

/-- **`ownG` at `scc_rt_thread_init`'s first two pcs on a pool stack** is
`own2b L a 12`. -/
theorem own_ti (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : pcOf s = 4199545 ∨ pcOf s = 4199546) (hsp : spPool L s) : ownG L a s = own2b L a 12 := by
  obtain ⟨-, -, e3, e4, -, -, -, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inl ⟨by unfold inPc; rw [e3, e4]; omega, hsp⟩
  rw [ownG_2b hlab hg, ph2b_eq]
  rcases hp with hp | hp <;> rw [hp]
  · rw [ti_facts.2.2.1]
  · rw [ti_facts.2.2.2.1]

/-- **`wc_main`'s frame on a pool stack at the call**: `%rsp` past the
`call` (`R.addr (-72)`) and past the callee's `pushq` (`R.addr (-80)`) in
`(pool.lo, pool.lo + pool.size]`. -/
def BandTi (L : RuntimeLayout) (R : Spike.Lib.Region) : Prop :=
  ∀ k, -80 ≤ k → k ≤ -72 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- `spPool` at `%rsp = R.addr k` in the band. -/
theorem spPool_of {R : Spike.Lib.Region} (hb : BandTi L R) {s : State} {k : Int} (h1 : -80 ≤ k) (h2 : k ≤ -72)
    (hs : s.st.1.regs.rsp.toBitVec = R.addr k) : spPool L s := by
  unfold spPool; rw [hs]; exact hb k h1 h2

/-! ## The generic moves -/

section Moves

variable {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`ownG` agrees with a constant `o` on a covered block**: at its pcs
(`hQ`) and at the pc its run ends at (`hlast`), its pcs off the take site. -/
theorem agreeBlk (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ 4200277)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).so m (arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → ownG L a s = o)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨n.pc, n.o, σ⟩).so m (arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownG L a s = o) :
    BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo' hhi
    (fun x hx k hk => by
      rw [hsite, lab_site hlab, site_toNat] at hx
      cases hx; exact hns k hk)
    (fun σ c hJ k hk s m hA _ _ hs => hQ σ c hJ k hk s m hA hs)
    (fun σ c hJ k hk s m hA _ _ hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.X64.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hlast σ c hJ s m hA hs)

/-- **A covered `ret`-free block of wakeCells inside `SFactsSt2` at `ownG`**,
at the outside move of any range `rS`: `blkW_pre` at the constant instance
`o` (no take phase), the source control replaced by `X64Consumer.c0`, moved
to `ownG` where it agrees with `o` (`hag`). -/
theorem blk_c (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (o : List (Loc × Val)) {Λ : Scc.Sem.Layout} {rS : Range} {n : ND} {blk : List (Directive × Nat)} {l : Label}
    {k : Nat} {blo bhi : Int} (hb : blockAtB L.prog l k blk = true)
    (he : (_root_.Executable.labels L.exe).label l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hcl : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hag : BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have h := Spike.Lib.X64.Rt.blkW_pre (InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) o False)
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (n := c0N n) hb he hok hR hlo' hhi c0N_cfacts
    (ra := 0) (dead := fun _ => false)
    (by rw [he]; exact Tcb2CallW.blkPh_const_of hcl (fun j hj => by rw [okPc_eq hΛ]; exact hpc j hj))
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hag' : BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) blk := by
    intro s σ c a1 a2 a3 a4 a5 a6 hJ k hk m a8 a9
    obtain ⟨-, c', hJ'⟩ := hJ
    exact hag s σ c' a1 a2 a3 a4 a5 a6 hJ' k hk m a8 a9
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Tcb2W.blkW_toSt2 h) hag'
  exact blkW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **A block in a range of `wc_main` where `ownG` is `o`** (`hown`: at
`l + k` for `k < N`, the range's pcs off the sites `hf` and off the take
site `hns`): `blk_c` and `agreeBlk`, the block's cells inside the range
(`hco`), its end's `ownG` `hlast`. -/
theorem blk_at (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (o : List (Loc × Val)) {Λ : Scc.Sem.Layout} {rS : Range} {l : Label} {base N off : Nat} {n : ND}
    {blk : List (Directive × Nat)} {blo bhi : Int}
    (hl : (_root_.Executable.labels L.exe).label l = Int64.ofNat base)
    (hf : ∀ k < N, (Int64.ofNat base + Int64.ofNat k).toBitVec.toNat = base + k ∧ okC (base + k) = true)
    (hns : 4200277 < base ∨ base + N ≤ 4200277)
    (hown : ∀ (s : State) (k : Nat), k < N → s.st.2 = (_root_.Executable.labels L.exe).label l + Int64.ofNat k →
      ownG L a s = o)
    (hb : blockAtB wakeCells l off blk = true)
    (he : (_root_.Executable.labels L.exe).label l + Int64.ofNat off = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hcl : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hco : ∀ k < blk.length, off + cellOff blk k < N)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨n.pc, n.o, σ⟩).so m (arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownG L a s = o) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have hpcE : ∀ k, n.pc + Int64.ofNat (cellOff blk k) =
      (_root_.Executable.labels L.exe).label l + Int64.ofNat (off + cellOff blk k) := fun k => by
    rw [← he, ofNat_add']
  refine blk_c hp hlo hΛ hsite o (onProg hp hb) he hok hR hlo' hhi hcl hnr (fun j hj => ?_) ?_
  · have h := hf _ (hco j hj)
    rw [hpcE, hl, h.1]; exact h.2
  refine agreeBlk hlab hsite (code_field L.lays rfl (onProg hp hb) he) hok hR hlo' hhi (fun k hk => ?_)
    (fun σ c _ k hk s m _ hs => hown s _ (hco k hk) (by rw [snd_of hs, hpcE])) hlast
  have h := hco k hk
  rw [hpcE, hl, (hf _ h).1]; omega

/-- **A node of wakeCells inside `SFactsSt2` at `ownG`** from the constant
instance's `SFacts` at `c0N n` (`h`), `ownG` `o` at its pc and the next
(`h0`, `hz`), its pc off the take site, each state at a `z`-byte cell off
`syscall` whose leaves are `z` bytes on (`hstep`). -/
theorem node_c (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} {K : State → State → Prop}
    {n : ND} {z : Nat}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.X64.PhRec.μ L) (fun _ => o) rS (fun _ => False) lbl s c) K
      L.exe L.endPc R F (c0N n))
    (hns : n.pc.toBitVec.toNat ≠ 4200277)
    (h0 : ∀ s : State, s.st.2 = n.pc → ownG L a s = o)
    (hz : ∀ s : State, s.st.2 = n.pc + Int64.ofNat z → ownG L a s = o)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) := by
    rintro s c ⟨h1, h2, h3, h4', σ, hA, hF, -, c', hJ⟩
    have hpc : s.st.2 = n.pc := h4'
    obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c' ⟨h1, h2, h3, hpc, σ, hA, hF, hJ⟩
    have hns' : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pcOf s ≠ x := by
      intro x hx; rw [hsite, lab_site hlab, site_toNat] at hx; cases hx; unfold pcOf; rw [hpc]; exact hns
    exact ⟨⟨h0 s hpc, fun s' hs => hz s' (by rw [WcW.succ_pc hc hd hex hl hns' hs, hpc])⟩, fun _ h => h⟩
  have h2 := Tcb2W.nodeW_ownCongr2 (Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Moves

/-- The blocks' and rows' code facts. -/
theorem sp4In : blockAtB wakeCells x20L 0 x20A = true ∧
    blockAtB wakeCells x20L 12 [(stDir .rcx 56 .rax, 4)] = true ∧ blockAtB wakeCells x20L 16 initCall = true ∧
    blockAtB wakeCells x21L 0 x21A = true ∧ blockAtB wakeCells x21L 12 [(op64 .mfence, 3)] = true ∧
    blockAtB wakeCells x21L 15 cloneLd = true ∧
    blockAtB wakeCells x21L 36 [(Spike.Lib.X64.FI.toDir (.xor_rr32_self .rdx), 2)] = true ∧
    blockAtB wakeCells x21L 38 [(Spike.Lib.X64.FI.toDir (.xor_rr32_self .r10), 3)] = true ∧
    blockAtB wakeCells x21L 41 nrB = true := by decide +kernel

/-- The blocks' cells inside their ranges. -/
theorem cells_in : (∀ k < x20A.length, 0 + cellOff x20A k < 25) ∧
    (∀ k < initCall.length, 16 + cellOff initCall k < 25) ∧ (∀ k < x21A.length, 0 + cellOff x21A k < 47) ∧
    (∀ k < cloneLd.length, 15 + cellOff cloneLd k < 47) ∧ (∀ k < nrB.length, 41 + cellOff nrB k < 47) := by
  decide +kernel

/-! ## The obligations -/

section Obl

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {c0 : Spike.Lib.Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
include hp hlo hΛ hlab hsite

/-- **`.x20`'s block** (`x20A`). -/
theorem n20_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n20) x20A :=
  blk_at hp hlo hΛ hlab hsite (own2a L a 0) (lab_x20 hlab)
    (fun k hk => ⟨(x20_facts k hk).1, (x20_facts k hk).2.2⟩) (by decide) (fun s k hk hs => own_x20 hlab hk hs)
    sp4In.1 (ofNat_zero' _) x20A_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_in.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label x20A
        ⟨(_root_.Executable.labels L.exe).label x20L, oW, σ⟩).pc at e
      rw [x20A_run] at e
      exact own_x20 hlab (k := 12) (by decide) e)

/-- **The tid store** (a row): `t + 56` mapped for writing, unmapped in
private memory under `F`, off `own2a L a 0` (`htidW`). -/
theorem n20s_wcG (a : BitVec 64)
    (htidW : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n20s) := by
  obtain ⟨hmw, hun, hno⟩ := htidW
  have hI := InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (own2a L a 0) False
  have hb := onProg hp sp4In.2.1
  refine node_c hlab hsite (o := own2a L a 0) (z := 4)
    (Spike.Lib.X64.Rt.nodeW_st_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F)
      (ownOf := fun _ => own2a L a 0) (fun _ => rfl) hb (p := L.lab x20L + Int64.ofNat 12) rfl rfl c0N_cfacts
      (okP_x20 hΛ hlab (by decide)) (fun _ _ h => h) rfl ?_ hmw hun (fun _ w => hno w)) ?_
    (fun s hs => own_x20 hlab (k := 12) (by decide) hs)
    (fun s hs => own_x20 hlab (k := 12 + 4) (by decide) (by rw [hs]; exact (ofNat_add' _ 12 4).symm)) ?_
  · rintro σ c ⟨-, c', ⟨⟨-, hcx, -⟩, -⟩⟩
    unfold Spike.Lib.X64.bAddr; rw [hcx]; rfl
  · show ((_root_.Executable.labels L.exe).label x20L + Int64.ofNat 12).toBitVec.toNat ≠ _
    rw [lab_x20 hlab, (x20_facts 12 (by decide)).1]; omega
  · rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, ⟨-, hcx, -⟩, -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb (p := L.lab x20L + Int64.ofNat 12) rfl h1 h2 h4'
    have ha' : eaddr s 4 (mB .rcx 56) = t + 56#64 :=
      (eaddr_mB s 4 .rcx 56).trans (by rw [hA.regs, hcx]; rfl)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

/-- **The call block** (`initCall`), its end at `scc_rt_thread_init` on a
pool stack (`hband`). -/
theorem n20p_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi) (hband : BandTi L R) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n20p) initCall :=
  blk_at hp hlo hΛ hlab hsite (own2a L a 0) (lab_x20 hlab)
    (fun k hk => ⟨(x20_facts k hk).1, (x20_facts k hk).2.2⟩) (by decide) (fun s k hk hs => own_x20 hlab hk hs)
    sp4In.2.2.1 rfl initCall_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_in.2.1
    (fun σ c _ s m' hA hs => by
      change Abs R (arun (_root_.Executable.labels L.exe).label initCall
        ⟨(_root_.Executable.labels L.exe).label x20L + 16, oW, σ⟩).so m' _ at hA
      change s.st = (m', (arun (_root_.Executable.labels L.exe).label initCall
        ⟨(_root_.Executable.labels L.exe).label x20L + 16, oW, σ⟩).pc) at hs
      rw [initCall_run] at hs hA
      have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
      have hm : s.st.1 = m' := by rw [hs]
      refine (own_ti hlab (.inl ?_) (spPool_of hband (k := -72) (by decide) (by decide) ?_)).trans
        (own2a0_eq L a).symm
      · unfold pcOf; rw [snd_of hs, lab_ti hlab]; rfl
      · rw [hm]; exact hsp)

/-- **`scc_rt_thread_init`'s entry** (the call node), on a pool stack
(`hband`): the first state of its first instruction's block. -/
theorem nI_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) (hband : BandTi L R) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNI L.lab c0 t cA m fr) := by
  have eT := lab_ti hlab (L := L)
  have hlen : tiPush.length = 1 := by decide
  have hb := onProg hp wake_tiPush
  refine Spike.Lib.LowerX64.BlkW.nodeW (blk := tiPush) ?_ (by decide)
  refine blk_c hp hlo hΛ hsite (own2b L a 12) hb (ofNat_zero' _) tiPush_ok hR hRlo hhi (by decide +kernel)
    (by decide +kernel) (fun j hj => ?_) ?_
  · obtain rfl : j = 0 := by omega
    show okC (((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat) = true
    rw [eT, ti_facts.1]; exact ti_facts.2.2.2.2
  refine agreeBlk hlab hsite (code_field L.lays rfl hb (ofNat_zero' _)) tiPush_ok hR hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m' hA hs => ?_) (fun σ c _ s m' hA hs => ?_)
  · obtain rfl : k = 0 := by omega
    show ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat ≠ _
    rw [eT, ti_facts.1]; omega
  · obtain rfl : k = 0 := by omega
    have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
    have hm : s.st.1 = m' := by rw [hs]
    refine own_ti hlab (.inl ?_) (spPool_of hband (k := -72) (by decide) (by decide) ?_)
    · unfold pcOf; rw [snd_of hs]
      show ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
        Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat = _
      rw [eT]; exact ti_facts.1
    · rw [hm, hsp]; rfl
  · change Abs R (arun (_root_.Executable.labels L.exe).label tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oC, σ⟩).so m' _ at hA
    change s.st = (m', (arun (_root_.Executable.labels L.exe).label tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oC, σ⟩).pc) at hs
    rw [tiPush_run] at hs hA
    have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
    have hm : s.st.1 = m' := by rw [hs]
    refine own_ti hlab (.inr ?_) (spPool_of hband (k := -80) (by decide) (by decide) (by rw [hm]; exact hsp))
    unfold pcOf; rw [snd_of hs, eT]; exact ti_facts.2.1

/-! ### The clone's, at any stack top `k` and frame `F` -/

variable {k : BitVec 64}

/-- **`.x21`'s block** (`x21A`). -/
theorem n21_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN21 L.lab c0 t k cA m fr) x21A :=
  blk_at hp hlo hΛ hlab hsite (own2b L a 0) (lab_x21 hlab)
    (fun k hk => ⟨(x21_facts k hk).1, (x21_facts k hk).2.2⟩) (by decide) (fun s k hk hs => own_x21 hlab hk hs)
    sp4In.2.2.2.1 (ofNat_zero' _) x21A_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_in.2.2.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label x21A
        ⟨(_root_.Executable.labels L.exe).label x21L, oW, σ⟩).pc at e
      rw [x21A_run] at e
      exact own_x21 hlab (k := 12) (by decide) e)

/-- **The fence** (a row, `mfence`). -/
theorem nf_wcG (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNf L.lab c0 t k cA m fr) := by
  have hI := InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (own2b L a 0) False
  have hb := onProg hp sp4In.2.2.2.2.1
  refine node_c hlab hsite (o := own2b L a 0) (z := 3)
    (nodeW_mfence_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) hb
      (p := L.lab x21L + Int64.ofNat 12) rfl rfl c0N_cfacts (okP_x21 hΛ hlab (by decide)) (fun _ _ h => h) rfl) ?_
    (fun s hs => own_x21 hlab (k := 12) (by decide) hs)
    (fun s hs => own_x21 hlab (k := 12 + 3) (by decide) (by rw [hs]; exact (ofNat_add' _ 12 3).symm)) ?_
  · show ((_root_.Executable.labels L.exe).label x21L + Int64.ofNat 12).toBitVec.toNat ≠ _
    rw [lab_x21 hlab, (x21_facts 12 (by decide)).1]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb (p := L.lab x21L + Int64.ofNat 12) rfl h1 h2 h4'
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_mfence hc, fun s' hu => ?_⟩
    obtain ⟨_, hu⟩ := hu
    simp only [TreeLeaf] at hu
    subst hu; rfl

/-- **The clone's loads** (`cloneLd`). -/
theorem na_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNa L.lab c0 t k cA m fr) cloneLd :=
  blk_at hp hlo hΛ hlab hsite (own2b L a 0) (lab_x21 hlab)
    (fun k hk => ⟨(x21_facts k hk).1, (x21_facts k hk).2.2⟩) (by decide) (fun s k hk hs => own_x21 hlab hk hs)
    sp4In.2.2.2.2.2.1 rfl cloneLd_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_in.2.2.2.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label cloneLd
        ⟨(_root_.Executable.labels L.exe).label x21L + 15, oW, σ⟩).pc at e
      rw [cloneLd_run] at e
      exact own_x21 hlab (k := 15 + 21) (by decide) (by rw [e]; exact (ofNat_add' _ 15 21).symm))

/-- A node at an `xorl` row of `.x21` (`z` bytes at `.x21 + j`) inside
`SFactsSt2` at `ownG`. -/
theorem xor_wcG (a : BitVec 64) {r : Reg64} {j z : Nat} {n : ND}
    (hb : blockAtB wakeCells x21L j [(Spike.Lib.X64.FI.toDir (.xor_rr32_self r), z)] = true)
    (hpc : n.pc = L.lab x21L + Int64.ofNat j) (hj : j + z < 47)
    (hC : ∀ σ c, (c0N n).J σ c → CFacts Λ (fun _ => none) c) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hI := InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) (own2b L a 0) False
  have hb' := onProg hp hb
  refine node_c hlab hsite (o := own2b L a 0) (z := z)
    (Spike.Lib.X64.Rt.nodeW_fi_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) hb' rfl hpc hC
      (okP_x21 hΛ hlab (by omega)) (fun _ _ h => h) rfl) ?_
    (fun s hs => own_x21 hlab (k := j) (by omega) (by rw [hs, hpc]))
    (fun s hs => own_x21 hlab (k := j + z) hj (by rw [hs, hpc, ofNat_add'])) ?_
  · rw [hpc]; show ((_root_.Executable.labels L.exe).label x21L + Int64.ofNat j).toBitVec.toNat ≠ _
    rw [lab_x21 hlab, (x21_facts j (by omega)).1]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb' rfl h1 h2 (h4'.trans hpc)
    obtain ⟨tr, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
    refine ⟨_, _, hc, fun w w' h => (by cases h), hex, fun s' hu => ?_⟩
    obtain ⟨_, rfl⟩ := Tcb2W.silent_leaf hst hu; rfl

/-- **`xorl %edx, %edx`** (a row). -/
theorem nd_wcG (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNd L.lab c0 t k cA m fr) :=
  xor_wcG hp hlo hΛ hlab hsite a sp4In.2.2.2.2.2.2.1 rfl (by decide) c0N_cfacts

/-- **`xorl %r10d, %r10d`** (a row). -/
theorem n10_wcG (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN10 L.lab c0 t k cA m fr) :=
  xor_wcG hp hlo hΛ hlab hsite a sp4In.2.2.2.2.2.2.2.1 rfl (by decide) c0N_cfacts

/-- **The call number** (`nrB`), to the `syscall`. -/
theorem nr_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNr L.lab c0 t k cA m fr) nrB :=
  blk_at hp hlo hΛ hlab hsite (own2b L a 0) (lab_x21 hlab)
    (fun k hk => ⟨(x21_facts k hk).1, (x21_facts k hk).2.2⟩) (by decide) (fun s k hk hs => own_x21 hlab hk hs)
    sp4In.2.2.2.2.2.2.2.2 rfl nrB_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_in.2.2.2.2
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label nrB
        ⟨(_root_.Executable.labels L.exe).label x21L + 41, oW, σ⟩).pc at e
      rw [nrB_run] at e
      exact own_x21 hlab (k := 41 + 5) (by decide) (by rw [e]; exact (ofNat_add' _ 41 5).symm))

/-- **`WcCloneW` at `SFactsSt2`/`ownG`**: `.x21` to the `syscall`, at any
stack top and frame. -/
theorem wcCloneW_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    WcCloneW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 t k cA m fr :=
  ⟨n21_wcG hp hlo hΛ hlab hsite a hR hRlo hhi, nf_wcG hp hlo hΛ hlab hsite a,
    na_wcG hp hlo hΛ hlab hsite a hR hRlo hhi, nd_wcG hp hlo hΛ hlab hsite a, n10_wcG hp hlo hΛ hlab hsite a,
    nr_wcG hp hlo hΛ hlab hsite a hR hRlo hhi⟩

/-- **`WcSp4W` at `SFactsSt2`/`ownG`**, at the outside move of any range
`rS`: `wc_main`'s frame on a pool stack at the call (`hband`) and the tid
word's facts (`htidW`), both from `h1` (`X64WakeWcInv.H1Stmt`, at
`WcMidW.sp4`: main's frame facts and the second TCB in the pool). -/
theorem wcSp4W_wcG (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -80) (hhi : 16 ≤ R.hi) {F₂ : MachineData → Prop}
    (hband : BandTi L R)
    (htidW : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0) :
    WcSp4W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F F₂ c0 t cA m fr :=
  { n20 := n20_wcG hp hlo hΛ hlab hsite a hR (by omega) hhi
    n20s := n20s_wcG hp hlo hΛ hlab hsite a htidW
    n20p := n20p_wcG hp hlo hΛ hlab hsite a hR (by omega) hhi hband
    nI := nI_wcG hp hlo hΛ hlab hsite a hR hRlo hhi hband
    clone := wcCloneW_wcG hp hlo hΛ hlab hsite a hR (by omega) hhi }

end Obl

end Spike.Lib.X64.WakePh.WcSp4W

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.wake_tiPush' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.wake_tiPush
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.x20_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.x20_facts
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.x21_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.x21_facts
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.ti_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.ti_facts
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.sp4In' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.sp4In
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.cells_in' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.cells_in
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.own2a0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.own2a0_eq
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.blk_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.blk_at
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.node_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.node_c
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.wcCloneW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.wcCloneW_wcG
/-- info: 'Spike.Lib.X64.WakePh.WcSp4W.wcSp4W_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4W.wcSp4W_wcG
