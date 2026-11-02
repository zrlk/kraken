/-
**hello.w's `wc_main` from `.x24` to its `clone` inside `SFactsSt2` at `ownGH`** (x86-64; the twin of
`Spike/Lib/A64HelloWcSp4W.lean`, at helloCells the twin of `Spike/Lib/X64WakeWcSp4W.lean`): the `SFactsSt2`
component of the pre-spawn chain's `W` at `HelloWc.WcSp4WH`'s nodes (`X64HelloWcSp3`), `scc_rt_thread_init`'s
entry (`wcNIH`), and `WcSp6.WcSp6W`'s (`X64HelloWcSp6Seg`), in `wc_main`'s 128-byte frame (`oWH`).

Each block and row is proved at a constant instance (`InstOk.const` of `instOkH`, owned words `o`, no take phase,
`X64Consumer.c0` for the source control) and moved to `ownGH`, which is `o` at every pc of the block and at its
successors:

- `.x24` to the call (`sp4AH`, the tid store, `initCallH`): `wc_main`'s range `[.x24, .x25)`, where `ownGH` is
  `own2aH (ph2aH pc) = own2aH 0`;
- `scc_rt_thread_init`'s entry (`nIH_wcGH`, its first instruction `pushq %rbp`) on a pool stack:
  `own2bH (ph2bH pc) = own2bH 12 = own2aH 0` (`own2a0_eqH`);
- `.x25` to the `syscall` (`sp6AH`, the fence, `cloneLdH`, the two flag rows, `nrB`): `[.x25, .stk)`, where
  `ownGH` is `own2bH (ph2bH pc) = own2bH 0`.

The pcs and phases are decided by the kernel at the canonical base (`hlab`).

Open premises (as wake's): `hband : BandTiH L R` (`wc_main`'s frame on a pool stack at the call, `%rsp =
R.addr (-136)` past the `call`, `R.addr (-144)` past the callee's `pushq`), and `htidW` (the tid word `t + 56`
mapped for writing, unmapped in private memory under `F`, off `own2aH L a 0`).

- `tiPushH` (`block_spec` of wake's `tiPush` at `oCH`), `hello_tiPush`: `scc_rt_thread_init`'s first
  instruction in hello's frame.
- `x24_factsH`, `x25_factsH`, `ti_factsH`, `site_toNatH`, `lab_x24H`, `lab_x25H`, `lab_tiH`, `lab_siteH`,
  `okP_x24H`, `okP_x25H`: the pcs and phases at the canonical base.
- `own_x24H`, `own_x25H`, `own_tiH`, `own2a0_eqH`: `ownGH` at the pcs; `BandTiH`, `spPool_ofH`: the call on a
  pool stack.
- `onProgH`, `agreeBlkH`, `blk_cH`, `blk_atH`, `node_cH`: the generic moves to `ownGH`; `sp4InH`, `cells_inH`:
  the code facts.
- `n4_wcGH`, `n4s_wcGH`, `n5_wcGH`, `nIH_wcGH` (before the call), `n6_wcGH`, `n6f_wcGH`, `n6a_wcGH`, `xor_wcGH`,
  `nd_wcGH`, `n10_wcGH`, `nr_wcGH` (the clone's): the obligations; `wcSp4W_wcGH`, `wcSp6W_wcGH`: the results.

## Differences from the AArch64 version

- Offsets are bytes (`cellOff`); there is no `hal`. The frame bounds are `R.lo ≤ -128` (`-136` with the call,
  `-144` at the callee's entry), `16 ≤ R.hi` (A64's `-144`/`-192`, `0`).
- The callee is entered through a one-cell block `pushq %rbp` at `oCH` (the return address at `-136`;
  A64's `sub sp, sp, #48` at `oWH`), so the band is `[-144, -136]` (A64's `[-192, -144]`).
- The fence is `mfence` (`nodeW_mfence_pre`; A64's `dmb`) and the clone's arguments are a load block, two `xorl`
  rows (`nodeW_fi_pre`) and the call number, so `WcSp6W` has six obligations (A64's three).
- As in x86-64 wake, the moves are wake's program-independent `Tcb2W`/`WcW` lemmas; `ownGH` at the callee's entry
  is `own2bH 12` directly and `own2a0_eqH` is used at the call's end. `nIH_wcGH` and the pieces of the clone part
  are separate theorems, as `WcSp4WH` (`X64HelloWcSp3`) has no `nI` field.
-/
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloWcSp6Seg
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64HelloPh
import Spike.Lib.X64WakeWcSp4W

namespace Spike.Lib.X64.HelloPh.WcSp4W

open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (blockAtB codeT_eq code_field okPcOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl CFacts SFacts K0)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At AS SO Abs arun cellOff okBlk CodeAt bAddr mB eaddr_mB agrees_of_decls stDir)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh (inPc spPool)
open Spike.Lib.X64.WakePh.WcSp4W (tiPush snd_of)
open Spike.Lib.X64.WakePh.WcClone (nrB)
open Spike.Lib.X64.HelloPh.WcSp6 (oWH x25L sp6AH cloneLdH sp6AH_ok cloneLdH_ok nrBH_ok sp6AH_run cloneLdH_run
  nrBH_run wcN6H wcN6fH wcN6aH wcNdH wcN10H wcNrH WcSp6W)
open Spike.Lib.X64.Flow.HelloWc (oCH x24L aNH wcNIH sp4AH initCallH sp4AH_ok initCallH_ok sp4AH_run initCallH_run
  WcSp4WH)
open Spike.Lib.X64.WakePh.WcW (c0N c0N_cfacts blkW_mapC nodeW_mapC nodeW_mfence_pre)
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_store_agrees exec_mfence op64)

/-! ## `scc_rt_thread_init`'s first instruction -/

-- `scc_rt_thread_init`'s first instruction (wake's `tiPush`) from hello's call node's offsets `oCH` (the return
-- address at `-136`).
block_spec tiPushH (-144) 16 oCH tiPush

theorem hello_tiPush : blockAtB helloCells "scc_rt_thread_init" 0 tiPush = true := by decide +kernel

/-! ## The pcs at the canonical base -/

/-- `.x24`'s 25 bytes: their values, `ph2aH` `0`, off the sites. -/
theorem x24_factsH : ∀ k < 25, (Int64.ofNat 4203749 + Int64.ofNat k).toBitVec.toNat = 4203749 + k ∧
    ph2aHC (4203749 + k) = 0 ∧ okC (4203749 + k) = true := by decide +kernel

/-- `.x25`'s 95 bytes (to the `syscall`): their values, `ph2bH` `0`, off the sites. -/
theorem x25_factsH : ∀ k < 95, (Int64.ofNat 4203774 + Int64.ofNat k).toBitVec.toNat = 4203774 + k ∧
    ph2bHC (4203774 + k) = 0 ∧ okC (4203774 + k) = true := by decide +kernel

/-- `scc_rt_thread_init`'s first two pcs: their values, `ph2bH` `12`, the first off the sites. -/
theorem ti_factsH : (Int64.ofNat 4199582 + Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat = 4199582 ∧
    (Int64.ofNat 4199582 + 1).toBitVec.toNat = 4199583 ∧ ph2bHC 4199582 = 12 ∧ ph2bHC 4199583 = 12 ∧
    okC 4199582 = true := by decide +kernel

/-- The take site at the canonical base. -/
theorem site_toNatH : (Int64.ofNat 4200314).toBitVec.toNat = 4200314 := rfl

/-- A block of helloCells in a layout of them. -/
theorem onProgH {L : RuntimeLayout} (hp : L.prog = helloCells) {l : Label} {k : Nat} {blk : List (Directive × Nat)}
    (h : blockAtB helloCells l k blk = true) : blockAtB L.prog l k blk = true := by
  rw [hp]; exact h

variable {L : RuntimeLayout} {a : BitVec 64}

theorem lab_x24H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label x24L = Int64.ofNat 4203749 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_x25H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label x25L = Int64.ofNat 4203774 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_tiH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label "scc_rt_thread_init" = Int64.ofNat 4199582 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_siteH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- `okPc` at `.x24`'s pcs. -/
theorem okP_x24H (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {j : Nat} (hj : j < 25) :
    okPcOf lo helloCells L.Λ ((_root_.Executable.labels L.exe).label x24L + Int64.ofNat j).toBitVec.toNat = true := by
  rw [okPc_eq hΛ, lab_x24H hlab, (x24_factsH j hj).1]; exact (x24_factsH j hj).2.2

/-- `okPc` at `.x25`'s pcs. -/
theorem okP_x25H (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {j : Nat} (hj : j < 95) :
    okPcOf lo helloCells L.Λ ((_root_.Executable.labels L.exe).label x25L + Int64.ofNat j).toBitVec.toNat = true := by
  rw [okPc_eq hΛ, lab_x25H hlab, (x25_factsH j hj).1]; exact (x25_factsH j hj).2.2

/-! ## `ownGH` at the pcs -/

/-- The two second instances' owned words at the second switch. -/
theorem own2a0_eqH (L : RuntimeLayout) (a : BitVec 64) : own2aH L a 0 = own2bH L a 12 :=
  (own2aH_mod4 L a 16).trans (own2a_own2bH L a)

/-- **`ownGH` at `.x24`'s pcs** is `own2aH L a 0`. -/
theorem own_x24H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 25) (hs : s.st.2 = (_root_.Executable.labels L.exe).label x24L + Int64.ofNat k) :
    ownGH L a s = own2aH L a 0 := by
  have hp : pcOf s = 4203749 + k := by unfold pcOf; rw [hs, lab_x24H hlab]; exact (x24_factsH k hk).1
  obtain ⟨-, -, -, -, e5, e6, -, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2aH L s := .inr (.inl (by unfold inPc; rw [e5, e6, hp]; omega))
  rw [ownGH_2a hlab hg, hp, ph2aH_eq, (x24_factsH k hk).2.1]

/-- **`ownGH` at `.x25`'s pcs to the `syscall`** is `own2bH L a 0`. -/
theorem own_x25H (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 95) (hs : s.st.2 = (_root_.Executable.labels L.exe).label x25L + Int64.ofNat k) :
    ownGH L a s = own2bH L a 0 := by
  have hp : pcOf s = 4203774 + k := by unfold pcOf; rw [hs, lab_x25H hlab]; exact (x25_factsH k hk).1
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2bH L s := .inr (.inl (by unfold inPc; rw [e6, e7, hp]; omega))
  rw [ownGH_2b hlab hg, hp, ph2bH_eq, (x25_factsH k hk).2.1]

/-- **`ownGH` at `scc_rt_thread_init`'s first two pcs on a pool stack** is
`own2bH L a 12`. -/
theorem own_tiH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : pcOf s = 4199582 ∨ pcOf s = 4199583) (hsp : spPool L s) : ownGH L a s = own2bH L a 12 := by
  obtain ⟨-, -, e3, e4, -, -, -, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2bH L s := .inl ⟨by unfold inPc; rw [e3, e4]; omega, hsp⟩
  rw [ownGH_2b hlab hg, ph2bH_eq]
  rcases hp with hp | hp <;> rw [hp]
  · rw [ti_factsH.2.2.1]
  · rw [ti_factsH.2.2.2.1]

/-- **`wc_main`'s frame on a pool stack at the call**: `%rsp` past the
`call` (`R.addr (-136)`) and past the callee's `pushq` (`R.addr (-144)`) in
`(pool.lo, pool.lo + pool.size]`. -/
def BandTiH (L : RuntimeLayout) (R : Spike.Lib.Region) : Prop :=
  ∀ k, -144 ≤ k → k ≤ -136 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- `spPool` at `%rsp = R.addr k` in the band. -/
theorem spPool_ofH {R : Spike.Lib.Region} (hb : BandTiH L R) {s : State} {k : Int} (h1 : -144 ≤ k) (h2 : k ≤ -136)
    (hs : s.st.1.regs.rsp.toBitVec = R.addr k) : spPool L s := by
  unfold spPool; rw [hs]; exact hb k h1 h2

/-! ## The generic moves -/

section Moves

variable {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`ownGH` agrees with a constant `o` on a covered block**: at its pcs
(`hQ`) and at the pc its run ends at (`hlast`), its pcs off the take site. -/
theorem agreeBlkH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ 4200314)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).so m (arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → ownGH L a s = o)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨n.pc, n.o, σ⟩).so m (arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownGH L a s = o) :
    BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo' hhi
    (fun x hx k hk => by
      rw [hsite, lab_siteH hlab, site_toNatH] at hx
      cases hx; exact hns k hk)
    (fun σ c hJ k hk s m hA _ _ hs => hQ σ c hJ k hk s m hA hs)
    (fun σ c hJ k hk s m hA _ _ hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.X64.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hlast σ c hJ s m hA hs)

/-- **A covered `ret`-free block of helloCells inside `SFactsSt2` at `ownGH`**,
at the outside move of any range `rS`: `blkW_pre` at the constant instance
`o` (no take phase), the source control replaced by `X64Consumer.c0`, moved
to `ownGH` where it agrees with `o` (`hag`). -/
theorem blk_cH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (o : List (Loc × Val)) {Λ : Scc.Sem.Layout} {rS : Range} {n : ND} {blk : List (Directive × Nat)} {l : Label}
    {k : Nat} {blo bhi : Int} (hb : blockAtB L.prog l k blk = true)
    (he : (_root_.Executable.labels L.exe).label l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hcl : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hag : BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have h := Spike.Lib.X64.Rt.blkW_pre (InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) o False)
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (n := c0N n) hb he hok hR hlo' hhi c0N_cfacts
    (ra := 0) (dead := fun _ => false)
    (by rw [he]; exact Spike.Lib.X64.WakePh.Tcb2CallW.blkPh_const_of hcl (fun j hj => by rw [okPc_eq hΛ]; exact hpc j hj))
    (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hag' : BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) blk := by
    intro s σ c a1 a2 a3 a4 a5 a6 hJ k hk m a8 a9
    obtain ⟨-, c', hJ'⟩ := hJ
    exact hag s σ c' a1 a2 a3 a4 a5 a6 hJ' k hk m a8 a9
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 h) hag'
  exact blkW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **A block in a range of `wc_main` where `ownGH` is `o`** (`hown`: at
`l + k` for `k < N`, the range's pcs off the sites `hf` and off the take
site `hns`): `blk_cH` and `agreeBlkH`, the block's cells inside the range
(`hco`), its end's `ownGH` `hlast`. -/
theorem blk_atH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (o : List (Loc × Val)) {Λ : Scc.Sem.Layout} {rS : Range} {l : Label} {base N off : Nat} {n : ND}
    {blk : List (Directive × Nat)} {blo bhi : Int}
    (hl : (_root_.Executable.labels L.exe).label l = Int64.ofNat base)
    (hf : ∀ k < N, (Int64.ofNat base + Int64.ofNat k).toBitVec.toNat = base + k ∧ okC (base + k) = true)
    (hns : 4200314 < base ∨ base + N ≤ 4200314)
    (hown : ∀ (s : State) (k : Nat), k < N → s.st.2 = (_root_.Executable.labels L.exe).label l + Int64.ofNat k →
      ownGH L a s = o)
    (hb : blockAtB helloCells l off blk = true)
    (he : (_root_.Executable.labels L.exe).label l + Int64.ofNat off = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hcl : blk.all (fun dz => (Spike.Lib.X64.classify dz.1).isSome) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hco : ∀ k < blk.length, off + cellOff blk k < N)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨n.pc, n.o, σ⟩).so m (arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownGH L a s = o) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have hpcE : ∀ k, n.pc + Int64.ofNat (cellOff blk k) =
      (_root_.Executable.labels L.exe).label l + Int64.ofNat (off + cellOff blk k) := fun k => by
    rw [← he, ofNat_add']
  refine blk_cH hp hlo hΛ hsite o (onProgH hp hb) he hok hR hlo' hhi hcl hnr (fun j hj => ?_) ?_
  · have h := hf _ (hco j hj)
    rw [hpcE, hl, h.1]; exact h.2
  refine agreeBlkH hlab hsite (code_field L.lays rfl (onProgH hp hb) he) hok hR hlo' hhi (fun k hk => ?_)
    (fun σ c _ k hk s m _ hs => hown s _ (hco k hk) (by rw [snd_of hs, hpcE])) hlast
  have h := hco k hk
  rw [hpcE, hl, (hf _ h).1]; omega

/-- **A node of helloCells inside `SFactsSt2` at `ownGH`** from the constant
instance's `SFacts` at `c0N n` (`h`), `ownGH` `o` at its pc and the next
(`h0`, `hz`), its pc off the take site, each state at a `z`-byte cell off
`syscall` whose leaves are `z` bytes on (`hstep`). -/
theorem node_cH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} {K : State → State → Prop}
    {n : ND} {z : Nat}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.X64.PhRec.μ L) (fun _ => o) rS (fun _ => False) lbl s c) K
      L.exe L.endPc R F (c0N n))
    (hns : n.pc.toBitVec.toNat ≠ 4200314)
    (h0 : ∀ s : State, s.st.2 = n.pc → ownGH L a s = o)
    (hz : ∀ s : State, s.st.2 = n.pc + Int64.ofNat z → ownGH L a s = o)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) := by
    rintro s c ⟨h1, h2, h3, h4', σ, hA, hF, -, c', hJ⟩
    have hpc : s.st.2 = n.pc := h4'
    obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c' ⟨h1, h2, h3, hpc, σ, hA, hF, hJ⟩
    have hns' : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pcOf s ≠ x := by
      intro x hx; rw [hsite, lab_siteH hlab, site_toNatH] at hx; cases hx; unfold pcOf; rw [hpc]; exact hns
    exact ⟨⟨h0 s hpc, fun s' hs => hz s' (by rw [Spike.Lib.X64.WakePh.WcW.succ_pc hc hd hex hl hns' hs, hpc])⟩, fun _ h => h⟩
  have h2 := Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Moves

/-- The blocks' and rows' code facts. -/
theorem sp4InH : blockAtB helloCells x24L 0 sp4AH = true ∧
    blockAtB helloCells x24L 12 [(stDir .rcx 56 .rax, 4)] = true ∧ blockAtB helloCells x24L 16 initCallH = true ∧
    blockAtB helloCells x25L 0 sp6AH = true ∧ blockAtB helloCells x25L 44 [(op64 .mfence, 3)] = true ∧
    blockAtB helloCells x25L 47 cloneLdH = true ∧
    blockAtB helloCells x25L 84 [(Spike.Lib.X64.FI.toDir (.xor_rr32_self .rdx), 2)] = true ∧
    blockAtB helloCells x25L 86 [(Spike.Lib.X64.FI.toDir (.xor_rr32_self .r10), 3)] = true ∧
    blockAtB helloCells x25L 89 nrB = true := by decide +kernel

/-- The blocks' cells inside their ranges. -/
theorem cells_inH : (∀ k < sp4AH.length, 0 + cellOff sp4AH k < 25) ∧
    (∀ k < initCallH.length, 16 + cellOff initCallH k < 25) ∧ (∀ k < sp6AH.length, 0 + cellOff sp6AH k < 95) ∧
    (∀ k < cloneLdH.length, 47 + cellOff cloneLdH k < 95) ∧ (∀ k < nrB.length, 89 + cellOff nrB k < 95) := by
  decide +kernel

/-! ## The obligations -/

section Obl

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {c0 : Spike.Lib.Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
  {fr : BitVec 64 × BitVec 64}
include hp hlo hΛ hlab hsite

/-- **`.x24`'s block** (`sp4AH`). -/
theorem n4_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n20) sp4AH :=
  blk_atH hp hlo hΛ hlab hsite (own2aH L a 0) (lab_x24H hlab)
    (fun k hk => ⟨(x24_factsH k hk).1, (x24_factsH k hk).2.2⟩) (by decide) (fun s k hk hs => own_x24H hlab hk hs)
    sp4InH.1 (ofNat_zero' _) sp4AH_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_inH.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label sp4AH
        ⟨(_root_.Executable.labels L.exe).label x24L, oWH, σ⟩).pc at e
      rw [sp4AH_run] at e
      exact own_x24H hlab (k := 12) (by decide) e)

/-- **The tid store** (a row): `t + 56` mapped for writing, unmapped in
private memory under `F`, off `own2aH L a 0` (`htidW`). -/
theorem n4s_wcGH (a : BitVec 64)
    (htidW : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2aH L a 0) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n20s) := by
  obtain ⟨hmw, hun, hno⟩ := htidW
  have hI := InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (own2aH L a 0) False
  have hb := onProgH hp sp4InH.2.1
  refine node_cH hlab hsite (o := own2aH L a 0) (z := 4)
    (Spike.Lib.X64.Rt.nodeW_st_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F)
      (ownOf := fun _ => own2aH L a 0) (fun _ => rfl) hb (p := L.lab x24L + Int64.ofNat 12) rfl rfl c0N_cfacts
      (okP_x24H hΛ hlab (by decide)) (fun _ _ h => h) rfl ?_ hmw hun (fun _ w => hno w)) ?_
    (fun s hs => own_x24H hlab (k := 12) (by decide) hs)
    (fun s hs => own_x24H hlab (k := 12 + 4) (by decide) (by rw [hs]; exact (ofNat_add' _ 12 4).symm)) ?_
  · rintro σ c ⟨-, c', -, hcx, -⟩
    rw [Spike.Lib.X64.bAddr, hcx]; rfl
  · show ((_root_.Executable.labels L.exe).label x24L + Int64.ofNat 12).toBitVec.toNat ≠ _
    rw [lab_x24H hlab, (x24_factsH 12 (by decide)).1]; omega
  · rintro s c ⟨h1, h2, h3', h4', σ, hA, hF, -, hcx, -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb (p := L.lab x24L + Int64.ofNat 12) rfl h1 h2 h4'
    have ha' : eaddr s 4 (mB .rcx 56) = t + 56#64 :=
      (eaddr_mB s 4 .rcx 56).trans (by rw [hA.regs, hcx]; rfl)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

/-- **The call block** (`initCallH`), its end at `scc_rt_thread_init` on a
pool stack (`hband`). -/
theorem n5_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi) (hband : BandTiH L R) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n20p) initCallH :=
  blk_atH hp hlo hΛ hlab hsite (own2aH L a 0) (lab_x24H hlab)
    (fun k hk => ⟨(x24_factsH k hk).1, (x24_factsH k hk).2.2⟩) (by decide) (fun s k hk hs => own_x24H hlab hk hs)
    sp4InH.2.2.1 rfl initCallH_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_inH.2.1
    (fun σ c _ s m' hA hs => by
      change Abs R (arun (_root_.Executable.labels L.exe).label initCallH
        ⟨(_root_.Executable.labels L.exe).label x24L + 16, oWH, σ⟩).so m' _ at hA
      change s.st = (m', (arun (_root_.Executable.labels L.exe).label initCallH
        ⟨(_root_.Executable.labels L.exe).label x24L + 16, oWH, σ⟩).pc) at hs
      rw [initCallH_run] at hs hA
      have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
      have hm : s.st.1 = m' := by rw [hs]
      refine (own_tiH hlab (.inl ?_) (spPool_ofH hband (k := -136) (by decide) (by decide) ?_)).trans
        (own2a0_eqH L a).symm
      · unfold pcOf; rw [snd_of hs, lab_tiH hlab]; rfl
      · rw [hm]; exact hsp)

/-- **`scc_rt_thread_init`'s entry** (the call node), on a pool stack
(`hband`): the first state of its first instruction's block. -/
theorem nIH_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -144) (hhi : 16 ≤ R.hi) (hband : BandTiH L R) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNIH L.lab c0 t sl me cA fr) := by
  have eT := lab_tiH hlab (L := L)
  have hlen : tiPush.length = 1 := by decide
  have hb := onProgH hp hello_tiPush
  refine Spike.Lib.LowerX64.BlkW.nodeW (blk := tiPush) ?_ (by decide)
  refine blk_cH hp hlo hΛ hsite (own2bH L a 12) hb (ofNat_zero' _) tiPushH_ok hR hRlo hhi (by decide +kernel)
    (by decide +kernel) (fun j hj => ?_) ?_
  · obtain rfl : j = 0 := by omega
    show okC (((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat) = true
    rw [eT, ti_factsH.1]; exact ti_factsH.2.2.2.2
  refine agreeBlkH hlab hsite (code_field L.lays rfl hb (ofNat_zero' _)) tiPushH_ok hR hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m' hA hs => ?_) (fun σ c _ s m' hA hs => ?_)
  · obtain rfl : k = 0 := by omega
    show ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
      Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat ≠ _
    rw [eT, ti_factsH.1]; omega
  · obtain rfl : k = 0 := by omega
    have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
    have hm : s.st.1 = m' := by rw [hs]
    refine own_tiH hlab (.inl ?_) (spPool_ofH hband (k := -136) (by decide) (by decide) ?_)
    · unfold pcOf; rw [snd_of hs]
      show ((_root_.Executable.labels L.exe).label "scc_rt_thread_init" +
        Int64.ofNat (cellOff tiPush 0)).toBitVec.toNat = _
      rw [eT]; exact ti_factsH.1
    · rw [hm, hsp]; rfl
  · change Abs R (arun (_root_.Executable.labels L.exe).label tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oCH, σ⟩).so m' _ at hA
    change s.st = (m', (arun (_root_.Executable.labels L.exe).label tiPush
      ⟨(_root_.Executable.labels L.exe).label "scc_rt_thread_init", oCH, σ⟩).pc) at hs
    rw [tiPushH_run] at hs hA
    have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
    have hm : s.st.1 = m' := by rw [hs]
    refine own_tiH hlab (.inr ?_) (spPool_ofH hband (k := -144) (by decide) (by decide) (by rw [hm]; exact hsp))
    unfold pcOf; rw [snd_of hs, eT]; exact ti_factsH.2.1

/-! ### The clone's, at any stack top `k` and frame `F` -/

variable {k : BitVec 64}

/-- **`.x25`'s block** (`sp6AH`). -/
theorem n6_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6H L.lab c0 t k sl me cA fr) sp6AH :=
  blk_atH hp hlo hΛ hlab hsite (own2bH L a 0) (lab_x25H hlab)
    (fun k hk => ⟨(x25_factsH k hk).1, (x25_factsH k hk).2.2⟩) (by decide) (fun s k hk hs => own_x25H hlab hk hs)
    sp4InH.2.2.2.1 (ofNat_zero' _) sp6AH_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_inH.2.2.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label sp6AH
        ⟨(_root_.Executable.labels L.exe).label x25L, oWH, σ⟩).pc at e
      rw [sp6AH_run] at e
      exact own_x25H hlab (k := 44) (by decide) e)

/-- **The fence** (a row, `mfence`). -/
theorem n6f_wcGH (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6fH L.lab c0 t k sl me cA fr) := by
  have hI := InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (own2bH L a 0) False
  have hb := onProgH hp sp4InH.2.2.2.2.1
  refine node_cH hlab hsite (o := own2bH L a 0) (z := 3)
    (nodeW_mfence_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) hb
      (p := L.lab x25L + Int64.ofNat 44) rfl rfl c0N_cfacts (okP_x25H hΛ hlab (by decide)) (fun _ _ h => h) rfl) ?_
    (fun s hs => own_x25H hlab (k := 44) (by decide) hs)
    (fun s hs => own_x25H hlab (k := 44 + 3) (by decide) (by rw [hs]; exact (ofNat_add' _ 44 3).symm)) ?_
  · show ((_root_.Executable.labels L.exe).label x25L + Int64.ofNat 44).toBitVec.toNat ≠ _
    rw [lab_x25H hlab, (x25_factsH 44 (by decide)).1]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb (p := L.lab x25L + Int64.ofNat 44) rfl h1 h2 h4'
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_mfence hc, fun s' hu => ?_⟩
    obtain ⟨_, hu⟩ := hu
    simp only [TreeLeaf] at hu
    subst hu; rfl

/-- **The clone's loads** (`cloneLdH`). -/
theorem n6a_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6aH L.lab c0 t k sl me cA fr) cloneLdH :=
  blk_atH hp hlo hΛ hlab hsite (own2bH L a 0) (lab_x25H hlab)
    (fun k hk => ⟨(x25_factsH k hk).1, (x25_factsH k hk).2.2⟩) (by decide) (fun s k hk hs => own_x25H hlab hk hs)
    sp4InH.2.2.2.2.2.1 rfl cloneLdH_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_inH.2.2.2.1
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label cloneLdH
        ⟨(_root_.Executable.labels L.exe).label x25L + 47, oWH, σ⟩).pc at e
      rw [cloneLdH_run] at e
      exact own_x25H hlab (k := 47 + 37) (by decide) (by rw [e]; exact (ofNat_add' _ 47 37).symm))

/-- A node at an `xorl` row of `.x25` (`z` bytes at `.x25 + j`) inside
`SFactsSt2` at `ownGH`. -/
theorem xor_wcGH (a : BitVec 64) {r : Reg64} {j z : Nat} {n : ND}
    (hb : blockAtB helloCells x25L j [(Spike.Lib.X64.FI.toDir (.xor_rr32_self r), z)] = true)
    (hpc : n.pc = L.lab x25L + Int64.ofNat j) (hj : j + z < 95)
    (hC : ∀ σ c, (c0N n).J σ c → CFacts Λ (fun _ => none) c) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hI := InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (own2bH L a 0) False
  have hb' := onProgH hp hb
  refine node_cH hlab hsite (o := own2bH L a 0) (z := z)
    (Spike.Lib.X64.Rt.nodeW_fi_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) hb' rfl hpc hC
      (okP_x25H hΛ hlab (by omega)) (fun _ _ h => h) rfl) ?_
    (fun s hs => own_x25H hlab (k := j) (by omega) (by rw [hs, hpc]))
    (fun s hs => own_x25H hlab (k := j + z) hj (by rw [hs, hpc, ofNat_add'])) ?_
  · rw [hpc]; show ((_root_.Executable.labels L.exe).label x25L + Int64.ofNat j).toBitVec.toNat ≠ _
    rw [lab_x25H hlab, (x25_factsH j (by omega)).1]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb' rfl h1 h2 (h4'.trans hpc)
    obtain ⟨tr, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
    refine ⟨_, _, hc, fun w w' h => (by cases h), hex, fun s' hu => ?_⟩
    obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakePh.Tcb2W.silent_leaf hst hu; rfl

/-- **`xorl %edx, %edx`** (a row). -/
theorem nd_wcGH (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNdH L.lab c0 t k sl me cA fr) :=
  xor_wcGH hp hlo hΛ hlab hsite a sp4InH.2.2.2.2.2.2.1 rfl (by decide) c0N_cfacts

/-- **`xorl %r10d, %r10d`** (a row). -/
theorem n10_wcGH (a : BitVec 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcN10H L.lab c0 t k sl me cA fr) :=
  xor_wcGH hp hlo hΛ hlab hsite a sp4InH.2.2.2.2.2.2.2.1 rfl (by decide) c0N_cfacts

/-- **The call number** (`nrB`), to the `syscall`. -/
theorem nr_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (wcNrH L.lab c0 t k sl me cA fr) nrB :=
  blk_atH hp hlo hΛ hlab hsite (own2bH L a 0) (lab_x25H hlab)
    (fun k hk => ⟨(x25_factsH k hk).1, (x25_factsH k hk).2.2⟩) (by decide) (fun s k hk hs => own_x25H hlab hk hs)
    sp4InH.2.2.2.2.2.2.2.2 rfl nrBH_ok hR hRlo hhi (by decide +kernel) (by decide +kernel) cells_inH.2.2.2.2
    (fun σ c _ s m' _ hs => by
      have e := snd_of hs
      change s.st.2 = (arun (_root_.Executable.labels L.exe).label nrB
        ⟨(_root_.Executable.labels L.exe).label x25L + 89, oWH, σ⟩).pc at e
      rw [nrBH_run] at e
      exact own_x25H hlab (k := 89 + 5) (by decide) (by rw [e]; exact (ofNat_add' _ 89 5).symm))

/-- **`WcSp6W` at `SFactsSt2`/`ownGH`**: `.x25` to the `syscall`, at any
stack top and frame. -/
theorem wcSp6W_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    WcSp6W (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 t k sl me cA fr :=
  ⟨n6_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi, n6f_wcGH hp hlo hΛ hlab hsite a,
    n6a_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi, nd_wcGH hp hlo hΛ hlab hsite a, n10_wcGH hp hlo hΛ hlab hsite a,
    nr_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi⟩

/-- **`WcSp4WH` at `SFactsSt2`/`ownGH`**, at the outside move of any range
`rS`: `wc_main`'s frame on a pool stack at the call (`hband`) and the tid
word's facts (`htidW`). -/
theorem wcSp4W_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -136) (hhi : 16 ≤ R.hi) (hband : BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2aH L a 0) :
    WcSp4WH (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F c0 t sl me cA fr :=
  ⟨n4_wcGH hp hlo hΛ hlab hsite a hR (by omega) hhi, n4s_wcGH hp hlo hΛ hlab hsite a htidW,
    n5_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi hband⟩

end Obl

end Spike.Lib.X64.HelloPh.WcSp4W

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.hello_tiPush' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.hello_tiPush
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.x24_factsH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.x24_factsH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.x25_factsH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.x25_factsH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.ti_factsH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.ti_factsH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.sp4InH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.sp4InH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.cells_inH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.cells_inH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.own2a0_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.own2a0_eqH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.blk_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.blk_atH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.node_cH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.node_cH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.nIH_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.nIH_wcGH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.wcSp4W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.wcSp4W_wcGH
/-- info: 'Spike.Lib.X64.HelloPh.WcSp4W.wcSp6W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcSp4W.wcSp6W_wcGH
