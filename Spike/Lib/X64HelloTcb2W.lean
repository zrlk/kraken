/-
**hello.w's `wc_main` second `scc_rt_alloc_tcb` call inside the global owned-words map on x86-64** (the twin of
`Spike/Lib/A64HelloTcb2W.lean`; wake's x86-64 version is `Spike/Lib/X64WakeTcb2W.lean` with its tools
`Spike/Lib/X64WakeTcb2WLib.lean`): the node obligations `TcbWG` of `scc_rt_alloc_tcb` at `HelloWc.tcb2QH g c0`
for `SFactsSt2` at `ownGH` (`tcb2W_ownGH`), from the instance's (`tcbW_postG` at `instOk2aPH`, `tcbPh2aH`)
moved along `ownGH = own2aH ∘ ph2aH` where `ownGH` picks `own2aH` (`Good2aH`: the callee's pcs on a pool stack,
its return to `.Lwc_main.x24`).

wake's program-independent pieces are reused (`Tcb2W.blkW_toSt2`, `nodeW_toSt2`, `nodeW_ownCongr2`, `soRun`,
`arun_so`, `keep_fi`, `keep_lea`, `keep_rmw`, `keep_hdr`; `BlkW.agree_of`, `NodeW.agree_of`). The call site's
block and nodes are `Spike/Lib/X64HelloWcSp3.lean`'s (`tcb2CallH`, `tcb2QH`, `wcN3H`, `wcNCH`), so there is no
separate twin of the wake call module. hello's pcs (wake's `+ 37` in the runtime): `scc_rt_alloc_tcb` at `4199029`
(`.entry` `4199048`, `.len` `4199070`, `.ok` `4199284`), `scc_rt_thread_reserve` at `4199484`, `.Lwc_main.x24`
`4203749`, `.x25` `4203774`, the take site `4200314`; the header word at `pinA + 80 + 24`.

- `PcAH`, `BandAH`, `good2aH_of`: where `Good2aH` holds by the pc and `%rsp`.
- `good2aH_blk`, `hpcH_of`, `good2aH_node`: `Good2aH` at a block's (a node's) states and their successors.
- `pcAH_ne`, `blk2aH`, `node2aH`: a block (a node) of the call moved to `ownGH`.
- `tcb_labsH`, `tcb2W_ownGH`: the result; `tcb2H_hdrA_ne`: the header's word is not `pinA + 8`.

## Differences from the AArch64 version

- As wake's x86-64 version: no `hal`; the band is `[-184, 8]` (A64's `[-192, 0]`); `hlo' : R.lo ≤ -184`,
  `hhi : 8 ≤ R.hi`; the return is to `.Lwc_main.x24` (A64's `.L22_wc_main.sp4`); 33 nodes (the length
  computation's flag-clobbering instructions and the `leaq`s are nodes of their own); the code's check
  (`HelloWc.hello_allocTcbIn`, from `X64HelloWcSp3`) has 35 conjuncts.
- `tcb2H_hdrA_ne` is new (wake's x86-64 `tcb2_hdrA_ne` at hello's header word `pinA + 104`).
-/
import Spike.Lib.X64HelloTcb2
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloOwnGAgree
import Spike.Lib.X64HelloOwnGAbT
import Spike.Lib.X64WakeTcb2WLib

namespace Spike.Lib.X64.HelloPh.Tcb2W

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq code_field)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf nextPc abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout tcbNG)
open Spike.Lib.X64Consumer (SFacts Lbl)
open Spike.Lib.X64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At SO SI FI AM Abs arun cellOff okBlk CodeAt xaddDir stDir mB)
open Kraken.Promising.Lower.X64 (CellAt eaddr)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TN StackM hdrBlk_eq rmwBlk_eq)
open Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh
open Spike.Lib.X64.WakePh.Tcb2W (blkW_toSt2 nodeW_toSt2 nodeW_ownCongr2 soRun arun_so keep_fi keep_lea keep_rmw
  keep_hdr)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH)

/-! ### Where `ownGH` picks `own2aH`, by the pc and `%rsp` -/

/-- **The pcs where `ownGH` picks `own2aH`**: `scc_rt_alloc_tcb`'s (on a pool
stack) or `wc_main`'s from `.x24` to `.x25`, at the canonical base. -/
def PcAH (p : Int64) : Prop :=
  (4199029 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 4199484) ∨
    (4203749 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 4203774)

instance (p : Int64) : Decidable (PcAH p) := by unfold PcAH; infer_instance

/-- **`scc_rt_alloc_tcb`'s frame on a pool stack**: every address of
`[-184, 8]` of `R` in `(pool.lo, pool.lo + pool.size]`. -/
def BandAH (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -184 ≤ k → k ≤ 8 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

variable {L : RuntimeLayout}

/-- **`Good2aH` by the pc and `%rsp`.** -/
theorem good2aH_of (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (hb : BandAH L R) {s : State} (hp : PcAH s.st.2) (hsp : SpAt R (-184) 8 s) : Good2aH L s := by
  obtain ⟨e1, e2, -, -, e5, e6, -, -, -⟩ := labs_eqH hlab (L := L)
  obtain ⟨k, h1, h2, hk⟩ := hsp
  unfold Good2aH inPc pcOf
  rw [e1, e2, e5, e6]
  rcases hp with hp | hp
  · exact .inl ⟨hp, by unfold spPool; rw [hk]; exact hb k h1 h2⟩
  · exact .inr (.inl hp)

section Blk

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`Good2aH` along a block** and at its successors, from its abstract
run: each pc it reaches in `PcAH` (`hpc`), each static `%rsp` offset in
`[-184, 8]` (`hso`), the frame on a pool stack (`hb`). -/
theorem good2aH_blk (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandAH L R)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hpc : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcAH (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8) :
    BlkW (fun s _ => Good2aH L s ∧ ∀ s', StSucc μ s s' → Good2aH L s') (fun _ _ => False)
      exe endPc R F n blk := by
  refine Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns ?_ ?_
  · intro σ c hJ k hk s m hA _ _ hs
    have hp := hpc σ c hJ k (Nat.le_of_lt hk)
    rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk] at hp
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2aH_of hlab hb (by rw [hs]; exact hp) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact Spike.Lib.X64ConsumerA.rsp_of_abs hA
  · intro σ c hJ k hk s m hA _ _ hs
    have ho := hso (k + 1) hk
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2aH_of hlab hb (by rw [hs]; exact hpc σ c hJ (k + 1) hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact Spike.Lib.X64ConsumerA.rsp_of_abs hA

/-- **`hpc` of `good2aH_blk`** from the block's pcs (`h1`) and where its
run ends (`h2`). -/
theorem hpcH_of (hok : okBlk blo bhi n.o blk = true)
    (h1 : ∀ k < blk.length, PcAH (n.pc + Int64.ofNat (cellOff blk k)))
    (h2 : ∀ σ c, n.J σ c → PcAH (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) :
    ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcAH (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc := by
  intro σ c hJ k hk
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk]; exact h1 k hk
  · rw [List.take_length]; exact h2 σ c hJ

/-- **`Good2aH` at a node** and at its successors, which keep `%rsp` and
`%rbp` and are `sz` bytes past it (`hk`): its pc and the next in `PcAH`
(`hpc`), its static `%rsp` offset in `[-184, 8]` (`hso`). -/
theorem good2aH_node {sz : Nat} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandAH L R)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : PcAH n.pc ∧ PcAH (n.pc + Int64.ofNat sz)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8) :
    NodeW (fun s _ => Good2aH L s ∧ ∀ s', StSucc μ s s' → Good2aH L s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.rsp.toBitVec = R.addr n.o.sp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
  refine ⟨⟨good2aH_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact good2aH_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

end Blk

/-! ### A block's and a node's obligations at `ownGH` from the instance's -/

section Move

variable {Λ : Scc.Sem.Layout} {μ : Marks} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND}

/-- `PcAH` is off the take site (`scc_rt_take_site` at `4200314`). -/
theorem pcAH_ne {p : Int64} (h : PcAH p) : p.toBitVec.toNat ≠ 4200314 := by
  unfold PcAH at h; omega

/-- **A block of the call at `ownGH`** from the instance's `SFacts`: the
block's pcs in `PcAH` (`h1`), where its run ends (`h2`), its static `%rsp`
offsets in `[-184, 8]` (`hso`), the take site at `4200314` (`hsite`). -/
theorem blk2aH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hb : BandAH L R)
    (hsite : ∀ x, μ.site .take = some x → x = 4200314) {blk : List (Directive × Nat)} {blo bhi : Int}
    (h : BlkW (fun s c => SFacts Λ μ (fun s => own2aH L a (ph2aH (pcOf s))) rS Tk lbl s c) K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcAH (n.pc + Int64.ofNat (cellOff blk k)))
    (h2 : ∀ σ c, n.J σ c → PcAH (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8) :
    BlkW (fun s _ => SFactsSt2 Λ μ (ownGH L a) s) K exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (blkW_toSt2 h)
    (BlkW.agree_of (good2aH_blk hlab hb hcode hok hR hlo hhi
      (fun x hx k hk => by rw [hsite x hx]; exact pcAH_ne (h1 k hk)) (hpcH_of hok h1 h2) hso)
      fun _ hs => ownGH_2a hlab hs)

/-- **A node of the call at `ownGH`** from the instance's `SFacts`: its
successors keeping `%rsp` and `%rbp` `sz` bytes on (`hk`), its pc and the
next in `PcAH` (`hpc`), its static `%rsp` offset in `[-184, 8]` (`hso`). -/
theorem node2aH {sz : Nat} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandAH L R)
    (h : NodeW (fun s c => SFacts Λ μ (fun s => own2aH L a (ph2aH (pcOf s))) rS Tk lbl s c) K exe endPc R F n)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : PcAH n.pc ∧ PcAH (n.pc + Int64.ofNat sz)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8) :
    NodeW (fun s _ => SFactsSt2 Λ μ (ownGH L a) s) K exe endPc R F n :=
  nodeW_ownCongr2 (nodeW_toSt2 h)
    (NodeW.agree_of (good2aH_node hlab hb hk hpc hso) fun _ hs => ownGH_2a hlab hs)

end Move


/-- The labels the call's pcs are decided from, at the canonical base. -/
theorem tcb_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199029 ∧
    (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199048 ∧
    (_root_.Executable.labels L.exe).label lenL = Int64.ofNat 4199070 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199284 ∧
    (_root_.Executable.labels L.exe).label ".Lwc_main.x24" = Int64.ofNat 4203749 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)


/-- `hso` of `blk2a` on a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -184 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

set_option hygiene false in
/-- A block of the call at `l + off` (`ok` its `okBlk`, `bb` its code
check, `oo` its entry offsets), its end pc's `PcAH` left. -/
local macro "tblk2 " bb:term:max ok:term:max blk:term:max oo:term:max el:term:max : tactic =>
  `(tactic| (
    refine blk2aH hlab hb hsite' h (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _))
      $ok hR (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT $blk $oo)
    · intro k hk; dsimp only [tcbNG]; rw [$el:term]; revert k; decide +kernel
    dsimp only [tcbNG] at hJ ⊢))

set_option hygiene false in
/-- A single-instruction node of the call (`z` bytes, `bb` its code check,
`kp` its `Keep` from the cell `hc` and the step `hs`). -/
local macro "tnode2 " z:term:max bb:term:max el:term:max kp:term : tactic =>
  `(tactic| (
    refine node2aH (sz := $z) hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [tcbNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (code_field L.lays rfl $bb (by first | rfl | exact ofNat_zero' _) s he hn).cell0 rfl rfl hp'
      have hK : Keep s s' := $kp
      exact ⟨hK, by rw [keep_pc hc hK, hp']⟩
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel
    · dsimp only [tcbNG, rmwPc, hdrPc]; rw [$el:term]; decide +kernel))

/-- **`scc_rt_alloc_tcb`'s node obligations at `tcb2QH g c0` inside
`SFactsSt2` at `ownGH`**: `tcbW_postG` at the second call's instance
(`instOk2aP`, `tcbPh2a`), each node moved to `ownGH` where it picks `own2aH`
(`blk2a`, `node2a`): the frame on a pool stack (`hb`), the return to
`.Lwc_main.x24` (`hra`), the counter's and the header's words mapped
(`hmP`, `hmH`) and off private memory (`hunP`, `hunH`). -/
theorem tcb2W_ownGH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Spike.Lib.X64Consumer.Lbl} {c0 : Ctl}
    (hC0 : Spike.Lib.X64Consumer.CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hb : BandAH L R) (g : G) (hra : g.ra = (L.lab ".Lwc_main.x24").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) true
      ⟨Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.X64.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.X64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s)
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2QH g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, eX20, eSite⟩ := tcb_labsH hlab (L := L)
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hT := Spike.Lib.X64.Rt.tcbW_postG (instOk2aPH hp hlo a hsite (rS := rS)) (fun _ => rfl)
    (hp ▸ Spike.Lib.X64.Flow.HelloWc.hello_allocTcbIn) hC0 hR hlo' hhi (tcb2QH g c0) rfl
    (ra := fun _ => L.lab ".Lwc_main.x24") hra (tcbPh2aH hΛ hlab hsep hhdr)
    (hpn ▸ hmP) hmH (hpn ▸ hunP) hunH hsub hSM
  have hsite' : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → x = 4200314 := by
    intro x hx
    rw [hsite, show L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 from eSite] at hx
    cases hx; rfl
  have hin := hp ▸ Spike.Lib.X64.Flow.HelloWc.hello_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  intro i
  have h := hT i
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TcbWG] at h ⊢
  case e =>
    tblk2 bE atPro_ok atPro oE eFn
    rw [(atPro_walkG _ _ hJ.2).1, eFn]; decide +kernel
  case entry =>
    tblk2 bEn atChk_ok atChk oI eEn
    rw [(atChk_walkG _ _ hJ.2).1, eEn]; decide +kernel
  case j1 =>
    tblk2 bJ1 atJ1_ok atJ1 oI eEn
    rw [(atJ1_walkG _ _ hJ.2).1]; show PcAH (_root_.Executable.labels L.exe |>.label lenL); rw [eLen]; decide +kernel
  case len =>
    tblk2 bL0 atL0_ok atL0 oI eLen
    rw [(atL0_walkG _ _ hJ.2).1, eLen]; decide +kernel
  case l1 =>
    tblk2 bL1 atL1_ok atL1 oI eLen
    rw [(atL1_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l2 =>
    tblk2 bL2 atL2_ok atL2 oI eLen
    rw [(atL2_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l3 =>
    tblk2 bL3 atL3_ok atL3 oI eLen
    rw [(atL3_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l4 =>
    tblk2 bL4 atL4_ok atL4 oI eLen
    rw [(atL4_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l5 =>
    tblk2 bL5 atL5_ok atL5 oI eLen
    rw [(atL5_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case l6 =>
    tblk2 bL6 atL6_ok atL6 oI eLen
    rw [(atL6_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case arg =>
    tblk2 bArg atArg_ok atArg oI eLen
    rw [(atArg_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide +kernel
  case bnd =>
    tblk2 bBnd atBnd_ok atBnd oI eLen
    rw [(atBnd_walkG _ _ hJ.2.1 hJ.2.2
      (by show (80#64).toNat + (lenOf Spike.Lib.X64.HelloPh.hdr2H).toNat ≤ 131072; decide)).1, eLen]
    decide +kernel
  case j2 =>
    tblk2 bJ2 atJ2_ok atJ2 oI eLen
    rw [(atJ2_walkG _ _ hJ.2).1]; show PcAH (_root_.Executable.labels L.exe |>.label okL); rw [eOk]; decide +kernel
  case o1 =>
    tblk2 bO1 atO1_ok atO1 oI eOk
    rw [(atO1_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o2 =>
    tblk2 bO2 atO2_ok atO2 oI eOk
    rw [(atO2_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o3 =>
    tblk2 bO3 atO3_ok atO3 oI eOk
    rw [(atO3_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o4 =>
    tblk2 bO4 atO4_ok atO4 oI eOk
    rw [(atO4_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case o5 =>
    tblk2 bO5 atO5_ok atO5 oI eOk
    rw [(atO5_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide +kernel
  case ret =>
    tblk2 bRet atRet_ok atRet oI eOk
    rw [(atRet_walkG _ _ hJ.2).1]
    show PcAH (Int64.ofBitVec g.ra)
    rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".Lwc_main.x24" = Int64.ofNat 4203749 from eX20]
    decide +kernel
  case shr1 => tnode2 3 fShr1 eLen keep_fi hc rfl hs
  case and1 => tnode2 3 fAnd1 eLen keep_fi hc rfl hs
  case shr2 => tnode2 3 fShr2 eLen keep_fi hc rfl hs
  case and2 => tnode2 3 fAnd2 eLen keep_fi hc rfl hs
  case imul1 => tnode2 4 fImul1 eLen keep_fi hc rfl hs
  case shl1 => tnode2 3 fShl1 eLen keep_fi hc rfl hs
  case lea1 => tnode2 7 sLea1 eLen keep_lea hc hs
  case ok => tnode2 7 sOk eOk keep_lea hc hs
  case imul2 => tnode2 4 fImul2 eOk keep_fi hc rfl hs
  case shl2 => tnode2 3 fShl2 eOk keep_fi hc rfl hs
  case shl3 => tnode2 3 fShl3 eOk keep_fi hc rfl hs
  case or1 => tnode2 3 fOr1 eOk keep_fi hc rfl hs
  case rmw =>
    tnode2 5 bRmw eLen keep_rmw hc hd (a := L.pnA)
      (by
        dsimp only [tcbNG] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]
        simp [Reg64s.get64, hJ.2.2.2, hpn])
      (hunP _ hF.1) hs
  case hdr =>
    tnode2 3 bHdr eOk keep_hdr hc hd (a := Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0))
      (by
        dsimp only [tcbNG] at hJ
        refine (Spike.Lib.X64.eaddr_mB s _ _ _).trans ?_
        rw [hA.regs]
        simp [Reg64s.get64, hJ.2.2.2])
      (hunH _ hF.1) hs

/-- **The header's word is not `pinA + 8`** (the call's header store is
off `tcbM`). -/
theorem tcb2H_hdrA_ne (g : G) (c0 : Ctl) :
    Spike.Lib.X64.Rt.hdrA L.lab (tcb2QH g c0) ≠ L.pinA + 8#64 := by
  rw [Spike.Lib.X64.Flow.HelloWc.tcb2QH_hdrA, L.lab_pin]
  intro h; bv_omega

end Spike.Lib.X64.HelloPh.Tcb2W

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.good2aH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.good2aH_of

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.good2aH_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.good2aH_blk

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.hpcH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.hpcH_of

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.good2aH_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.good2aH_node

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.pcAH_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.pcAH_ne

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.blk2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.blk2aH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.node2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.node2aH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.tcb_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.tcb_labsH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.tcb2W_ownGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.tcb2W_ownGH

/-- info: 'Spike.Lib.X64.HelloPh.Tcb2W.tcb2H_hdrA_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Tcb2W.tcb2H_hdrA_ne
