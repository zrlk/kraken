/-
**`wc_main` from `.sp4` to its `clone` inside `SFactsSt2` at wake.w's
global owned-words map `ownG`** (AArch64): the `SFactsSt2` component
of the pre-spawn chain's `W` at `WcSp4W`'s nodes (`A64WakeWcSp4Seg`).

Each block and row is proved at a constant instance (`InstOk.const` of
`instOkW`, owned words `o`, no take phase, `A64Consumer.c0` for the source
control: the state facts do not read it) and moved to `ownG`, which is `o`
at every pc of the block and at its successors:

- `.sp4` to the call (`sp4A`, the tid store, `initCall`): `wc_main`'s range
  `[.sp4, .sp6)`, where `ownG` is `own2a (ph2a pc) = own2a 0`;
- `scc_rt_thread_init`'s entry (`nI`, its first instruction `sub sp, sp, #48`)
  on a pool stack: `own2b (ph2b pc) = own2b 12 = own2a 0` (`own2a0_eq`);
- `.sp6` to the `svc` (`sp6A`, the fence, `cloneArgs`): `[.sp6, .stack_grow)`,
  where `ownG` is `own2b (ph2b pc) = own2b 0`.

The pcs and phases are decided by the kernel at the canonical base (`hlab`).

Open premises of `wcSp4W_wcG` (none proved here; the dischargers are
the pre-spawn chain's `h1`, `A64WakeWcInv.H1Stmt`, at `WcMidW.sp4`):
- `hband : BandTi L R`: `wc_main`'s frame on a pool stack at the call
  (`sp = R.addr (-80)` and `R.addr (-128)`, the callee's `sub`), as
  `Tcb2CallW.BandSp3` for the first call: from main's frame facts (h1).
- `htidW`: the tid word `t + 56` mapped for writing, unmapped in private
  memory under `F`, off `own2a L a 0` (a runtime word of the second TCB):
  from the TCB in the pool (h1, as `wake_wc_sp4_segW`'s `htid`).

- `tiSub`, `wake_tiSub`: `scc_rt_thread_init`'s first instruction.
- `sp4_facts`, `sp6_facts`, `ti_facts`, `lab_sp4`, `lab_sp6`, `lab_ti`: the
  pcs and phases at the canonical base.
- `own_sp4`, `own_sp6`, `own_ti`, `own2a0_eq`: `ownG` at the pcs; `BandTi`: the call on a pool stack.
- `agreeBlk`, `blk_c`, `node_c`, `blkW_nodeW`: the generic moves.
- `n4_wcG` … `n6a_wcG`: the seven obligations; `wcSp4W_wcG`: the result.
-/
import Spike.Lib.A64WakeWcSp4Seg
import Spike.Lib.A64WakeWcPreWI

namespace Spike.Lib.A64.WakePh.WcSp4W

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero code_of)
open Spike.Lib.A64.WakePh.Tcb2Call (oW)
open Spike.Lib.A64.WakePh.WcSp4 (sp4A initCall sp6A cloneArgs sp4A_ok initCall_ok sp6A_ok cloneArgs_ok sp4A_run
  initCall_run sp6A_run cloneArgs_run wcSp4In wake_wcSp4In wcN4F wcN4s wcN5 wcNI wcN6 wcN6f wcN6a)
open Spike.Lib.A64.WakePh.WcW (c0N c0N_cfacts blkW_mapC nodeW_mapC cell1)
open Spike.Lib.A64.Flow.WakeWc (WcSp4W aN bN XA XB tidSt_eq fenceB_eq)

/-! ## `scc_rt_thread_init`'s first instruction -/

/-- `scc_rt_thread_init`'s frame (`tiPro`'s first instruction). -/
def tiSub : List Directive := parseAArch64("sub sp, sp, #48")

block_spec tiSub (-128) 0 oW tiSub

theorem wake_tiSub : blockAt wakeProg "scc_rt_thread_init" 0 tiSub = true := by decide +kernel

/-! ## The pcs at the canonical base -/

/-- `.sp4`'s six pcs: their values, `ph2a` `0`, off the sites. -/
theorem sp4_facts : ∀ k < 6, (Int64.ofNat 2169268 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169268 + 4 * k ∧
    ph2aC (2169268 + 4 * k) = 0 ∧ okC (2169268 + 4 * k) = true := by decide +kernel

/-- `.sp6`'s fourteen pcs (to the `svc`): their values, `ph2b` `0`, off the sites. -/
theorem sp6_facts : ∀ k < 14, (Int64.ofNat 2169292 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169292 + 4 * k ∧
    ph2bC (2169292 + 4 * k) = 0 ∧ okC (2169292 + 4 * k) = true := by decide +kernel

/-- `scc_rt_thread_init`'s first two pcs: their values, `ph2b` `12`, the first off the sites. -/
theorem ti_facts : (Int64.ofNat 2165244 + Int64.ofNat (4 * 0)).toBitVec.toNat = 2165244 ∧
    (Int64.ofNat 2165244 + 4).toBitVec.toNat = 2165248 ∧ ph2bC 2165244 = 12 ∧ ph2bC 2165248 = 12 ∧
    okC 2165244 = true := by decide +kernel

/-- The take site at the canonical base. -/
theorem site_toNat : (Int64.ofNat 2165940).toBitVec.toNat = 2165940 := rfl

variable {L : RuntimeLayout} {a : BitVec 64}

theorem lab_sp4 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".L21_wc_main.sp4" = Int64.ofNat 2169268 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_sp6 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".L21_wc_main.sp6" = Int64.ofNat 2169292 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_ti (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_thread_init" = Int64.ofNat 2165244 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_site (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-- Two offsets from a label as one. -/
theorem pc_add (x : Int64) (k j : Nat) :
    x + Int64.ofNat (4 * k) + Int64.ofNat (4 * j) = x + Int64.ofNat (4 * (k + j)) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add]

theorem snd_of {s : State} {m : MachineData} {p : Int64} (h : s.st = (m, p)) : s.st.2 = p := by rw [h]

/-! ## `ownG` at the pcs -/

/-- The two second instances' owned words at the second switch. -/
theorem own2a0_eq (L : RuntimeLayout) (a : BitVec 64) : own2a L a 0 = own2b L a 12 := by
  have h := own2a_own2b_ph L a
  have h1 : ph2a 2169288 = 0 := by rw [ph2a_eq]; unfold ph2aC; rw [threadInit2_ph.1]
  have h2 : ph2b 2165244 = 12 := by rw [ph2b_eq]; unfold ph2bC; rw [threadInit2_ph.2.2]
  rwa [h1, h2] at h

/-- **`ownG` at `.sp4`'s pcs** is `own2a L a 0`. -/
theorem own_sp4 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 6) (hs : s.st.2 = L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * k)) : ownG L a s = own2a L a 0 := by
  have hp : pcOf s = 2169268 + 4 * k := by unfold pcOf; rw [hs, lab_sp4 hlab]; exact (sp4_facts k hk).1
  obtain ⟨-, -, -, -, e5, e6, -, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2a L s := .inr (.inl (by unfold inPc; rw [e5, e6, hp]; omega))
  rw [ownG_2a hlab hg, hp, ph2a_eq, (sp4_facts k hk).2.1]

/-- **`ownG` at `.sp6`'s pcs to the `svc`** is `own2b L a 0`. -/
theorem own_sp6 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State} {k : Nat}
    (hk : k < 14) (hs : s.st.2 = L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * k)) : ownG L a s = own2b L a 0 := by
  have hp : pcOf s = 2169292 + 4 * k := by unfold pcOf; rw [hs, lab_sp6 hlab]; exact (sp6_facts k hk).1
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inr (.inl (by unfold inPc; rw [e6, e7, hp]; omega))
  rw [ownG_2b hlab hg, hp, ph2b_eq, (sp6_facts k hk).2.1]

/-- **`ownG` at `scc_rt_thread_init`'s first two pcs on a pool stack** is
`own2b L a 12`. -/
theorem own_ti (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : pcOf s = 2165244 ∨ pcOf s = 2165248) (hsp : spPool L s) : ownG L a s = own2b L a 12 := by
  obtain ⟨-, -, e3, e4, -, -, -, -, -⟩ := labs_eq hlab (L := L)
  have hg : Good2b L s := .inl ⟨by unfold inPc; rw [e3, e4]; omega, hsp⟩
  rw [ownG_2b hlab hg, ph2b_eq]
  rcases hp with hp | hp <;> rw [hp]
  · rw [ti_facts.2.2.1]
  · rw [ti_facts.2.2.2.1]

/-- **`wc_main`'s frame on a pool stack at the call**: `sp` at the call
(`R.addr (-80)`) and past the callee's `sub` (`R.addr (-128)`) in
`(pool.lo, pool.lo + pool.size]`. -/
def BandTi (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -128 ≤ k → k ≤ -80 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- `sp` from the abstraction. -/
theorem sp_of {R : Region} {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R o m σ) :
    m.regs.SP.toBitVec = R.addr o.sp := by
  rw [hA.regs]; exact hA.so .SP _ rfl

/-- `spPool` at `sp = R.addr k` in the band. -/
theorem spPool_of {R : Region} (hb : BandTi L R) {s : State} {k : Int} (h1 : -128 ≤ k) (h2 : k ≤ -80)
    (hs : s.st.1.regs.SP.toBitVec = R.addr k) : spPool L s := by
  unfold spPool; rw [hs]; exact hb k h1 h2

/-! ## The generic moves -/

section Moves

variable {R : Region} {F : MachineData → Prop}

/-- **A node's states inside `W`**: the first of a block's
(`LowerA64.BlkW.nodeW`, not imported here). -/
theorem blkW_nodeW {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk) (hne : blk ≠ []) :
    NodeW W K exe endPc R F n := by
  rintro s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩
  have hk : 0 < blk.length := List.length_pos_iff.mpr hne
  have := h s σ c he hn hd hp hA hF hJ 0 hk s.st.1 hA (Spike.Lib.A64.Flow.DFrame.refl _ _)
  have hs : { s with st := (s.st.1, n.pc + Int64.ofNat (4 * 0)) } = s := by
    rw [← hp]; simp
    rfl
  rw [hs] at this
  exact this

/-- **`ownG` agrees with a constant `o` on a covered block**: at its pcs
(`hQ`) and at the pc its run ends at (`hlast`), its pcs off the take site. -/
theorem agreeBlk (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {n : ND} {blk : List Directive} {blo bhi : Int}
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ k < blk.length,
      (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, n.pc + Int64.ofNat (4 * k)) → ownG L a s = o)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownG L a s = o) :
    BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk :=
  Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo' hhi
    (fun x hx k hk => by rw [hsite] at hx; cases hx; exact hns k hk)
    (fun σ c hJ k hk s m hA _ _ hs => hQ σ c hJ k hk s m hA hs)
    (fun σ c hJ k hk s m hA _ _ hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hlast σ c hJ s m hA hs)

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hsite

/-- **A covered `ret`-free block of wakeProg inside `SFactsSt2` at `ownG`**,
at the outside move of any range `rS`: `blkW_pre` at the constant instance
`o` (no take phase), the source control replaced by `A64Consumer.c0`, moved
to `ownG` where it agrees with `o` (`hag`). -/
theorem blk_c (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (o : List (Loc × Val)) {Λ : Scc.Sem.Layout}
    {rS : Range} {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi) (hcl : blk.all (fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hag : BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have h := Spike.Lib.A64.Rt.blkW_pre (InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) o False)
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (n := c0N n) (hp ▸ hb) he hok hR hal hlo' hhi c0N_cfacts
    (ra := 0) (dead := fun _ => false)
    (by rw [he]; exact Tcb2CallW.blkPh_const_of hcl (fun j hj => by rw [okPc_eq hΛ]; exact hpc j hj))
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hag' : BlkW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) blk := by
    intro s σ c a1 a2 a3 a4 a5 a6 hJ k hk m a8 a9
    obtain ⟨-, c', hJ'⟩ := hJ
    exact hag s σ c' a1 a2 a3 a4 a5 a6 hJ' k hk m a8 a9
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Tcb2W.blkW_toSt2 h) hag'
  exact blkW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

omit hp hlo in
/-- **A node of wakeProg inside `SFactsSt2` at `ownG`** from the constant
instance's `SFacts` at `c0N n` (`h`), `ownG` `o` at its pc and the next
(`h0`, `h4`), its pc off the take site, each state at a 4-byte cell off
`svc` whose leaves are 4 bytes on (`hstep`). -/
theorem node_c {o : List (Loc × Val)} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} {K : State → State → Prop}
    {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.A64.PhRec.μ L) (fun _ => o) rS (fun _ => False) lbl s c) K
      L.exe L.endPc R F (c0N n))
    (hns : n.pc.toBitVec.toNat ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (h0 : ∀ s : State, s.st.2 = n.pc → ownG L a s = o)
    (h4 : ∀ s : State, s.st.2 = n.pc + Int64.ofNat 4 → ownG L a s = o)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => ownG L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) := by
    rintro s c ⟨h1, h2, h3, h4', σ, hA, hF, -, c', hJ⟩
    have hpc : s.st.2 = n.pc := h4'
    obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c' ⟨h1, h2, h3, hpc, σ, hA, hF, hJ⟩
    have hns' : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → pcOf s ≠ x := by
      intro x hx; rw [hsite] at hx; cases hx; unfold pcOf; rw [hpc]; exact hns
    exact ⟨⟨h0 s hpc, fun s' hs => h4 s' (by rw [WcW.succ_pc4 hc hd hex hl hns' hs, hpc])⟩, fun _ h => h⟩
  have h2 := Tcb2W.nodeW_ownCongr2 (Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Moves

/-- The blocks' and rows' code facts. -/
theorem sp4In : blockAt wakeProg ".L21_wc_main.sp4" 0 sp4A = true ∧
    blockAt wakeProg ".L21_wc_main.sp4" 3 [Spike.Lib.A64.Flow.strDir .X9 .X10 56] = true ∧
    blockAt wakeProg ".L21_wc_main.sp4" 4 initCall = true ∧ blockAt wakeProg ".L21_wc_main.sp6" 0 sp6A = true ∧
    blockAt wakeProg ".L21_wc_main.sp6" 3 [.instr ⟨.W64, .DMB .sy⟩] = true ∧
    blockAt wakeProg ".L21_wc_main.sp6" 4 cloneArgs = true := by
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b4, b4s⟩, b5⟩, -⟩, b6⟩, b6f⟩, b6a⟩ := hin
  exact ⟨b4, tidSt_eq ▸ b4s, b5, b6, fenceB_eq ▸ b6f, b6a⟩

/-! ## The seven obligations -/

section Obl

variable (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  {Λ : Scc.Sem.Layout} {rS : Range} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
include hp hlo hΛ hlab hsite

/-- **`.sp4`'s block** (`sp4A`). -/
theorem n4_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n4) sp4A := by
  have b4 := sp4In.1
  have e4 := lab_sp4 hlab (L := L)
  have eS := lab_site hlab (L := L)
  have hlen : sp4A.length = 3 := by decide
  refine blk_c hp hlo hsite hΛ (own2a L a 0) b4 (ofNat4_zero _) sp4A_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [e4, (sp4_facts j (by omega)).1]; exact (sp4_facts j (by omega)).2.2
  refine agreeBlk hsite (code_of L.lays rfl (hp ▸ b4) (ofNat4_zero _)) sp4A_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m _ hs => own_sp4 hlab (by omega) (snd_of hs)) ?_
  · show (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [e4, (sp4_facts k (by omega)).1, eS, site_toNat]; omega
  · intro σ c _ s m' _ hs
    have e := snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab sp4A ⟨L.lab ".L21_wc_main.sp4", oW, σ⟩).pc at e
    rw [sp4A_run] at e
    exact own_sp4 hlab (k := 3) (by decide)
      (by rw [e, show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc])

/-- **The tid store** (a row): `t + 56` mapped for writing, unmapped in
private memory under `F`, off `own2a L a 0` (`htidW`). -/
theorem n4s_wcG (a : BitVec 64)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n4s) := by
  have b4s := sp4In.2.1
  have e4 := lab_sp4 hlab (L := L)
  have eS := lab_site hlab (L := L)
  obtain ⟨hmw, hun, hno⟩ := htidW
  have hok : okPcOf lo wakeProg L.Λ (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat = true := by
    rw [okPc_eq hΛ, e4, (sp4_facts 3 (by decide)).1]; exact (sp4_facts 3 (by decide)).2.2
  refine node_c hsite (o := own2a L a 0)
    (Spike.Lib.A64.Rt.nodeW_st_pre (InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) _ False)
      (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) (ownOf := fun _ => own2a L a 0) (fun _ => rfl)
      (hp ▸ b4s) rfl rfl c0N_cfacts hok (fun _ _ h => h) rfl ?_ hmw hun (fun _ w => hno w)) ?_
    (fun s hs => own_sp4 hlab (k := 3) (by decide) hs)
    (fun s hs => own_sp4 hlab (k := 4) (by decide) (by
      rw [hs]; show L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 3) + Int64.ofNat 4 = _; rw [Int64.add_assoc]; rfl)) ?_
  · rintro σ c ⟨-, c', ⟨-, -, h10, -⟩, -⟩
    rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; rfl
  · show (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat ≠ _
    rw [e4, (sp4_facts 3 (by decide)).1, eS, site_toNat]; omega
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, ⟨-, -, h10, -⟩, -⟩
    have hc := cell1 hp b4s h1 h2 h4'
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 56 = t + 56#64 := by
      rw [hAb.regs, Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; rfl
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_str hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The call block** (`initCall`), its end at `scc_rt_thread_init` on a
pool stack (`hband`). -/
theorem n5_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hband : BandTi L R) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aN L.lab c0 t cA m fr .n5) initCall := by
  have b5 := sp4In.2.2.1
  have e4 := lab_sp4 hlab (L := L)
  have eS := lab_site hlab (L := L)
  have hlen : initCall.length = 2 := by decide
  refine blk_c hp hlo hsite hΛ (own2a L a 0) b5 rfl initCall_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [pc_add, e4, (sp4_facts (4 + j) (by omega)).1]; exact (sp4_facts (4 + j) (by omega)).2.2
  refine agreeBlk hsite (code_of L.lays rfl (hp ▸ b5) rfl) initCall_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m _ hs => own_sp4 hlab (k := 4 + k) (by omega)
      (by rw [snd_of hs]; exact pc_add _ 4 k)) ?_
  · show (L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [pc_add, e4, (sp4_facts (4 + k) (by omega)).1, eS, site_toNat]; omega
  · intro σ c _ s m' hA hs
    change Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab initCall
      ⟨L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4), oW, σ⟩).so m' _ at hA
    change s.st = (m', (Spike.Lib.A64.Flow.arun L.lab initCall
      ⟨L.lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4), oW, σ⟩).pc) at hs
    rw [initCall_run] at hs
    have hsp := sp_of hA
    rw [initCall_run] at hsp
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_ti hlab (.inl ?_) (spPool_of hband (k := -80) (by decide) (by decide) (by rw [hm]; exact hsp))).trans
      (own2a0_eq L a).symm
    unfold pcOf; rw [snd_of hs, lab_ti hlab]; rfl

/-- **`scc_rt_thread_init`'s entry** (the call node), on a pool stack
(`hband`): the first state of its first instruction's block. -/
theorem nI_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hband : BandTi L R) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcNI L.lab c0 t cA m fr) := by
  have eT := lab_ti hlab (L := L)
  have eS := lab_site hlab (L := L)
  refine blkW_nodeW (blk := tiSub) ?_ (by decide)
  refine blk_c hp hlo hsite hΛ (own2a L a 0) wake_tiSub (ofNat4_zero _) tiSub_ok hR hal hRlo hhi (by decide)
    (by decide) (fun j hj => ?_) ?_
  · have hj0 : j = 0 := by have : tiSub.length = 1 := by decide
                           omega
    subst hj0
    show okC (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat = true
    rw [eT, ti_facts.1]; exact ti_facts.2.2.2.2
  refine agreeBlk hsite (code_of L.lays rfl (hp ▸ wake_tiSub) (ofNat4_zero _)) tiSub_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m' hA hs => ?_) (fun σ c _ s m' hA hs => ?_)
  · have hk0 : k = 0 := by have : tiSub.length = 1 := by decide
                           omega
    subst hk0
    show (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat ≠ _
    rw [eT, ti_facts.1, eS, site_toNat]; omega
  · have hk0 : k = 0 := by have : tiSub.length = 1 := by decide
                           omega
    subst hk0
    have hsp := sp_of hA
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_ti hlab (.inl ?_) (spPool_of hband (k := -80) (by decide) (by decide) ?_)).trans
      (own2a0_eq L a).symm
    · unfold pcOf; rw [snd_of hs]; show (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat = _
      rw [eT]; rfl
    · rw [hm, hsp]; rfl
  · change Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab tiSub ⟨L.lab "scc_rt_thread_init", oW, σ⟩).so m'
      _ at hA
    change s.st = (m', (Spike.Lib.A64.Flow.arun L.lab tiSub ⟨L.lab "scc_rt_thread_init", oW, σ⟩).pc) at hs
    rw [tiSub_run] at hs
    have hsp := sp_of hA
    rw [tiSub_run] at hsp
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_ti hlab (.inr ?_) (spPool_of hband (k := -128) (by decide) (by decide) (by rw [hm]; exact hsp))).trans
      (own2a0_eq L a).symm
    unfold pcOf; rw [snd_of hs, eT]; exact ti_facts.2.1

/-- **`.sp6`'s block** (`sp6A`). -/
theorem n6_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {k : BitVec 64} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6 L.lab c0 t k cA m fr) sp6A := by
  have b6 := sp4In.2.2.2.1
  have e6 := lab_sp6 hlab (L := L)
  have eS := lab_site hlab (L := L)
  have hlen : sp6A.length = 3 := by decide
  refine blk_c hp hlo hsite hΛ (own2b L a 0) b6 (ofNat4_zero _) sp6A_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [e6, (sp6_facts j (by omega)).1]; exact (sp6_facts j (by omega)).2.2
  refine agreeBlk hsite (code_of L.lays rfl (hp ▸ b6) (ofNat4_zero _)) sp6A_ok hR hal hRlo hhi
    (fun j hj => ?_) (fun σ c _ j hj s m _ hs => own_sp6 hlab (by omega) (snd_of hs)) ?_
  · show (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * j)).toBitVec.toNat ≠ _
    rw [e6, (sp6_facts j (by omega)).1, eS, site_toNat]; omega
  · intro σ c _ s m' _ hs
    have e := snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab sp6A ⟨L.lab ".L21_wc_main.sp6", oW, σ⟩).pc at e
    rw [sp6A_run] at e
    exact own_sp6 hlab (k := 3) (by decide)
      (by rw [e, show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc])

/-- **The fence** (a row). -/
theorem n6f_wcG (a : BitVec 64) {k : BitVec 64} :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6f L.lab c0 t k cA m fr) := by
  have b6f := sp4In.2.2.2.2.1
  have e6 := lab_sp6 hlab (L := L)
  have eS := lab_site hlab (L := L)
  have hok : okPcOf lo wakeProg L.Λ (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 3)).toBitVec.toNat = true := by
    rw [okPc_eq hΛ, e6, (sp6_facts 3 (by decide)).1]; exact (sp6_facts 3 (by decide)).2.2
  refine node_c hsite (o := own2b L a 0)
    (WcW.nodeW_dmb_pre (InstOk.const (instOkW hp hlo a (fun _ => False) hsite (rS := rS)) _ False)
      (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) (hp ▸ b6f) rfl rfl c0N_cfacts hok (fun _ _ h => h) rfl) ?_
    (fun s hs => own_sp6 hlab (k := 3) (by decide) hs)
    (fun s hs => own_sp6 hlab (k := 4) (by decide) (by
      rw [hs]; show L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 3) + Int64.ofNat 4 = _; rw [Int64.add_assoc]; rfl)) ?_
  · show (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 3)).toBitVec.toNat ≠ _
    rw [e6, (sp6_facts 3 (by decide)).1, eS, site_toNat]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1 hp b6f h1 h2 h4'
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The clone's arguments** (`cloneArgs`), to the `svc`. -/
theorem n6a_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {k : BitVec 64} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6a L.lab c0 t k cA m fr) cloneArgs := by
  have b6a := sp4In.2.2.2.2.2
  have e6 := lab_sp6 hlab (L := L)
  have eS := lab_site hlab (L := L)
  have hlen : cloneArgs.length = 9 := by decide
  refine blk_c hp hlo hsite hΛ (own2b L a 0) b6a rfl cloneArgs_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [pc_add, e6, (sp6_facts (4 + j) (by omega)).1]; exact (sp6_facts (4 + j) (by omega)).2.2
  refine agreeBlk hsite (code_of L.lays rfl (hp ▸ b6a) rfl) cloneArgs_ok hR hal hRlo hhi
    (fun j hj => ?_) (fun σ c _ j hj s m _ hs => own_sp6 hlab (k := 4 + j) (by omega)
      (by rw [snd_of hs]; exact pc_add _ 4 j)) ?_
  · show (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * j)).toBitVec.toNat ≠ _
    rw [pc_add, e6, (sp6_facts (4 + j) (by omega)).1, eS, site_toNat]; omega
  · intro σ c _ s m' _ hs
    have e := snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab cloneArgs
      ⟨L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 4), oW, σ⟩).pc at e
    rw [cloneArgs_run] at e
    exact own_sp6 hlab (k := 13) (by decide) (by
      rw [e, show Int64.ofNat (4 * 4) = 16 from rfl,
        show Int64.ofNat (4 * 13) = 16 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
      simp only [Int64.add_assoc])

/-- **`WcSp4W` at `SFactsSt2`/`ownG`**, at the outside move of any range
`rS`: `wc_main`'s frame on a pool stack at the call (`hband`) and the tid
word's facts (`htidW`), both from `h1` (`A64WakeWcInv.H1Stmt`, at
`WcMidW.sp4`: main's frame facts and the second TCB in the pool). -/
theorem wcSp4W_wcG (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -128)
    (hhi : 0 ≤ R.hi) {F₂ : MachineData → Prop} (hband : BandTi L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2a L a 0) :
    WcSp4W (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F F₂ c0 t cA m fr :=
  ⟨n4_wcG hp hlo hΛ hlab hsite a hR hal (by omega) hhi, n4s_wcG hp hlo hΛ hlab hsite a htidW,
    n5_wcG hp hlo hΛ hlab hsite a hR hal (by omega) hhi hband, nI_wcG hp hlo hΛ hlab hsite a hR hal hRlo hhi hband,
    n6_wcG hp hlo hΛ hlab hsite a hR hal (by omega) hhi, n6f_wcG hp hlo hΛ hlab hsite a,
    n6a_wcG hp hlo hΛ hlab hsite a hR hal (by omega) hhi⟩

end Obl

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.sp4_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.sp4_facts

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.sp6_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.sp6_facts

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.ti_facts' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.ti_facts

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.own2a0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.own2a0_eq

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.own_sp4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.own_sp4

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.own_sp6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.own_sp6

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.own_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.own_ti

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.blkW_nodeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.blkW_nodeW

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.agreeBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.agreeBlk

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.blk_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.blk_c

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.node_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.node_c

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n4_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n4_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n4s_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n4s_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n5_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n5_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.nI_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.nI_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n6_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n6_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n6f_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n6f_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.n6a_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.n6a_wcG

/-- info: 'Spike.Lib.A64.WakePh.WcSp4W.wcSp4W_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcSp4W.wcSp4W_wcG

end Spike.Lib.A64.WakePh.WcSp4W
