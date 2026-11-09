/-
**hello.w's `wc_main` from `.sp4` to its `clone` inside `SFactsSt2` at
`ownGH`** (AArch64): the twin of
`Spike/Lib/A64WakeWcSp4W.lean` at helloProg, the `SFactsSt2` component of
the pre-spawn chain's `W` at `HelloWc.WcSp4WH`'s nodes
(`Spike/Lib/A64HelloWcSp3.lean`), `scc_rt_thread_init`'s entry, and
`WcSp6.WcSp6W`'s (`Spike/Lib/A64HelloWcSp6Seg.lean`), in `wc_main`'s
144-byte frame (`oWH`).

Each block and row is proved at a constant instance (`InstOk.const` of
`instOkH`, owned words `o`, no take phase, `A64Consumer.c0` for the source
control) and moved to `ownGH`, which is `o` at every pc of the block
and at its successors:

- `.sp4` to the call (`sp4AH`, the tid store, `initCallH`): `wc_main`'s
  range `[.sp4, .sp6)`, where `ownGH` is `own2aH (ph2aH pc) = own2aH 0`;
- `scc_rt_thread_init`'s entry (`nIH_wcGH`, its first instruction
  `sub sp, sp, #48`) on a pool stack: `own2bH (ph2bH pc) = own2bH 12 =
  own2aH 0` (`own2a0_eqH`);
- `.sp6` to the `svc` (`sp6AH`, the fence, `cloneArgsH`): `[.sp6,
  .stack_grow)`, where `ownGH` is `own2bH (ph2bH pc) = own2bH 0`.

The pcs and phases are decided by the kernel at the canonical base (`hlab`).

Open premises (as wake's): `hband : BandTiH L R` (`wc_main`'s frame on a
pool stack at the call, `sp = R.addr (-144)` and the callee's
`R.addr (-192)`), and `htidW` (the tid word `t + 56` mapped for writing,
unmapped in private memory under `F`, off `own2aH L a 0`).

- `tiSubH`, `hello_tiSub`: `scc_rt_thread_init`'s first instruction in
  hello's frame.
- `sp4_factsH`, `sp6_factsH`, `sp6_okH`, `ti_factsH`, `lab_sp4H`, `lab_sp6H`,
  `lab_tiH`, `lab_siteH`: the pcs and phases at the canonical base.
- `own_sp4H`, `own_sp6H`, `own_tiH`, `own2a0_eqH`: `ownGH` at the pcs;
  `BandTiH`, `spPool_ofH`: the call on a pool stack.
- `agreeBlkH`, `blk_cH`, `node_cH`: the generic moves to `ownGH`.
- `n4_wcGH` … `n6a_wcGH`, `nIH_wcGH`: the obligations; `wcSp4W_wcGH`,
  `wcSp6W_wcGH`: the results.
-/
import Spike.Lib.A64HelloWcPreWI
import Spike.Lib.A64HelloWcSp6Seg
import Spike.Lib.A64WakeWcSp4W

namespace Spike.Lib.A64.HelloPh.WcSp4W

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero code_of)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.HelloPh.WcSp6 (oWH wcN6H wcN6fH wcN6aH sp6AH cloneArgsH sp6AH_ok cloneArgsH_ok sp6AH_run
  cloneArgsH_run hello_wcSp6In wcSp6In WcSp6W)
open Spike.Lib.A64.Flow.HelloWc (aNH wcNIH sp4AH initCallH sp4AH_ok initCallH_ok sp4AH_run initCallH_run
  hello_wcSp3InH wcSp3InH WcSp4WH)
open Spike.Lib.A64.WakePh.WcSp4 (fenceB tidSt)
open Spike.Lib.A64.WakePh.WcSp4W (tiSub)
open Spike.Lib.A64.WakePh.WcW (c0N c0N_cfacts blkW_mapC nodeW_mapC)
open Spike.Lib.A64.Flow.WakeWc (tidSt_eq fenceB_eq)
open Spike.Lib.A64.WakePh (inPc spPool)

/-! ## `scc_rt_thread_init`'s first instruction -/

block_spec tiSubH (-192) 0 oWH tiSub

theorem hello_tiSub : blockAt SccCode.helloProg "scc_rt_thread_init" 0 tiSub = true := by decide +kernel

/-! ## The pcs at the canonical base -/

/-- `.sp4`'s six pcs: their values, `ph2aH` `0`, off the sites. -/
theorem sp4_factsH : ∀ k < 6, (Int64.ofNat 2169748 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169748 + 4 * k ∧
    ph2aHC (2169748 + 4 * k) = 0 ∧ okC (2169748 + 4 * k) = true := by decide +kernel

/-- `.sp6`'s twenty-six pcs (to the `svc`): their values, `ph2bH` `0`. -/
theorem sp6_factsH : ∀ k < 26, (Int64.ofNat 2169772 + Int64.ofNat (4 * k)).toBitVec.toNat = 2169772 + 4 * k ∧
    ph2bHC (2169772 + 4 * k) = 0 := by decide +kernel

/-- `.sp6`'s pcs before the `svc` are off the sites. -/
theorem sp6_okH : ∀ k < 25, okC (2169772 + 4 * k) = true := by decide +kernel

/-- `scc_rt_thread_init`'s first two pcs: their values, `ph2bH` `12`, the first off the sites. -/
theorem ti_factsH : (Int64.ofNat 2165284 + Int64.ofNat (4 * 0)).toBitVec.toNat = 2165284 ∧
    (Int64.ofNat 2165284 + 4).toBitVec.toNat = 2165288 ∧ ph2bHC 2165284 = 12 ∧ ph2bHC 2165288 = 12 ∧
    okC 2165284 = true := by decide +kernel

/-- The take site at the canonical base. -/
theorem site_toNatH : (Int64.ofNat 2165980).toBitVec.toNat = 2165980 := rfl

variable {L : RuntimeLayout} {a : BitVec 64}

theorem lab_sp4H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".L22_wc_main.sp4" = Int64.ofNat 2169748 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_sp6H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".L22_wc_main.sp6" = Int64.ofNat 2169772 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_tiH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_thread_init" = Int64.ofNat 2165284 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

theorem lab_siteH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165980 :=
  hlab _ _ (by rw [← codeT_eq]; decide +kernel)

/-! ## `ownGH` at the pcs -/

/-- The two second instances' owned words at the second switch. -/
theorem own2a0_eqH (L : RuntimeLayout) (a : BitVec 64) : own2aH L a 0 = own2bH L a 12 :=
  (own2aH_mod4 L a 16).trans (own2a_own2bH L a)

/-- **`ownGH` at `.sp4`'s pcs** is `own2aH L a 0`. -/
theorem own_sp4H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    {k : Nat} (hk : k < 6) (hs : s.st.2 = L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * k)) :
    ownGH L a s = own2aH L a 0 := by
  have hp : pcOf s = 2169748 + 4 * k := by unfold pcOf; rw [hs, lab_sp4H hlab]; exact (sp4_factsH k hk).1
  obtain ⟨-, -, -, -, e5, e6, -, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2aH L s := .inr (.inl (by unfold inPc; rw [e5, e6, hp]; omega))
  rw [ownGH_2a hlab hg, hp, ph2aH_eq, (sp4_factsH k hk).2.1]

/-- **`ownGH` at `.sp6`'s pcs to the `svc`** is `own2bH L a 0`. -/
theorem own_sp6H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    {k : Nat} (hk : k < 26) (hs : s.st.2 = L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * k)) :
    ownGH L a s = own2bH L a 0 := by
  have hp : pcOf s = 2169772 + 4 * k := by unfold pcOf; rw [hs, lab_sp6H hlab]; exact (sp6_factsH k hk).1
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2bH L s := .inr (.inl (by unfold inPc; rw [e6, e7, hp]; omega))
  rw [ownGH_2b hlab hg, hp, ph2bH_eq, (sp6_factsH k hk).2]

/-- **`ownGH` at `scc_rt_thread_init`'s first two pcs on a pool stack** is
`own2bH L a 12`. -/
theorem own_tiH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : pcOf s = 2165284 ∨ pcOf s = 2165288) (hsp : spPool L s) : ownGH L a s = own2bH L a 12 := by
  obtain ⟨-, -, e3, e4, -, -, -, -, -⟩ := labs_eqH hlab (L := L)
  have hg : Good2bH L s := .inl ⟨by unfold inPc; rw [e3, e4]; omega, hsp⟩
  rw [ownGH_2b hlab hg, ph2bH_eq]
  rcases hp with hp | hp <;> rw [hp]
  · rw [ti_factsH.2.2.1]
  · rw [ti_factsH.2.2.2.1]

/-- **`wc_main`'s frame on a pool stack at the call**: `sp` at the call
(`R.addr (-144)`) and past the callee's `sub` (`R.addr (-192)`) in
`(pool.lo, pool.lo + pool.size]`. -/
def BandTiH (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -192 ≤ k → k ≤ -144 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- `spPool` at `sp = R.addr k` in the band. -/
theorem spPool_ofH {R : Region} (hb : BandTiH L R) {s : State} {k : Int} (h1 : -192 ≤ k) (h2 : k ≤ -144)
    (hs : s.st.1.regs.SP.toBitVec = R.addr k) : spPool L s := by
  unfold spPool; rw [hs]; exact hb k h1 h2

/-! ## The generic moves -/

section Moves

variable {R : Region} {F : MachineData → Prop}

/-- **`ownGH` agrees with a constant `o` on a covered block**: at its pcs
(`hQ`) and at the pc its run ends at (`hlast`), its pcs off the take site. -/
theorem agreeBlkH (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {o : List (Loc × Val)} {n : ND} {blk : List Directive} {blo bhi : Int}
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ k < blk.length,
      (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, n.pc + Int64.ofNat (4 * k)) → ownGH L a s = o)
    (hlast : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.st = (m, (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) → ownGH L a s = o) :
    BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownGH L a s' = o)
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

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hsite

/-- **A covered `ret`-free block of helloProg inside `SFactsSt2` at
`ownGH`**, at the outside move of any range `rS`: `blkW_pre` at the constant
instance `o` (no take phase), the source control replaced by
`A64Consumer.c0`, moved to `ownGH` where it agrees with `o` (`hag`). -/
theorem blk_cH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (o : List (Loc × Val)) {Λ : Scc.Sem.Layout}
    {rS : Range} {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi) (hcl : blk.all (fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hag : BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  have h := Spike.Lib.A64.Rt.blkW_pre (InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) o False)
    (Λ := Λ) (lbl := fun _ => none) (rS := rS) (F := F) (n := c0N n) (hp ▸ hb) he hok hR hal hlo' hhi c0N_cfacts
    (ra := 0) (dead := fun _ => false)
    (by
      rw [he]
      exact Spike.Lib.A64.WakePh.Tcb2CallW.blkPh_const_of hcl fun j hj => by rw [okPc_eq hΛ]; exact hpc j hj)
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hag' : BlkW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) blk := by
    intro s σ c a1 a2 a3 a4 a5 a6 hJ k hk m a8 a9
    obtain ⟨-, c', hJ'⟩ := hJ
    exact hag s σ c' a1 a2 a3 a4 a5 a6 hJ' k hk m a8 a9
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 h) hag'
  exact blkW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

omit hp hlo in
/-- **A node of helloProg inside `SFactsSt2` at `ownGH`** from the constant
instance's `SFacts` at `c0N n` (`h`), `ownGH` `o` at its pc and the next
(`h0`, `h4`), its pc off the take site, each state at a 4-byte cell off
`svc` whose leaves are 4 bytes on (`hstep`). -/
theorem node_cH {o : List (Loc × Val)} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl} {K : State → State → Prop}
    {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.A64.PhRec.μ L) (fun _ => o) rS (fun _ => False) lbl s c) K
      L.exe L.endPc R F (c0N n))
    (hns : n.pc.toBitVec.toNat ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (h0 : ∀ s : State, s.st.2 = n.pc → ownGH L a s = o)
    (h4 : ∀ s : State, s.st.2 = n.pc + Int64.ofNat 4 → ownGH L a s = o)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => ownGH L a s = o ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownGH L a s' = o)
      (fun _ _ => False) L.exe L.endPc R F (c0N n) := by
    rintro s c ⟨h1, h2, h3, h4', σ, hA, hF, -, c', hJ⟩
    have hpc : s.st.2 = n.pc := h4'
    obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c' ⟨h1, h2, h3, hpc, σ, hA, hF, hJ⟩
    have hns' : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → pcOf s ≠ x := by
      intro x hx; rw [hsite] at hx; cases hx; unfold pcOf; rw [hpc]; exact hns
    exact ⟨⟨h0 s hpc, fun s' hs => h4 s' (by rw [Spike.Lib.A64.WakePh.WcW.succ_pc4 hc hd hex hl hns' hs, hpc])⟩,
      fun _ h => h⟩
  have h2 := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Moves

/-- The blocks' and rows' code facts. -/
theorem sp4InH : blockAt SccCode.helloProg ".L22_wc_main.sp4" 0 sp4AH = true ∧
    blockAt SccCode.helloProg ".L22_wc_main.sp4" 3 [Spike.Lib.A64.Flow.strDir .X9 .X10 56] = true ∧
    blockAt SccCode.helloProg ".L22_wc_main.sp4" 4 initCallH = true ∧
    blockAt SccCode.helloProg ".L22_wc_main.sp6" 0 sp6AH = true ∧
    blockAt SccCode.helloProg ".L22_wc_main.sp6" 11 [.instr ⟨.W64, .DMB .sy⟩] = true ∧
    blockAt SccCode.helloProg ".L22_wc_main.sp6" 12 cloneArgsH = true := by
  have h3 := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at h3
  obtain ⟨⟨⟨⟨⟨-, -⟩, b4⟩, b4s⟩, b5⟩, -⟩ := h3
  have h6 := hello_wcSp6In
  simp only [wcSp6In, Bool.and_eq_true] at h6
  obtain ⟨⟨⟨b6, b6f⟩, b6a⟩, -⟩ := h6
  rw [tidSt_eq] at b4s
  rw [fenceB_eq] at b6f
  exact ⟨b4, b4s, b5, b6, b6f, b6a⟩

/-! ## The obligations -/

section Obl

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  {Λ : Scc.Sem.Layout} {rS : Range} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
  {fr : BitVec 64 × BitVec 64}
include hp hlo hΛ hlab hsite

/-- **`.sp4`'s block** (`sp4AH`). -/
theorem n4_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n4) sp4AH := by
  have b4 := sp4InH.1
  have e4 := lab_sp4H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  have hlen : sp4AH.length = 3 := by decide
  refine blk_cH hp hlo hsite hΛ (own2aH L a 0) b4 (ofNat4_zero _) sp4AH_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [e4, (sp4_factsH j (by omega)).1]; exact (sp4_factsH j (by omega)).2.2
  refine agreeBlkH hsite (code_of L.lays rfl (hp ▸ b4) (ofNat4_zero _)) sp4AH_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m _ hs => own_sp4H hlab (by omega) (Spike.Lib.A64.WakePh.WcSp4W.snd_of hs)) ?_
  · show (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [e4, (sp4_factsH k (by omega)).1, eS, site_toNatH]; omega
  · intro σ c _ s m' _ hs
    have e := Spike.Lib.A64.WakePh.WcSp4W.snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab sp4AH ⟨L.lab ".L22_wc_main.sp4", oWH, σ⟩).pc at e
    rw [sp4AH_run] at e
    exact own_sp4H hlab (k := 3) (by decide)
      (by rw [e, show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc])

/-- **The tid store** (a row): `t + 56` mapped for writing, unmapped in
private memory under `F`, off `own2aH L a 0` (`htidW`). -/
theorem n4s_wcGH (a : BitVec 64)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2aH L a 0) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n4s) := by
  have b4s := sp4InH.2.1
  have e4 := lab_sp4H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  obtain ⟨hmw, hun, hno⟩ := htidW
  have hok : okPcOf lo SccCode.helloProg L.Λ
      (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat = true := by
    rw [okPc_eq hΛ, e4, (sp4_factsH 3 (by decide)).1]; exact (sp4_factsH 3 (by decide)).2.2
  refine node_cH hsite (o := own2aH L a 0)
    (Spike.Lib.A64.Rt.nodeW_st_pre (InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) _ False)
      (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) (ownOf := fun _ => own2aH L a 0) (fun _ => rfl)
      (hp ▸ b4s) rfl rfl c0N_cfacts hok (fun _ _ h => h) rfl ?_ hmw hun (fun _ w => hno w)) ?_
    (fun s hs => own_sp4H hlab (k := 3) (by decide) hs)
    (fun s hs => own_sp4H hlab (k := 4) (by decide) (by
      rw [hs]; show L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 3) + Int64.ofNat 4 = _; rw [Int64.add_assoc]; rfl)) ?_
  · rintro σ c ⟨-, c', -, -, h10, -⟩
    rw [Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; rfl
  · show (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 3)).toBitVec.toNat ≠ _
    rw [e4, (sp4_factsH 3 (by decide)).1, eS, site_toNatH]; omega
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, -, -, h10, -⟩
    have hc := Spike.Lib.A64.HelloPh.WcW.cell1H hp b4s h1 h2 h4'
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 56 = t + 56#64 := by
      rw [hAb.regs, Spike.Lib.A64.Flow.Ret0.rAddr_x10 h10]; rfl
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_str hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The call block** (`initCallH`), its end at `scc_rt_thread_init` on a
pool stack (`hband`). -/
theorem n5_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hband : BandTiH L R) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (aNH L.lab c0 t sl me cA fr .n5) initCallH := by
  have b5 := sp4InH.2.2.1
  have e4 := lab_sp4H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  have hlen : initCallH.length = 2 := by decide
  refine blk_cH hp hlo hsite hΛ (own2aH L a 0) b5 rfl initCallH_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [Spike.Lib.A64.WakePh.WcSp4W.pc_add, e4, (sp4_factsH (4 + j) (by omega)).1]
    exact (sp4_factsH (4 + j) (by omega)).2.2
  refine agreeBlkH hsite (code_of L.lays rfl (hp ▸ b5) rfl) initCallH_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m _ hs => own_sp4H hlab (k := 4 + k) (by omega)
      (by rw [Spike.Lib.A64.WakePh.WcSp4W.snd_of hs]; exact Spike.Lib.A64.WakePh.WcSp4W.pc_add _ 4 k)) ?_
  · show (L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4) + Int64.ofNat (4 * k)).toBitVec.toNat ≠ _
    rw [Spike.Lib.A64.WakePh.WcSp4W.pc_add, e4, (sp4_factsH (4 + k) (by omega)).1, eS, site_toNatH]; omega
  · intro σ c _ s m' hA hs
    change Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab initCallH
      ⟨L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4), oWH, σ⟩).so m' _ at hA
    change s.st = (m', (Spike.Lib.A64.Flow.arun L.lab initCallH
      ⟨L.lab ".L22_wc_main.sp4" + Int64.ofNat (4 * 4), oWH, σ⟩).pc) at hs
    rw [initCallH_run] at hs
    have hsp := Spike.Lib.A64.WakePh.WcSp4W.sp_of hA
    rw [initCallH_run] at hsp
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_tiH hlab (.inl ?_) (spPool_ofH hband (k := -144) (by decide) (by decide)
      (by rw [hm]; exact hsp))).trans (own2a0_eqH L a).symm
    unfold pcOf; rw [Spike.Lib.A64.WakePh.WcSp4W.snd_of hs, lab_tiH hlab]; rfl

/-- **`scc_rt_thread_init`'s entry** (the call node), on a pool stack
(`hband`): the first state of its first instruction's block. -/
theorem nIH_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hband : BandTiH L R) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcNIH L.lab c0 t sl me cA fr) := by
  have eT := lab_tiH hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  refine Spike.Lib.A64.WakePh.WcSp4W.blkW_nodeW (blk := tiSub) ?_ (by decide)
  refine blk_cH hp hlo hsite hΛ (own2aH L a 0) hello_tiSub (ofNat4_zero _) tiSubH_ok hR hal hRlo hhi (by decide)
    (by decide) (fun j hj => ?_) ?_
  · have hj0 : j = 0 := by
      have : tiSub.length = 1 := by decide
      omega
    subst hj0
    show okC (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat = true
    rw [eT, ti_factsH.1]; exact ti_factsH.2.2.2.2
  refine agreeBlkH hsite (code_of L.lays rfl (hp ▸ hello_tiSub) (ofNat4_zero _)) tiSubH_ok hR hal hRlo hhi
    (fun k hk => ?_) (fun σ c _ k hk s m' hA hs => ?_) (fun σ c _ s m' hA hs => ?_)
  · have hk0 : k = 0 := by
      have : tiSub.length = 1 := by decide
      omega
    subst hk0
    show (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat ≠ _
    rw [eT, ti_factsH.1, eS, site_toNatH]; omega
  · have hk0 : k = 0 := by
      have : tiSub.length = 1 := by decide
      omega
    subst hk0
    have hsp := Spike.Lib.A64.WakePh.WcSp4W.sp_of hA
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_tiH hlab (.inl ?_) (spPool_ofH hband (k := -144) (by decide) (by decide) ?_)).trans
      (own2a0_eqH L a).symm
    · unfold pcOf; rw [Spike.Lib.A64.WakePh.WcSp4W.snd_of hs]
      show (L.lab "scc_rt_thread_init" + Int64.ofNat (4 * 0)).toBitVec.toNat = _
      rw [eT]; rfl
    · rw [hm, hsp]; rfl
  · change Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab tiSub ⟨L.lab "scc_rt_thread_init", oWH, σ⟩).so m'
      _ at hA
    change s.st = (m', (Spike.Lib.A64.Flow.arun L.lab tiSub ⟨L.lab "scc_rt_thread_init", oWH, σ⟩).pc) at hs
    rw [tiSubH_run] at hs
    have hsp := Spike.Lib.A64.WakePh.WcSp4W.sp_of hA
    rw [tiSubH_run] at hsp
    have hm : s.st.1 = m' := by rw [hs]
    refine (own_tiH hlab (.inr ?_) (spPool_ofH hband (k := -192) (by decide) (by decide)
      (by rw [hm]; exact hsp))).trans (own2a0_eqH L a).symm
    unfold pcOf; rw [Spike.Lib.A64.WakePh.WcSp4W.snd_of hs, eT]; exact ti_factsH.2.1

/-- **`.sp6`'s block** (`sp6AH`). -/
theorem n6_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {k : BitVec 64} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6H L.lab c0 t k sl me cA fr) sp6AH := by
  have b6 := sp4InH.2.2.2.1
  have e6 := lab_sp6H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  have hlen : sp6AH.length = 11 := by decide
  refine blk_cH hp hlo hsite hΛ (own2bH L a 0) b6 (ofNat4_zero _) sp6AH_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [e6, (sp6_factsH j (by omega)).1]; exact sp6_okH j (by omega)
  refine agreeBlkH hsite (code_of L.lays rfl (hp ▸ b6) (ofNat4_zero _)) sp6AH_ok hR hal hRlo hhi
    (fun j hj => ?_) (fun σ c _ j hj s m _ hs => own_sp6H hlab (by omega) (Spike.Lib.A64.WakePh.WcSp4W.snd_of hs)) ?_
  · show (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * j)).toBitVec.toNat ≠ _
    rw [e6, (sp6_factsH j (by omega)).1, eS, site_toNatH]; omega
  · intro σ c _ s m' _ hs
    have e := Spike.Lib.A64.WakePh.WcSp4W.snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab sp6AH ⟨L.lab ".L22_wc_main.sp6", oWH, σ⟩).pc at e
    rw [sp6AH_run] at e
    exact own_sp6H hlab (k := 11) (by decide)
      (by rw [e, show Int64.ofNat (4 * 11) = 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
          simp only [Int64.add_assoc])

/-- **The fence** (a row). -/
theorem n6f_wcGH (a : BitVec 64) {k : BitVec 64} :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6fH L.lab c0 t k sl me cA fr) := by
  have b6f := sp4InH.2.2.2.2.1
  have e6 := lab_sp6H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  have hok : okPcOf lo SccCode.helloProg L.Λ
      (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 11)).toBitVec.toNat = true := by
    rw [okPc_eq hΛ, e6, (sp6_factsH 11 (by decide)).1]; exact sp6_okH 11 (by decide)
  refine node_cH hsite (o := own2bH L a 0)
    (Spike.Lib.A64.WakePh.WcW.nodeW_dmb_pre
      (InstOk.const (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) _ False)
      (Λ := Λ) (rS := rS) (lbl := fun _ => none) (F := F) (hp ▸ b6f) rfl rfl c0N_cfacts hok
      (fun _ _ h => h) rfl) ?_
    (fun s hs => own_sp6H hlab (k := 11) (by decide) hs)
    (fun s hs => own_sp6H hlab (k := 12) (by decide) (by
      rw [hs]; show L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 11) + Int64.ofNat 4 = _; rw [Int64.add_assoc]; rfl))
    ?_
  · show (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 11)).toBitVec.toNat ≠ _
    rw [e6, (sp6_factsH 11 (by decide)).1, eS, site_toNatH]; omega
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := Spike.Lib.A64.HelloPh.WcW.cell1H hp b6f h1 h2 h4'
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The clone's arguments** (`cloneArgsH`), to the `svc`. -/
theorem n6a_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {k : BitVec 64} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (wcN6aH L.lab c0 t k sl me cA fr) cloneArgsH := by
  have b6a := sp4InH.2.2.2.2.2
  have e6 := lab_sp6H hlab (L := L)
  have eS := lab_siteH hlab (L := L)
  have hlen : cloneArgsH.length = 13 := by decide
  refine blk_cH hp hlo hsite hΛ (own2bH L a 0) b6a rfl cloneArgsH_ok hR hal hRlo hhi (by decide) (by decide)
    (fun j hj => ?_) ?_
  · show okC (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 12) + Int64.ofNat (4 * j)).toBitVec.toNat = true
    rw [Spike.Lib.A64.WakePh.WcSp4W.pc_add, e6, (sp6_factsH (12 + j) (by omega)).1]
    exact sp6_okH (12 + j) (by omega)
  refine agreeBlkH hsite (code_of L.lays rfl (hp ▸ b6a) rfl) cloneArgsH_ok hR hal hRlo hhi
    (fun j hj => ?_) (fun σ c _ j hj s m _ hs => own_sp6H hlab (k := 12 + j) (by omega)
      (by rw [Spike.Lib.A64.WakePh.WcSp4W.snd_of hs]; exact Spike.Lib.A64.WakePh.WcSp4W.pc_add _ 12 j)) ?_
  · show (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 12) + Int64.ofNat (4 * j)).toBitVec.toNat ≠ _
    rw [Spike.Lib.A64.WakePh.WcSp4W.pc_add, e6, (sp6_factsH (12 + j) (by omega)).1, eS, site_toNatH]; omega
  · intro σ c _ s m' _ hs
    have e := Spike.Lib.A64.WakePh.WcSp4W.snd_of hs
    change s.st.2 = (Spike.Lib.A64.Flow.arun L.lab cloneArgsH
      ⟨L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 12), oWH, σ⟩).pc at e
    rw [cloneArgsH_run] at e
    exact own_sp6H hlab (k := 25) (by decide) (by
      rw [e, show Int64.ofNat (4 * 12) = 48 from rfl,
        show Int64.ofNat (4 * 25) = 48 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
      simp only [Int64.add_assoc])

/-- **`WcSp4WH` at `SFactsSt2`/`ownGH`**, at the outside move of any range
`rS`: `wc_main`'s frame on a pool stack at the call (`hband`) and the tid
word's facts (`htidW`). -/
theorem wcSp4W_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hband : BandTiH L R)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨t + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none) ∧ ∀ w, (⟨t + 56#64, 8⟩, w) ∉ own2aH L a 0) :
    WcSp4WH (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F c0 t sl me cA fr :=
  ⟨n4_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi, n4s_wcGH hp hlo hΛ hlab hsite a htidW,
    n5_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi hband⟩

/-- **`WcSp6W` at `SFactsSt2`/`ownGH`**, at the outside move of any range
`rS`, for any stack top `k`. -/
theorem wcSp6W_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {k : BitVec 64} :
    WcSp6W (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F c0 t k sl me cA fr :=
  ⟨n6_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi, n6f_wcGH hp hlo hΛ hlab hsite a,
    n6a_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi⟩

end Obl

end Spike.Lib.A64.HelloPh.WcSp4W

/-- info: 'Spike.Lib.A64.HelloPh.WcSp4W.own2a0_eqH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcSp4W.own2a0_eqH

/-- info: 'Spike.Lib.A64.HelloPh.WcSp4W.nIH_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcSp4W.nIH_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcSp4W.wcSp4W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcSp4W.wcSp4W_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcSp4W.wcSp6W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcSp4W.wcSp6W_wcGH
