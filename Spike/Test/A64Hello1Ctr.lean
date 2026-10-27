/-
**`hello1.w`'s counter add before the allocation** (AArch64): the context
`W0`'s counter write lives in (`CtxA`: `scc_rt_alloc`'s counter add for
`wc_rodata`'s call, in its region under the call's frame condition and
context `RdCtx`), and the consumer's counter row there (`hW0`'s `hctr`),
its landing in the greatest closed invariant inside `W0` (`hmax`).

- `fstable_aR`: the allocator's frame condition at `wc_rodata`'s call is
  stable under writes in its region.
- `FrameRun.eq_of_newBuf`: a control at a buffer allocation runs nowhere.
- `aR_al`: the allocator's region is aligned.
- `allocA_closedWS`: from any of the allocator's nodes or exits of `wc_rodata`'s
  call, no exit (the allocator from the node, the return impossible at the
  static placement, the heap abort run on into the abort path).
- `qswap`: the call at the counter add swapped to one with its premises.
- `CtxA`, `hctrA`: the context and the counter row at it.
-/
import Spike.Test.A64Hello1LevelsB
import Spike.Test.A64Hello1W0
import Spike.Test.A64Hello1Gfp
import Spike.Lib.A64CtrRow

namespace Spike.Test.A64Hello1Ctr

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS SegWS MemSide Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Hello1
open Spike.Lib.A64.Flow.Ret0 (TakeK LimOk MainG limA CallerCells)
open Spike.Lib.A64.Alloc (Call Ea AN AX)
open Spike.Lib.A64.Rt (MainE swFSL)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Test.A64Hello1CorrectA (Ih)
open SccCode (hello1Asm hello1Λ hello1Prog hello1Secs)

/-! ## The allocator's frame condition -/

/-- **The allocator's frame condition at `wc_rodata`'s call is stable**
under writes in its region: the caller's `F`, its cells outside holding
values (`CallerCells`), the call's context (`RdCtx`, its cells outside
kept). -/
theorem fstable_aR {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {lab : Label → Int64}
    {Jc : AS → Spike.Lib.Ctl → Prop} {q : Call} (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -48 + -160)
    (hkc : (-48 : Int) < R.hi) :
    FStable (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 0 m ∧ RdCtx ms lab R Jc q m) := by
  intro m m' hm hd
  have heq : ∀ k, R.Off k → ¬ (aR R).Off (k - -48) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo (by decide) hkc (by decide) (by decide) (by decide) hk hn)
  obtain ⟨h1, h2, mC, σC, c, hA, hJ, hN, hK⟩ := hm
  exact ⟨FStable.callee hR hlo (by decide) hkc (by omega) hF m m' h1 hd,
    fun k hk hn => by rw [heq k hk hn]; exact h2 k hk hn, mC, σC, c, hA, hJ, hN,
    fun k hk hn => (heq k hk hn).trans (hK k hk hn)⟩

/-- **The allocator's region at the call is 16-aligned** when the caller's
region is. -/
theorem aR_al {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48 + -160)
    (hhi : (-48 : Int) < R.hi) : (aR R).base.toNat % 16 = 0 := by
  have hb := Region.callee_base (hi' := 0) hR hlo (by decide) hhi
  have : (((aR R).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **A control at a buffer allocation runs nowhere**: no local step, no
call, no return. -/
theorem FrameRun.eq_of_newBuf {p : Prog} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} {x : String} {a : At}
    {τ : Ty} {e : Expr} (ht : c.term = .let_ x (.newBuf a τ) e) {q : Spike.Lib.Ctl × List TermRun.Frame}
    (h : FrameRun p (c, fs) q) : q = (c, fs) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    cases hs with
    | loc h' => exact absurd ht (h'.not_newBuf x a τ e)
    | call ht' => rw [ht] at ht'; cases ht'
    | ret ht' => rw [ht] at ht'; cases ht'

/-! ## No exit from the allocator of `wc_rodata`'s call -/

section Closed

open Spike.Test.A64Hello1LevelsB (P1A PreP hxa_pre)

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}

/-- **The allocator's frame condition at `wc_rodata`'s call** in `scc_rt_main`'s
region `swR v (-L) 0` at the caller's state `m0`, `σC`, for the call `q`
under the memory side `ms`. -/
abbrev FaA (ms : MemSide isaLSE2) (exe : _root_.Executable) (rT : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Spike.Lib.Ctl) (L : Int) (v : BitVec 64) (m0 : MachineData) (σC : AS) (q : Call) :
    MachineData → Prop := fun m =>
  mF (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) m0 σC m ∧
    CallerCells (mR (swR v (-L) 0)) (-48) (-160) 0 m ∧
    RdCtx ms (_root_.Executable.labels exe).label (mR (swR v (-L) 0))
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) q m

/-- **No exit from the allocator of `wc_rodata`'s call** at the level
before (`Ih lsize ⊥ inv1`, the static placement), from any of its nodes or
exits under `rodata`'s frame: the allocator from the node
(`seg_alloc_ofW_at`, its states inside `W` from cut A's premises `hP`, its
fresh-label landings in `inv1` by `hxa_pre`), its return impossible at the
static placement, its heap abort left to `wc_rodata`'s (`abs_leave`) and
run on into the abort path (`hello1_heapAb_segWS`). -/
theorem allocA_closedWS {W : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) (hL : setupL ≤ L)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64)
    (hP1 : ∀ l b n, hello1Λ.static l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
      ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs)
    {v : BitVec 64} (h16 : v.toNat % 16 = 0) (hok : (swR v (-L) 0).OK)
    (hP : PreP W K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
      endPc (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
      (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hsH : HAbStub W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
      (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J))
    (m0 : MachineData) (σC : AS)
    (q : AG (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
      [setupFrame e env]) (_root_.Executable.labels exe).label)
    (hra : q.1.ra = ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec) :
    SegWS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize)
      ((Next exe endPc (aR (mR (swR v (-L) 0)))
        (FaA (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
          [setupFrame e env]) exe rT tcb top c0 L v m0 σC q.1)
        (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1)
        (Spike.Lib.A64.Alloc.E (_root_.Executable.labels exe).label
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1 hello1Λ.static)).at [setupFrame e env])
      (fun _ _ _ => False) := by
  let lab := (_root_.Executable.labels exe).label
  have hF : FStable (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) := fun m m' h hd' =>
    ⟨Spike.Lib.A64.Rt.swF_stableL hfit hout m m' h.1 hd', Spike.Lib.A64.Flow.Ret0.stackOff_stable hfitS m m' h.2 hd'⟩
  have hlo : (swR v (-L) 0).lo ≤ -setupL := show -L ≤ -setupL by simp only [setupL] at hL ⊢; omega
  have hhi : (0 : Int) ≤ (swR v (-L) 0).hi := Int.le_refl _
  obtain ⟨hR', hal', hF'⟩ := mR_ok hok h16 hF (by simp only [setupL] at hlo; omega) hhi m0 σC
  have hRa : (aR (mR (swR v (-L) 0))).OK :=
    Region.callee_ok hR' (show (mR (swR v (-L) 0)).lo ≤ -48 + -160 by simp [Region.callee]) (by decide)
      (show (-48 : Int) < (mR (swR v (-L) 0)).hi by simp [Region.callee]) (by simp [Region.callee])
  have hala := aR_al hR' hal' (by simp [Region.callee]) (by simp [Region.callee])
  have hFa := fstable_aR (ms := msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static
    lsize [setupFrame e env]) (lab := lab) (q := q.1)
    (Jc := mRdJ0 (mNC lab (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) hR' hF'
    (show (mR (swR v (-L) 0)).lo ≤ -48 + -160 by simp [Region.callee])
    (show (-48 : Int) < (mR (swR v (-L) 0)).hi by simp [Region.callee])
  have hW := (hP.hW.rd m0 σC).alloc q.1 q.2 hra
  have hA := Spike.Lib.SegW.exists_pre fun i =>
    seg_alloc_ofW_at (p := p) (lbl := hello1Λ.static) hp hend hello1_alloc hFa hRa
    hala (by simp [Region.callee]) (by simp [Region.callee]) q.2
    (fun a ha m hm => hP.hmem q.1 q.2 a ha m hm.1.1)
    (fun l b w s c hl hAt =>
      (hxa_pre hP1 h16 hok hP).hxa m0 σC q _ (fun _ h => h.1) (fun _ h => h.2.2) l b w s c hl hAt)
    hW i
  have hE : SegWS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize)
      (Spike.Lib.Frag.at (fun s c => ∃ x, At exe endPc (aR (mR (swR v (-L) 0)))
        (FaA (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
          [setupFrame e env]) exe rT tcb top c0 L v m0 σC q.1)
        (Spike.Lib.A64.Alloc.E lab
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1 hello1Λ.static x) s c) [setupFrame e env])
      (fun _ _ _ => False) := by
    refine (hello1_heapAb_segWS hF hok h16 (by simp only [setupL] at hlo; omega) hhi rfl hsH _).mono_pre ?_
    rintro s c fs ⟨⟨x, h⟩, hfs⟩
    cases x
    · obtain ⟨-, -, -, -, σ, -, -, l, ini, old, hv, -⟩ := h
      obtain ⟨-, x, hx, -⟩ := hv
      simp only [Scc.Sem.wordAddr] at hx
      exact absurd hx (by rw [show hello1Λ.static _ = none from rfl]; exact nofun)
    · obtain ⟨he, hn, hdc, hpc, σ, hA, ⟨hD1, -, mC, σ', c', hAC, ⟨⟨σe, hJe, -, -⟩, -⟩, ⟨hc', -⟩, hK⟩, h2, hfull⟩ := h
      refine ⟨⟨m0, σC, he, hn, hdc, hpc, leave (aR (mR (swR v (-L) 0))) (-48) σ' σ,
        abs_leave hA hAC hK, hD1, h2, q, hfull, σe, hc' ▸ hJe⟩, hfs⟩
  refine ((SegWS.liftS [setupFrame e env] hA fun _ _ h => h).seq hE |>.or_pre hE).mono_pre ?_
  rintro s c fs ⟨h | h, hfs⟩
  · exact .inl ⟨h, hfs⟩
  · exact .inr ⟨h, hfs⟩

end Closed

/-! ## The counter's add in its context -/

section Ctx

open Spike.Test.A64Hello1LevelsB (P1A PreP okA)

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}

/-- **The call at the counter add, swapped to one with its premises**: at
`scc_rt_alloc`'s counter add for a call `q` under `wc_rodata`'s call
context (`RdCtx` at `rodata`'s allocation `rdJ' g`), a call `q'` with its
premises (from `hq`, `PreP.hq`, at the caller's source control) and `q`'s
`x29` and return address is at the same node: the control, header, count
and units agree, being the call node's registers. -/
theorem qswap {ms : MemSide isaLSE2} {R0 : Region} {F0 : MachineData → Prop} {m0 : MachineData} {σC : AS}
    {g : MainG} {q : Call} {s : State} {c : Spike.Lib.Ctl}
    (hq : ∀ σ c, rdJ' g σ c → ∃ q1 : Call, q1.OK ms (_root_.Executable.labels exe).label ∧ q1.c0 = c ∧
      q1.h = 257#64 ∧ q1.k = 2#64 ∧ q1.u ms = 3#64)
    (hAt : At exe endPc (aR (mR R0)) (fun m => mF R0 F0 m0 σC m ∧ CallerCells (mR R0) (-48) (-160) 0 m ∧
      RdCtx ms (_root_.Executable.labels exe).label (mR R0)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) q m)
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    ∃ q' : AG ms (_root_.Executable.labels exe).label, q'.1.ra = q.ra ∧
      At exe endPc (aR (mR R0)) (fun m => mF R0 F0 m0 σC m ∧ CallerCells (mR R0) (-48) (-160) 0 m ∧
        RdCtx ms (_root_.Executable.labels exe).label (mR R0)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) q'.1 m)
        (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms q'.1 .rmw) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, ⟨hmF, hCC, mC, σ', c1, hAbs, h1, h2, hK⟩, hJ⟩ := hAt
  have h1' := h1
  obtain ⟨⟨σe, ⟨-, ⟨σm, hrd, -⟩, -⟩, -, -⟩, hX0, hX1, hX2, -⟩ := h1'
  obtain ⟨q1, hok, hc1, hh1, hk1, hu1⟩ := hq σm c1 hrd
  obtain ⟨hcq, hx29, hra, hh, hk, hu⟩ := h2
  obtain ⟨⟨hc, ⟨s16, s8, s160, s152, s144⟩, hn28⟩, hX10, hX9⟩ := hJ
  have hqh : q.h = q1.h := hh.symm.trans (hX0.trans hh1.symm)
  have hqk : q.k = q1.k := hk.symm.trans (hX1.trans hk1.symm)
  have hqu : q.u ms = q1.u ms := hu.symm.trans (hX2.trans hu1.symm)
  have hn1 : q1.n < 2 ^ 28 := by
    have h := congrArg BitVec.toNat hqk
    simp only [Call.k, BitVec.toNat_ofNat] at h
    have := hok.n_lt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt this] at h
    omega
  refine ⟨⟨{ q1 with x29 := q.x29, ra := q.ra }, ⟨hok.term, hok.ev, hok.num, hok.hold, hok.n_lt, hok.ctr,
    hok.heap, hok.room, hok.cells, hok.units, hok.off, hok.accs, hok.rt, hok.mp, hok.grow, hok.hdr⟩⟩, rfl,
    he, hn, hdc, hpc, σ, hA, ⟨hmF, hCC, mC, σ', c1, hAbs, h1, ⟨hc1.symm, hx29, hra, hX0.trans hh1.symm,
      hX1.trans hk1.symm, hX2.trans hu1.symm⟩, hK⟩, ⟨⟨hc.trans (hcq.symm.trans hc1.symm),
      ⟨s16, s8, s160.trans hqh, s152.trans hqk, s144.trans hqu⟩, hn1⟩, hX10, hX9.trans hqu⟩⟩

/-- **The context of `W0`'s counter write**: `scc_rt_alloc`'s counter add
for `wc_rodata`'s call `q` (returning to `wc_rodata`'s `.sp0`) under
`rodata`'s frame, in the allocator's region under its frame condition
(`FaA`) for some aligned well-formed region `swR v (-L) 0` and caller's
state `m0`, `σC`. Any such call, as `RdPreW.alloc` quantifies: `hctrA`
swaps it to one with its premises (`qswap`). The memory side is the one of
no allocation fragment: `W0` comes before the levels' fragments, and the
node and the frame condition read none of it. -/
def CtxA (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS) (lsize : Lsize)
    (exe : _root_.Executable) (endPc : Int64) (rT : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Spike.Lib.Ctl)
    (L : Int) (e : Expr) (env : TermRun.Env) : FragS isaLSE2 := fun s c fs =>
  fs = [setupFrame e env] ∧ ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK ∧
    ∃ (m0 : MachineData) (σC : AS) (q : Call),
    q.ra = ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec ∧
    At exe endPc (aR (mR (swR v (-L) 0)))
      (FaA (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env]) exe rT
        tcb top c0 L v m0 σC q)
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env]) q .rmw) s c

/-- **The consumer's counter row in the context `CtxA`** (`hW0`'s `hctr`):
the control at the allocation runs nowhere (`FrameRun.eq_of_newBuf`), the
counter add's row (`ctrRow_alloc`) lands at the allocator's next node,
which is in every closed invariant inside `W` at the level before
(`allocA_closedWS`), so in `inv0` (`hmax`), so in `Ih`'s pre-allocation
branch. -/
theorem hctrA {W inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) (hL : setupL ≤ L)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64)
    (hP1 : ∀ l b n, hello1Λ.static l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
      ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs)
    (hPre : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      PreP W K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
        endPc (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) [setupFrame e env]
        (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hsH : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      HAbStub W K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
        (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J))
    (hmax : ∀ inv, SegInvS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
      ∀ s c fs, inv s c fs → inv0 s c fs) :
    ∀ s c fs, CtxA μ rd G own lsize exe endPc rT tcb top c0 L e env s c fs →
      ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs')
        (fun s' c'' => PendA p (Ih lsize inv0 inv1) hello1Λ.static lsize s' c'' fs') s c' := by
  rintro s c fs ⟨rfl, v, h16, hok, m0, σC, q0, hra0, hAt0⟩ c' fs' hrun -
  have hP := hPre v h16 hok
  obtain ⟨q, hra', hAt⟩ := qswap (ms := msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static
    lsize [setupFrame e env]) (fun σ c h => (hP.hq σ c h).imp fun q1 h => ⟨okA h.1, h.2⟩) hAt0
  have hra := hra'.trans hra0
  have hc : c = q.1.c0 := by
    obtain ⟨-, -, -, -, σ, -, -, hJ, -⟩ := hAt
    exact hJ.1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf (hc ▸ q.2.term) hrun)
  let qI : AG (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
      [setupFrame e env]) (_root_.Executable.labels exe).label := ⟨q.1, okA q.2⟩
  obtain ⟨inv, hinv, hS⟩ := SegInvS.ofSegWS
    (allocA_closedWS hp hend hL hfit hout hfitS hP1 h16 hok hP (hsH v h16 hok) m0 σC qI hra)
  have hF : FStable (swR v (-L) 0) (swFSL L rT top (limA (UInt64.ofBitVec tcb)) v) := fun m m' h hd' =>
    ⟨Spike.Lib.A64.Rt.swF_stableL hfit hout m m' h.1 hd', Spike.Lib.A64.Flow.Ret0.stackOff_stable hfitS m m' h.2 hd'⟩
  have hlo : (swR v (-L) 0).lo ≤ -setupL := show -L ≤ -setupL by simp only [setupL] at hL ⊢; omega
  obtain ⟨hR', -, hF'⟩ := mR_ok hok h16 hF (by simp only [setupL] at hlo; omega) (Int.le_refl _) m0 σC
  have hFa := fstable_aR (ms := msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static
    lsize [setupFrame e env]) (lab := (_root_.Executable.labels exe).label) (q := q.1)
    (Jc := mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) hR' hF'
    (show (mR (swR v (-L) 0)).lo ≤ -48 + -160 by simp [Region.callee])
    (show (-48 : Int) < (mR (swR v (-L) 0)).hi by simp [Region.callee])
  have hrow := Spike.Lib.A64.Alloc.ctrRow_alloc (lbl := hello1Λ.static)
    (ms := msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize [setupFrame e env]) hFa
    (okA q.2) (alloc_code hp hend hello1_alloc) (fun m hm => hP.hmem q.1 (okA q.2) _ (.inl rfl) m hm.1.1) hAt
  obtain ⟨k, op, g, x, a, τ, e', ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrow
  refine ⟨k, op, g, x, a, τ, e', ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle => ?_⟩
  obtain ⟨hG', hX⟩ := h9 old hG hown hle
  refine ⟨hG', fun h => absurd h (List.cons_ne_nil _ _), Spike.Lib.Pend.of (.inl ⟨rfl, rfl, ?_⟩)⟩
  exact hmax inv hS _ _ _ (hinv _ _ _ ⟨hX, rfl⟩)

end Ctx

/-- info: 'Spike.Test.A64Hello1Ctr.allocA_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocA_closedWS

/-- info: 'Spike.Test.A64Hello1Ctr.hctrA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hctrA

/-- info: 'Spike.Test.A64Hello1Ctr.qswap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qswap

end Spike.Test.A64Hello1Ctr
