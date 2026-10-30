/-
**`hello1.w`'s counter add before the allocation** (x86-64): the context
`W0`'s counter write lives in (`CtxA`: `scc_rt_alloc`'s counter add for
`wc_rodata`'s call, in its region under the call's frame condition and
context `RdCtx`), and the consumer's counter row there (`hW0`'s `hctr`),
its landing in the greatest closed invariant inside `W0` (`hmax`). The
x86-64 twin of `Spike/Test/A64Hello1Ctr.lean`.

- `fstable_aR`: the allocator's frame condition at `wc_rodata`'s call is
  stable under writes in its region.
- `FrameRun.eq_of_newBuf`: a control at a buffer allocation runs nowhere.
- `allocA_closedWS`: from any of the allocator's nodes or exits of `wc_rodata`'s
  call, no exit (the allocator from the node, the return impossible at the
  static placement, the heap abort run on into the abort path).
- `qswap`: the call at the counter add swapped to one with its premises.
- `CtxA`, `hctrA`: the context and the counter row at it.

Where x86-64 differs from AArch64: `scc_rt_main`'s region is `mainR v L`
under `mainF` (no alignment premise on `v`, so no `aR_al`); the
allocator's region `aR` keeps the return address cell above (`hi' = 8`);
the allocator returns to `wc_rodata`'s `.x13`; the call's frame record is
`fp` (`%rbp`) for `x29`; the heap abort's node is left to `wc_rodata`'s
region by `at_leave`.
-/
import Spike.Test.X64Hello1LevelsB
import Spike.Test.X64Hello1W0
import Spike.Test.X64Hello1Gfp
import Spike.Lib.X64CtrRow

namespace Spike.Test.X64Hello1Ctr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS SegWS MemSide Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Hello1
open Spike.Lib.X64.Flow.Ret0 (TakeK LimOk MainG limA tpOf CallerCells)
open Spike.Lib.X64.Alloc (Call Ea AN AX)
open Spike.Lib.X64.Rt (MainE swFSL mainE_ok)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Test.X64Hello1CorrectA (Ih)
open SccCode (hello1Asm hello1Λ hello1Cells hello1Secs)

/-! ## The allocator's frame condition -/

/-- **The allocator's frame condition at `wc_rodata`'s call is stable**
under writes in its region: the caller's `F`, its cells outside holding
values (`CallerCells`), the call's context (`RdCtx`, its cells outside
kept). -/
theorem fstable_aR {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {lab : Label → Int64}
    {Jc : AS → Spike.Lib.Ctl → Prop} {q : Call} (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ -48 + -160)
    (hhi : (-48 : Int) + 8 ≤ R.hi) :
    FStable (aR R) (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧ RdCtx ms lab R Jc q m) := by
  intro m m' hm hd
  have heq : ∀ k, R.Off k → ¬ (aR R).Off (k - -48) →
      Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 := fun k hk hn =>
    hd _ (R.addr_fit hR hk)
      (Region.callee_sep hR hlo (by decide) (by omega) (by decide) (by decide) (by decide) hk hn)
  obtain ⟨h1, h2, mC, σC, c, hA, hJ, hN, hK⟩ := hm
  exact ⟨FStable.callee hR hlo (by decide) (by omega) hhi hF m m' h1 hd,
    fun k hk hn => by rw [heq k hk hn]; exact h2 k hk hn, mC, σC, c, hA, hJ, hN,
    fun k hk hn => (heq k hk hn).trans (hK k hk hn)⟩

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

open Spike.Test.X64Hello1LevelsB (P1A PreP hxa_pre)

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}

/-- **The allocator's frame condition at `wc_rodata`'s call** in `scc_rt_main`'s
region `mainR v L` at the caller's state `m0`, `σC`, for the call `q`
under the memory side `ms`. -/
abbrev FaA (ms : MemSide isa) (exe : _root_.Executable) (rT : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Spike.Lib.Ctl) (L : Int) (v : BitVec 64) (m0 : MachineData) (σC : AS) (q : Call) :
    MachineData → Prop := fun m =>
  mF (mainR v L) (mainF rT tcb top v L) m0 σC m ∧ CallerCells (mR (mainR v L)) (-48) (-160) 8 m ∧
    RdCtx ms (_root_.Executable.labels exe).label (mR (mainR v L))
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC) q m

/-- **No exit from the allocator of `wc_rodata`'s call** at the level
before (`Ih lsize ⊥ inv1`, the static placement), from any of its nodes or
exits under `rodata`'s frame: the allocator from the node
(`seg_allocW_at`, its states inside `W` from cut A's premises `hP`, its
fresh-label landings in `inv1` by `hxa_pre`), its return impossible at the
static placement, its heap abort left to `wc_rodata`'s (`at_leave`) and
run on into the abort path (`hello1_heapAb_segWS`). -/
theorem allocA_closedWS {W : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells) (hL : setupL + 8 ≤ L) (hL8 : L % 8 = 0)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64)
    (hP1 : ∀ l b n, hello1Λ.static l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
      ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs)
    {v : BitVec 64} (hok : (swR v (-L) 0).OK)
    (hP : PreP W K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
      endPc (mainR v L) (mainF rT tcb top v L) [setupFrame e env] (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩))
    (hsH : HAbStub W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
      (mainR v L) (mainF rT tcb top v L) (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J))
    (m0 : MachineData) (σC : AS)
    (q : AG (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
      [setupFrame e env]) (_root_.Executable.labels exe).label)
    (hra : q.1.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x13").toBitVec) :
    SegWS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize)
      ((Next exe endPc (aR (mR (mainR v L)))
        (FaA (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
          [setupFrame e env]) exe rT tcb top c0 L v m0 σC q.1)
        (Alloc.N (_root_.Executable.labels exe).label
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1)
        (Alloc.E (_root_.Executable.labels exe).label
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1 hello1Λ.static)).at [setupFrame e env])
      (fun _ _ _ => False) := by
  let lab := (_root_.Executable.labels exe).label
  obtain ⟨hR, hF⟩ := mainE_ok (show 8 ≤ L by simp only [setupL] at hL; omega) hL8 hok hfit hout hfitS
  obtain ⟨hR', hF'⟩ := mR_ok hR hF (show 8 - L ≤ -288 by simp only [setupL] at hL; omega)
    (show (8 : Int) ≤ 8 by decide) m0 σC
  have hRa : (aR (mR (mainR v L))).OK :=
    Region.callee_ok hR' (show (-208 : Int) ≤ -48 + -160 by decide) (by decide)
      (show (-48 : Int) < 8 by decide) (show (-48 : Int) + 8 ≤ 8 by decide)
  have hFa := fstable_aR (ms := msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static
    lsize [setupFrame e env]) (lab := lab) (q := q.1)
    (Jc := mRdJ0 (mNC lab (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC) hR' hF'
    (show (-208 : Int) ≤ -48 + -160 by decide) (show (-48 : Int) + 8 ≤ 8 by decide)
  have hW := (hP.hW.rd m0 σC).alloc q.1 q.2 hra
  have hA := Spike.Lib.SegW.exists_pre fun i =>
    Alloc.seg_allocW_at (p := p) (lbl := hello1Λ.static) hp hend Alloc.hello1_allocIn hFa hRa
    (show (-160 : Int) ≤ -160 by decide) (show (8 : Int) ≤ 8 by decide) q.2
    (fun a ha m hm => hP.hmem q.1 q.2 a ha m hm.1.1)
    (fun l b w s c hl hAt =>
      (hxa_pre hP1 hok hP).hxa m0 σC q _ (fun _ h => h.1) (fun _ h => h.2.2) l b w s c hl hAt)
    hW i
  have hE : SegWS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize)
      (Spike.Lib.Frag.at (fun s c => ∃ x, At exe endPc (aR (mR (mainR v L)))
        (FaA (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
          [setupFrame e env]) exe rT tcb top c0 L v m0 σC q.1)
        (Alloc.E lab
          (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) q.1 hello1Λ.static x) s c) [setupFrame e env])
      (fun _ _ _ => False) := by
    refine (hello1_heapAb_segWS hF hR (show 8 - L ≤ -320 by simp only [setupL] at hL; omega)
      (show (8 : Int) ≤ 8 by decide) rfl hsH _).mono_pre ?_
    rintro s c fs ⟨⟨x, h⟩, hfs⟩
    cases x
    · obtain ⟨-, -, -, -, σ, -, -, l, ini, old, hv, -⟩ := h
      obtain ⟨-, x, hx, -⟩ := hv
      simp only [Scc.Sem.wordAddr] at hx
      exact absurd hx (by rw [show hello1Λ.static _ = none from rfl]; exact nofun)
    · have h' : At exe endPc (aR (mR (mainR v L)))
          (FaA (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
            [setupFrame e env]) exe rT tcb top c0 L v m0 σC q.1)
          ⟨lab "scc_rt_abort", ⟨-160, []⟩, (Alloc.E lab
            (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize
              [setupFrame e env]) q.1 hello1Λ.static .abort).J⟩ s c := by
        obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
        exact ⟨he, hn, hdc, hpc, σ, Abs.weaken (show SO.le ⟨-160, []⟩ ⟨-160, [(.rbp, -8)]⟩ = true by decide) hA, hD, hJ⟩
      have hl := at_leave (R := mR (mainR v L)) (F := mF (mainR v L) (mainF rT tcb top v L) m0 σC)
        (kb := -48) (lo' := -160) (hi' := 8) (e := -160)
        (P := fun _ => ∃ σe, mRdJ0 (mNC lab (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC σe q.1.c0)
        rfl (fun m hm => by
          obtain ⟨hmF, -, mC, σC', c1, hAbs, ⟨⟨σe, hJe, -⟩, -⟩, ⟨hc1, -⟩, hK⟩ := hm
          exact ⟨hmF, mC, σC', _, hK, hAbs, σe, hc1 ▸ hJe⟩) h'
      obtain ⟨he, hn, hdc, hpc, σ', hA', hD', σx, σC', ⟨h2, hfull⟩, hJe, rfl⟩ := hl
      exact ⟨⟨m0, σC, he, hn, hdc, hpc, _, hA', hD', h2, q, hfull, hJe⟩, hfs⟩
  refine ((SegWS.liftS [setupFrame e env] hA fun _ _ h => h).seq hE |>.or_pre hE).mono_pre ?_
  rintro s c fs ⟨h | h, hfs⟩
  · exact .inl ⟨h, hfs⟩
  · exact .inr ⟨h, hfs⟩

end Closed

/-! ## The counter's add in its context -/

section Ctx

open Spike.Test.X64Hello1LevelsB (P1A PreP okA)

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {rT : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {e : Expr} {env : TermRun.Env}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The call at the counter add, swapped to one with its premises**: at
`scc_rt_alloc`'s counter add for a call `q` under `wc_rodata`'s call
context (`RdCtx` at `rodata`'s allocation `rdJ' g`), a call `q'` with its
premises (from `hq`, `PreP.hq`, at the caller's source control) and `q`'s
`fp` and return address is at the same node: the control, header, count
and units agree, being the call node's registers. -/
theorem qswap {ms : MemSide isa} {R0 : Region} {F0 : MachineData → Prop} {m0 : MachineData} {σC : AS}
    {g : MainG} {q : Call} {s : State} {c : Spike.Lib.Ctl}
    (hq : ∀ σ c, rdJ' g σ c → ∃ q1 : Call, q1.OK ms (_root_.Executable.labels exe).label ∧ q1.c0 = c ∧
      q1.h = 257#64 ∧ q1.k = 2#64 ∧ q1.u ms = 3#64)
    (hAt : At exe endPc (aR (mR R0)) (fun m => mF R0 F0 m0 σC m ∧ CallerCells (mR R0) (-48) (-160) 8 m ∧
      RdCtx ms (_root_.Executable.labels exe).label (mR R0)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R0 (rdJ' g)).J σC) q m)
      (Alloc.N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    ∃ q' : AG ms (_root_.Executable.labels exe).label, q'.1.ra = q.ra ∧
      At exe endPc (aR (mR R0)) (fun m => mF R0 F0 m0 σC m ∧ CallerCells (mR R0) (-48) (-160) 8 m ∧
        RdCtx ms (_root_.Executable.labels exe).label (mR R0)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R0 (rdJ' g)).J σC) q'.1 m)
        (Alloc.N (_root_.Executable.labels exe).label ms q'.1 .rmw) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, ⟨hmF, hCC, mC, σ', c1, hAbs, h1, h2, hK⟩, hJ⟩ := hAt
  have h1' := h1
  obtain ⟨⟨σe, ⟨-, ⟨σm, hrd, -⟩⟩, -⟩, -, hX0, hX1, hX2, -⟩ := h1'
  obtain ⟨q1, hok, hc1, hh1, hk1, hu1⟩ := hq σm c1 hrd
  obtain ⟨hcq, hfp, hra, hh, hk, hu⟩ := h2
  obtain ⟨⟨hc, ⟨s0, s8, s16, s24, s32⟩, hn28⟩, hrcx, hrax⟩ := hJ
  have hqh : q.h = q1.h := hh.symm.trans (hX0.trans hh1.symm)
  have hqk : q.k = q1.k := hk.symm.trans (hX1.trans hk1.symm)
  have hqu : q.u ms = q1.u ms := hu.symm.trans (hX2.trans hu1.symm)
  have hn1 : q1.n < 2 ^ 28 := by
    have h := congrArg BitVec.toNat hqk
    simp only [Call.k, BitVec.toNat_ofNat] at h
    have := hok.n_lt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt this] at h
    omega
  refine ⟨⟨{ q1 with fp := q.fp, ra := q.ra }, { hok with }⟩, rfl,
    he, hn, hdc, hpc, σ, hA, ⟨hmF, hCC, mC, σ', c1, hAbs, h1, ⟨hc1.symm, hfp, hra, hX0.trans hh1.symm,
      hX1.trans hk1.symm, hX2.trans hu1.symm⟩, hK⟩, ⟨⟨hc.trans (hcq.symm.trans hc1.symm),
      ⟨s0, s8, s16.trans hqh, s24.trans hqk, s32.trans hqu⟩, hn1⟩, hrcx, hrax.trans hqu⟩⟩

/-- **The context of `W0`'s counter write**: `scc_rt_alloc`'s counter add
for `wc_rodata`'s call `q` (returning to `wc_rodata`'s `.x13`) under
`rodata`'s frame, in the allocator's region under its frame condition
(`FaA`) for some well-formed region `swR v (-L) 0` and caller's state
`m0`, `σC`. Any such call, as `RdPreW.alloc` quantifies: `hctrA` swaps it
to one with its premises (`qswap`). The memory side is the one of no
allocation fragment: `W0` comes before the levels' fragments, and the node
and the frame condition read none of it. -/
def CtxA (μ : Marks) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (own : OwnS) (lsize : Lsize)
    (exe : _root_.Executable) (endPc : Int64) (rT : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Spike.Lib.Ctl)
    (L : Int) (e : Expr) (env : TermRun.Env) : FragS isa := fun s c fs =>
  fs = [setupFrame e env] ∧ ∃ v : BitVec 64, (swR v (-L) 0).OK ∧
    ∃ (m0 : MachineData) (σC : AS) (q : Call),
    q.ra = ((_root_.Executable.labels exe).label ".Lwc_rodata.x13").toBitVec ∧
    At exe endPc (aR (mR (mainR v L)))
      (FaA (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env]) exe rT
        tcb top c0 L v m0 σC q)
      (Alloc.N (_root_.Executable.labels exe).label
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static lsize [setupFrame e env]) q .rmw) s c

/-- **The consumer's counter row in the context `CtxA`** (`hW0`'s `hctr`):
the call swapped to one with its premises (`qswap`), the control at the
allocation runs nowhere (`FrameRun.eq_of_newBuf`), the counter add's row
(`ctrRow_alloc`) lands at the allocator's next node, which is in every
closed invariant inside `W` at the level before (`allocA_closedWS`), so in
`inv0` (`hmax`), so in `Ih`'s pre-allocation branch. -/
theorem hctrA {W inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells) (hL : setupL + 8 ≤ L) (hL8 : L % 8 = 0)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rT.lo + rT.size ≤ 2 ^ 64)
    (hP1 : ∀ l b n, hello1Λ.static l = none → Spike.Lib.HeapLand.AllocLand ar.heap ar.cells b n →
      ∀ s c fs, P1A μ rd G own lsize exe endPc rT tcb top c0 L e env l b n s c fs → inv1 l b n s c fs)
    (hPre : ∀ v : BitVec 64, (swR v (-L) 0).OK →
      PreP W K (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe
        endPc (mainR v L) (mainF rT tcb top v L) [setupFrame e env] (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩))
    (hsH : ∀ v : BitVec 64, (swR v (-L) 0).OK →
      HAbStub W K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) exe endPc
        (mainR v L) (mainF rT tcb top v L) (setupFrame e env)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J))
    (hmax : ∀ inv, SegInvS W K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
      ∀ s c fs, inv s c fs → inv0 s c fs) :
    ∀ s c fs, CtxA μ rd G own lsize exe endPc rT tcb top c0 L e env s c fs →
      ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs')
        (fun s' c'' => PendA p (Ih lsize inv0 inv1) hello1Λ.static lsize s' c'' fs') s c' := by
  rintro s c fs ⟨rfl, v, hok, m0, σC, q0, hra0, hAt0⟩ c' fs' hrun -
  have hP := hPre v hok
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
    (allocA_closedWS hp hend hL hL8 hfit hout hfitS hP1 hok hP (hsH v hok) m0 σC qI hra)
  obtain ⟨hR, hF⟩ := mainE_ok (show 8 ≤ L by simp only [setupL] at hL; omega) hL8 hok hfit hout hfitS
  obtain ⟨hR', hF'⟩ := mR_ok hR hF (show 8 - L ≤ -288 by simp only [setupL] at hL; omega)
    (show (8 : Int) ≤ 8 by decide) m0 σC
  have hFa := fstable_aR (ms := msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) hello1Λ.static
    lsize [setupFrame e env]) (lab := (_root_.Executable.labels exe).label) (q := q.1)
    (Jc := mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC)
    hR' hF' (show (-208 : Int) ≤ -48 + -160 by decide) (show (-48 : Int) + 8 ≤ 8 by decide)
  have hrow := Alloc.ctrRow_alloc (lbl := hello1Λ.static)
    (ms := msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize [setupFrame e env]) hp hend
    Alloc.hello1_allocIn hFa (okA q.2) (fun m hm => hP.hmem q.1 (okA q.2) _ (.inl rfl) m hm.1.1) hAt
  obtain ⟨k, op, g, x, a, τ, e', ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrow
  refine ⟨k, op, g, x, a, τ, e', ta, ws, n, h1, h2, h3, h4, h5, h6, h7, h8, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hX⟩ := h9 old hG hown hle hlo
  refine ⟨hG', fun h => absurd h (List.cons_ne_nil _ _), Spike.Lib.Pend.of (.inl ⟨rfl, rfl, ?_⟩)⟩
  exact hmax inv hS _ _ _ (hinv _ _ _ ⟨hX, rfl⟩)

end Ctx

/-- info: 'Spike.Test.X64Hello1Ctr.allocA_closedWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocA_closedWS

/-- info: 'Spike.Test.X64Hello1Ctr.hctrA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hctrA

/-- info: 'Spike.Test.X64Hello1Ctr.qswap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qswap

end Spike.Test.X64Hello1Ctr
