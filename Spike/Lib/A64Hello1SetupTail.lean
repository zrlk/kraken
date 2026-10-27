/-
**`hello1.w`'s `scc_rt_main` at the setup block's source with its abort
tails** (AArch64): the exits of `hello1_setup_main_segWS`,
`hello1_setup_segWS` and `hello1_main_post_segWS`
(`Spike/Lib/A64Hello1SetupGlue.lean`, `Spike/Lib/A64Hello1SetupPost.lean`)
run on into the abort paths, which do not return, so each segment has no
exit. The abort paths' obligations stay premises (`StubWW`, `StubHW`, e.g.
`stubWW_of_code`, `stubHW_of_code`).

`print`'s abort (`mAb`, `x0 = 4`, at `-224` in `scc_rt_main`'s region) is
`Abort.Disp.seg_jabort4W` there. The heap abort (`rX .abort`, `x0 = 2`) is
at `-208` in `wc_rodata`'s region `mR R`, whose `-208` floor leaves the
dispatcher no room; the node is first left to `scc_rt_main`'s region
(`at_leaveE`, at `-80 - 208 = -288`), where the dispatcher runs below it
down to `-336` (`setupL`).

- `at_leaveE`: `at_leave` for a callee's node at any `sp` offset `e`.
- `Abort.Disp.seg_jabort2W_up`: `seg_jabort2W` from a node of a callee's
  region, the dispatcher in the caller's region below the node.
- `hello1_mAb_segWS`: `print`'s abort at any frames, into any fragment.
- `hello1_heapAb_segWS`: the heap abort under `rodata`'s frame, into any
  fragment.
- `hello1_setup_main_closedWS`, `hello1_setup_closedWS`: from
  `scc_rt_main`'s entry (the start's entry) at the setup block's source, no
  exit (the allocation's level before it).
- `hello1_main_post_closedWS`: from `wc_rodata`'s `.sp0` under `rodata`'s
  frame, no exit (the level after the allocation).
-/
import Spike.Lib.A64Hello1SetupGlue
import Spike.Lib.A64AbortHeapS
import Spike.Lib.A64AbortWriteW

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

section Leave

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **Leaving the callee's region at any offset**: `at_leave` for a node
`x` of the callee at `sp` offset `e`, at `kc + e = k` in the caller's
region. -/
theorem at_leaveE {kc lo' hi' e k : Int} {F' : MachineData → Prop} {P : AS → Prop} {x : ND}
    (hx : x.o = ⟨e, []⟩) (hk : kc + e = k)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC ∧ P σC)
    {s : State} {c : Ctl} (h : At exe endPc (R.callee kc lo' hi') F' x s c) :
    At exe endPc R F ⟨x.pc, ⟨k, []⟩, fun σ c => ∃ σx σC, x.J σx c ∧ P σC ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩ s c := by
  subst hk
  obtain ⟨he, hn, hdc, hpc, σx, hAx, hD, hJx⟩ := h
  obtain ⟨hDF, m0, σC, o, hK, hAC, hP⟩ := hF' _ hD
  refine ⟨he, hn, hdc, hpc, leave (R.callee kc lo' hi') kc σC σx, ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩, hDF,
    σx, σC, hJx, hP, rfl⟩
  · intro r k' hr
    rcases r with y | _
    · cases hr
    · simp only [SO.get, Option.some.injEq] at hr
      subst hr
      have := hAx.so .SP e (by rw [hx]; rfl)
      simp only [leave] at this ⊢
      rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kc lo' hi').Off (k - kc)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hK k hk hin]; exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

end Leave

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.Abort.Disp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A jump to `scc_rt_abort` with `x0 = 2` from a callee's region does
not return**: from a node `nX` of the callee's region (at `kc`, `sp` at
`e`, `F'` giving the caller's `F` and its cells outside as in a caller's
state) the node left to the caller's region at `k = kc + e` (`at_leaveE`),
then `seg_jabort2W` there, the dispatcher below `k`. -/
theorem seg_jabort2W_up {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    {kc lo' hi' e k : Int} {F' : MachineData → Prop} {nX : ND} (hx : nX.o = ⟨e, []⟩) (hk : kc + e = k)
    (hpc : nX.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hX0 : ∀ σ c, nX.J σ c → σ.regs.X0.toBitVec.toNat = 2)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Flow.Abs R o m0 σC)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ k - 48)
    (hkc : k < R.hi) (h16 : k % 16 = 0) (hK : ms.K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0, (∃ σx, nX.J σx c0) → StubHW W K p lbl ms exe endPc (R.callee k (-48) 0)
      (fun m => F m ∧ CKept R k (-48) 0 m0 m ∧ Flow.Abs R ⟨k, []⟩ m0 σC) c0) :
    SegW W K p lbl ms (At exe endPc (R.callee kc lo' hi') F' nX) Q :=
  (seg_jabort2W (nC := ⟨nX.pc, ⟨k, []⟩, fun σ c => ∃ σx σC, nX.J σx c ∧ True ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩) hpc
    (fun σ c ⟨σx, _, hJ, _, hσ⟩ => by subst hσ; exact hX0 σx c hJ) hF hR hal hlo hkc h16 hK
    (fun m0 σC c0 ⟨σx, _, hJ, _⟩ => hstub m0 σC c0 ⟨σx, hJ⟩)).mono_pre
    fun _ _ h => at_leaveE (P := fun _ => True) hx hk (fun m hm =>
      let ⟨h1, m0, σC, o, h2, h3⟩ := hF' m hm
      ⟨h1, m0, σC, o, h2, h3, trivial⟩) h

end Spike.Lib.A64.Abort.Disp

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA stackOff_stable)
open Spike.Lib.A64.Rt (MainE mainE0 swFSL swF_stableL)
open Scc.Cert.Rt.A64 (Lays endOf)

/-! ## The abort tails -/

section Tails

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`print`'s abort's obligations** in `scc_rt_main`'s region `R` under
`F`, at the frames `fs`: the write abort path's below `-224` for every
caller's state with `x0 = 4`. -/
def MAbStub (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) : Prop :=
  ∀ m0 σC c0, σC.regs.X0 = 4 → Abort.Disp.StubWW (fun s c => W s c fs) K p lbl (ms fs) exe endPc
    (R.callee (-224) (-48) 0) (fun m => F m ∧ CKept R (-224) (-48) 0 m0 m ∧ Abs R ⟨-224, []⟩ m0 σC) c0

/-- **The heap abort's obligations** in `scc_rt_main`'s region `R` under
`F`, at the frame `fr`: the heap abort path's below `-288` (`wc_rodata`'s
node at `-208` left to `R`) for every source control of the node, `J0`
`wc_rodata`'s entry invariant per caller's state. -/
def HAbStub (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : TermRun.Frame) (J0 : AS → AS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (∃ σC' σx, (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (J0 σC') .abort).J σx c0) →
    Abort.Disp.StubHW (fun s c => W s c [fr]) K p lbl (ms [fr]) exe endPc (R.callee (-288) (-48) 0)
      (fun m => F m ∧ CKept R (-288) (-48) 0 m0 m ∧ Abs R ⟨-288, []⟩ m0 σC) c0

/-- **`print`'s abort does not return**: from `mAb` in `scc_rt_main`'s
region at the frames `fs`, into any fragment (`seg_jabort4W`). -/
theorem hello1_mAb_segWS {W : FragS isaLSE2} {K : State → State → Prop} {fs : List TermRun.Frame}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.A64.abi) (hstub : MAbStub W K p lbl ms exe endPc R F fs) (Q : FragS isaLSE2) :
    SegWS W K p lbl ms ((At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at fs) Q :=
  SegWS.liftS_noret fs (Abort.Disp.seg_jabort4W (Q := fun _ _ => False)
    (nC := mAb (_root_.Executable.labels exe).label) rfl
    (fun σ c h => by show σ.regs.X0.toNat = 4; rw [show σ.regs.X0 = 4 from h]; rfl) hF hR hal
    (by show R.lo ≤ -224 - 48; omega) (by show (-224 : Int) < R.hi; omega)
    (by show (-224 : Int) % 16 = 0; decide) hK fun m0 σC c0 h => hstub m0 σC c0 h) (fun _ _ h => h) Q

/-- **The heap abort does not return**: from `wc_rodata`'s `rX .abort` in
its region `mR R` (for some caller's state at its call) under `rodata`'s
frame `fr`, into any fragment (`seg_jabort2W_up` at `-80 - 208`). -/
theorem hello1_heapAb_segWS {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    {J0 : AS → AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hK : (ms [fr]).K = some Scc.Sem.A64.abi) (hstub : HAbStub W K p lbl ms exe endPc R F fr J0)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms (Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (J0 σC) .abort) s c) [fr]) Q :=
  SegWS.liftS_noret [fr] (SegW.exists_pre fun m0 => SegW.exists_pre fun σC =>
    Abort.Disp.seg_jabort2W_up (Q := fun _ _ => False) (kc := -80) (lo' := -208) (hi' := 0) (e := -208)
      (k := -288) rfl (by decide) rfl
      (fun σ c h => by obtain ⟨h2, -⟩ := h; show σ.regs.X0.toNat = 2; rw [h2]; rfl)
      (fun m hm => ⟨hm.1, m0, σC, _, hm.2.1, hm.2.2⟩) hF hR hal (by omega) (by omega) (by decide) hK
      (fun m0' σC' c0 ⟨σx, hJ⟩ => hstub m0' σC' c0 ⟨σC, σx, hJ⟩)) (fun _ _ h => h) Q

end Tails

/-! ## The levels with no exit -/

section Closed

open Spike.Lib.Hello1Src (hello1Src)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source, no exit**:
`hello1_setup_main_segWS` then `print`'s abort (`hello1_mAb_segWS`) or the
heap abort (`hello1_heapAb_segWS`), in a region of depth at least `336`
(`setupL`). -/
theorem hello1_setup_main_closedWS {W : FragS isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -setupL) (hhi : 0 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.A64.abi)
    {e : Expr} {env : TermRun.Env} (hK' : (ms [setupFrame e env]).K = some Scc.Sem.A64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hret : ∀ m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) .sp0).J σ c →
      Jp m0 σC σ c)
    (hPost : ∀ m0 σC, SetupPostP W K p lbl ms exe endPc R F (setupFrame e env) m0 σC (Jp m0 σC) (J1 m0 σC)
      (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) (Jr m0 σC) (Jw m0 σC))
    (hsW : MAbStub W K p lbl ms exe endPc R F [])
    (hsH : HAbStub W K p lbl ms exe endPc R F (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun _ _ _ => False) :=
  have hlo' : R.lo ≤ -336 := by simp only [setupL] at hlo; omega
  (hello1_setup_main_segWS hp hend hF hR hal (by omega) hhi hK hd hu hg hWe hPre hret hPost).seq
    ((hello1_mAb_segWS hF hR hal (by omega) hhi hK hsW _).or_pre
      (hello1_heapAb_segWS hF hR hal hlo' hhi hK' hsH _))

/-- **`hello1.w` from the start's entry at the setup block's source, no
exit**: the start's segment to `MainE` (`hD`), then for every value `v` of
the new stack's base `hello1_setup_main_closedWS` in its region of depth
`L ≥ setupL`; the abort paths' obligations per `v` (`hsW`, `hsH`). -/
theorem hello1_setup_closedWS {W : FragS isaLSE2} {K : State → State → Prop} {P0 : FragS isaLSE2}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hL : setupL ≤ L) (hK : (ms []).K = some Scc.Sem.A64.abi)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hK' : (ms [setupFrame e env]).K = some Scc.Sem.A64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, SetupPreP W K lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      [setupFrame e env] (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) .sp0).J
        σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W K p lbl ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env) m0 σC (Jp v m0 σC) (J1 v m0 σC)
      (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC))
    (hsW : ∀ v, MAbStub W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) [])
    (hsH : ∀ v, HAbStub W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J)) :
    SegWS W K p lbl ms P0 (fun _ _ _ => False) := by
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR v.1 (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v.1)
        (mainE0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩)).at [])
    fun v => hello1_setup_main_closedWS hp hend (fun m m' h hd' =>
        ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩) v.2.2 v.2.1
      (show -L ≤ -setupL by simp only [setupL] at hL ⊢; omega) (Int.le_refl _) hK hK' hd hu
      (g := ⟨top, UInt64.ofBitVec tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2.1, v.2.2, h⟩) (hPre v.1) (hret v.1) (hPost v.1) (hsW v.1)
      (hsH v.1)).mono_pre ?_)
  rintro s c fs ⟨⟨v, h16, hok, h⟩, rfl⟩
  exact ⟨⟨v, h16, hok⟩, h, rfl⟩

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` under `rodata`'s frame, no
exit**: `hello1_main_post_segWS` (cut B's premises `hPost`) then `print`'s
abort (`hello1_mAb_segWS`). -/
theorem hello1_main_post_closedWS {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hfr : fr.σs = [])
    {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hPost : SetupPostP W K p lbl ms exe endPc R F fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hsW : MAbStub W K p lbl ms exe endPc R F []) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp J1 J2 J3 J4 .s0)).at [fr])
      (fun _ _ _ => False) :=
  (hello1_main_post_segWS hp hend hF hR hal hlo hhi hK hfr hPost.hW hPost.hra hPost.hmem hPost.h1 hPost.h2
    hPost.h3 hPost.h4 hPost.hedge hPost.hlimW hPost.hsvc hPost.hedgeW hPost.hok).seq
    (hello1_mAb_segWS hF hR hal (by omega) hhi hK hsW _)

end Closed

end Spike.Lib.A64.Flow.Hello1
