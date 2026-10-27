/-
**`hello1.w`'s `scc_rt_main` at the setup block's source with its abort
tails** (x86-64): the exits of `hello1_setup_main_segWS`,
`hello1_setup_segWS` and `hello1_main_post_segWS`
(`Spike/Lib/X64Hello1SetupGlue.lean`, `Spike/Lib/X64Hello1SetupPost.lean`)
run on into the abort paths, which do not return, so each segment has no
exit. The abort paths' obligations stay premises (`StubWW`, `StubHW`, e.g.
`stubWW_of_code`, `stubHW_of_code`). The x86-64 twin of
`Spike/Lib/A64Hello1SetupTail.lean`.

`print`'s abort (`mAb`, `%rdi = 4`, at `-224` in `scc_rt_main`'s region) is
`Abort.Disp.seg_jabort4W` there. The heap abort (`rX .abort`, `%rdi = 2`)
is at `-208` in `wc_rodata`'s region `mR R`, whose `-208` floor leaves the
dispatcher no room; the node is first left to `scc_rt_main`'s region
(`at_leave`, at `-80 - 208 = -288`), where the dispatcher runs below it
down to `-320` (`setupL`).

- `Abort.Disp.seg_jabort2W_up`: `seg_jabort2W` from a node of a callee's
  region, the dispatcher in the caller's region below the node.
- `MAbStub`, `HAbStub`: the two abort paths' obligations.
- `hello1_mAb_segWS`: `print`'s abort at any frames, into any fragment.
- `hello1_heapAb_segWS`: the heap abort under `rodata`'s frame, into any
  fragment.
- `hello1_setup_main_closedWS`, `hello1_setup_closedWS`: from
  `scc_rt_main`'s entry (the start's entry) at the setup block's source, no
  exit (the allocation's level before it).
- `hello1_main_post_closedWS`: from `wc_rodata`'s `.x13` under `rodata`'s
  frame, no exit (the level after the allocation).

Where x86-64 differs from AArch64: x86-64's `at_leave` already takes a node
at any `%rsp` offset, so there is no `at_leaveE`; the dispatcher's region is
`[-24, 16)` below the pushed return address (`32` below the node, so
`setupL` is `80 + 208 + 32`, and `print`'s abort needs `-256`); there is no
`SegWS.liftS_noret` on this side (it lives with the AArch64 abort files), so
the no-return segments are `SegWS.liftS` with the empty exit dropped, as in
`Spike/Lib/X64AbortHeapS.lean`; after the start, `scc_rt_main`'s region is
`mainR v L`, so the start's depth is `setupL + 8 ≤ L`.
-/
import Spike.Lib.X64Hello1SetupGlue
import Spike.Lib.X64AbortHeapS
import Spike.Lib.X64AbortWriteW

namespace Spike.Lib.X64.Abort.Disp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A jump to `scc_rt_abort` with `%rdi = 2` from a callee's region does
not return**: from a node `nX` of the callee's region (at `kc`, `%rsp` at
`e`, `F'` giving the caller's `F` and its cells outside as in a caller's
state) the node left to the caller's region at `k = kc + e` (`at_leave`),
then `seg_jabort2W` there, the dispatcher below `k`. -/
theorem seg_jabort2W_up {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    {kc lo' hi' e k : Int} {F' : MachineData → Prop} {nX : ND} (hx : nX.o = ⟨e, []⟩) (hk : kc + e = k)
    (hpc : nX.pc = (_root_.Executable.labels exe).label "scc_rt_abort")
    (hrdi : ∀ σ c, nX.J σ c → σ.regs.get64 .rdi = 2#64)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ k - 32) (hhi : k + 8 ≤ R.hi) (h8 : k % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, (∃ σx, nX.J σx c0) → StubHW W K p lbl ms exe endPc (R.callee (k - 8) (-24) 16)
      (fun m => F m ∧ CKept R (k - 8) (-24) 16 m0 m ∧ Abs R ⟨k, []⟩ m0 σC) c0) :
    SegW W K p lbl ms (At exe endPc (R.callee kc lo' hi') F' nX) Q := by
  subst hk
  exact (seg_jabort2W (nC := ⟨nX.pc, ⟨kc + e, []⟩, fun σ c => ∃ σx σC, nX.J σx c ∧ True ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩) hpc
    (fun σ c ⟨σx, _, hJ, _, hσ⟩ => by subst hσ; exact hrdi σx c hJ) hF hR hlo hhi h8 hK
    (fun m0 σC c0 ⟨σx, _, hJ, _⟩ => hstub m0 σC c0 ⟨σx, hJ⟩)).mono_pre
    fun _ _ h => at_leave (P := fun _ => True) hx (fun m hm =>
      let ⟨h1, m0, σC, o, h2, h3⟩ := hF' m hm
      ⟨h1, m0, σC, o, h2, h3, trivial⟩) h

end Spike.Lib.X64.Abort.Disp

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA tpOf)
open Spike.Lib.X64.Rt (MainE mainE0 swFSL mainE_ok)
open Scc.Cert.Rt.X64 (Lays endOf)

/-! ## The abort tails -/

section Tails

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`print`'s abort's obligations** in `scc_rt_main`'s region `R` under
`F`, at the frames `fs`: the write abort path's below `-224` (the
dispatcher's region at `-232`) for every caller's state with `%rdi = 4`. -/
def MAbStub (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) : Prop :=
  ∀ m0 σC c0, σC.regs.get64 .rdi = 4 → Abort.Disp.StubWW (fun s c => W s c fs) K p lbl (ms fs) exe endPc
    (R.callee (-232) (-24) 16) (fun m => F m ∧ CKept R (-232) (-24) 16 m0 m ∧ Abs R ⟨-224, []⟩ m0 σC) c0

/-- **The heap abort's obligations** in `scc_rt_main`'s region `R` under
`F`, at the frame `fr`: the heap abort path's below `-288` (`wc_rodata`'s
node at `-208` left to `R`; the dispatcher's region at `-296`) for every
source control of the node, `J0` `wc_rodata`'s entry invariant per caller's
state. -/
def HAbStub (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fr : TermRun.Frame) (J0 : AS → AS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (∃ σC' σx, (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (mR R) (J0 σC') .abort).J σx c0) →
    Abort.Disp.StubHW (fun s c => W s c [fr]) K p lbl (ms [fr]) exe endPc (R.callee (-296) (-24) 16)
      (fun m => F m ∧ CKept R (-296) (-24) 16 m0 m ∧ Abs R ⟨-288, []⟩ m0 σC) c0

/-- **`print`'s abort does not return**: from `mAb` in `scc_rt_main`'s
region at the frames `fs`, into any fragment (`seg_jabort4W`). -/
theorem hello1_mAb_segWS {W : FragS isa} {K : State → State → Prop} {fs : List TermRun.Frame}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -256) (hhi : 8 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.X64.abi) (hstub : MAbStub W K p lbl ms exe endPc R F fs) (Q : FragS isa) :
    SegWS W K p lbl ms ((At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at fs) Q :=
  (SegWS.liftS fs (Abort.Disp.seg_jabort4W (Q := fun _ _ => False)
    (nC := mAb (_root_.Executable.labels exe).label) rfl (fun σ c h => h) hF hR
    (by show R.lo ≤ -224 - 32; omega) (by show (-224 : Int) + 8 ≤ R.hi; omega)
    (by show (-224 : Int) % 8 = 0; decide) hK fun m0 σC c0 h => hstub m0 σC c0 h) (fun _ _ h => h)).mono_post
    fun _ _ _ h => h.1.elim

/-- **The heap abort does not return**: from `wc_rodata`'s `rX .abort` in
its region `mR R` (for some caller's state at its call) under `rodata`'s
frame `fr`, into any fragment (`seg_jabort2W_up` at `-80 - 208`). -/
theorem hello1_heapAb_segWS {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}
    {J0 : AS → AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 8 ≤ R.hi)
    (hK : (ms [fr]).K = some Scc.Sem.X64.abi) (hstub : HAbStub W K p lbl ms exe endPc R F fr J0)
    (Q : FragS isa) :
    SegWS W K p lbl ms (Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
      (rX (ms [fr]) (_root_.Executable.labels exe).label lbl (mR R) (J0 σC) .abort) s c) [fr]) Q := by
  refine (SegWS.liftS (Q₀ := fun _ _ => False) [fr]
    (SegW.exists_pre fun m0 => SegW.exists_pre fun σC => ?_) (fun _ _ h => h)).mono_post fun _ _ _ h => h.1.elim
  refine Abort.Disp.seg_jabort2W_up (Q := fun _ _ => False) (kc := -80) (lo' := -208) (hi' := 8) (e := -208)
    (k := -288) rfl (by decide) rfl ?_ ?_ hF hR (by show R.lo ≤ -288 - 32; omega)
    (by show (-288 : Int) + 8 ≤ R.hi; omega) (by decide) hK ?_
  · intro σ c h
    exact h.1
  · intro m hm
    exact ⟨hm.1, m0, σC, _, hm.2.1, hm.2.2⟩
  · rintro m0' σC' c0 ⟨σx, hJ⟩
    exact hstub m0' σC' c0 ⟨σC, σx, hJ⟩

end Tails

/-! ## The levels with no exit -/

section Closed

open Spike.Lib.Hello1Src (hello1Src)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source, no exit**:
`hello1_setup_main_segWS` then `print`'s abort (`hello1_mAb_segWS`) or the
heap abort (`hello1_heapAb_segWS`), in a region of depth at least `320`
(`setupL`). -/
theorem hello1_setup_main_closedWS {W : FragS isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -setupL) (hhi : 8 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.X64.abi)
    {e : Expr} {env : TermRun.Env} (hK' : (ms [setupFrame e env]).K = some Scc.Sem.X64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hret : ∀ m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R (rdJ' g)).J σC) .x13).J σ c →
      Jp m0 σC σ c)
    (hPost : ∀ m0 σC, SetupPostP W K p lbl ms exe endPc R F (setupFrame e env) m0 σC (Jp m0 σC) (J1 m0 σC)
      (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) (Jr m0 σC) (Jw m0 σC))
    (hsW : MAbStub W K p lbl ms exe endPc R F [])
    (hsH : HAbStub W K p lbl ms exe endPc R F (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label R (rdJ' g)).J)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun _ _ _ => False) :=
  have hlo' : R.lo ≤ -320 := by simp only [setupL] at hlo; omega
  (hello1_setup_main_segWS hp hend hF hR (by omega) hhi hK hd hu hg hWe hPre hret hPost).seq
    ((hello1_mAb_segWS hF hR (by omega) hhi hK hsW _).or_pre
      (hello1_heapAb_segWS hF hR hlo' hhi hK' hsH _))

/-- **`hello1.w` from the start's entry at the setup block's source, no
exit**: the start's segment to `MainE` (`hD`), then for every value `v` of
the new stack's base `hello1_setup_main_closedWS` in `scc_rt_main`'s region
`mainR v L` (`mainE_ok`: the new region of depth `L ≥ setupL + 8`, `8 ∣ L`);
the abort paths' obligations per `v` (`hsW`, `hsH`). -/
theorem hello1_setup_closedWS {W : FragS isa} {K : State → State → Prop} {P0 : FragS isa}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hL : setupL + 8 ≤ L) (hL8 : L % 8 = 0) (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hK' : (ms [setupFrame e env]).K = some Scc.Sem.X64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, SetupPreP W K lbl ms exe endPc (mainR v L) (mainF rS tcb top v L)
      [setupFrame e env] (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR (mainR v L))
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC)
        .x13).J σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) (setupFrame e env)
      m0 σC (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC))
    (hsW : ∀ v, MAbStub W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) [])
    (hsH : ∀ v, HAbStub W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J)) :
    SegWS W K p lbl ms P0 (fun _ _ _ => False) := by
  have hL' : 328 ≤ L := by simp only [setupL] at hL; omega
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc (mainR v.1 L) (mainF rS tcb top v.1 L)
        (mainE0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩)).at [])
    fun v => hello1_setup_main_closedWS hp hend (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).2
      (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).1
      (show 8 - L ≤ -setupL by simp only [setupL]; omega) (show (8 : Int) ≤ 8 by decide) hK hK' hd hu
      (g := ⟨top - 8#64, tpOf tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2, h⟩) (hPre v.1) (hret v.1) (hPost v.1) (hsW v.1) (hsH v.1)).mono_pre ?_)
  rintro s c fs ⟨⟨v, hok, h⟩, rfl⟩
  exact ⟨⟨v, hok⟩, h, rfl⟩

/-- **`scc_rt_main` from `wc_rodata`'s `.x13` under `rodata`'s frame, no
exit**: `hello1_main_post_segWS` (cut B's premises `hPost`) then `print`'s
abort (`hello1_mAb_segWS`). -/
theorem hello1_main_post_closedWS {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hfr : fr.σs = [])
    {m0 : MachineData} {σC : AS} {Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop}
    (hPost : SetupPostP W K p lbl ms exe endPc R F fr m0 σC Jp J1 J2 J3 J4 Jr Jw)
    (hsW : MAbStub W K p lbl ms exe endPc R F []) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC) (rdX13 (_root_.Executable.labels exe).label Jp)).at [fr])
      (fun _ _ _ => False) :=
  (hello1_main_post_segWS hp hend hF hR hlo hhi hK hfr hPost.hW hPost.hbp hPost.hra hPost.hmem hPost.h1 hPost.h2
    hPost.h3 hPost.h4 hPost.hedge hPost.hbpr hPost.hlimW hPost.hsvc hPost.hedgeW hPost.hbpw hPost.hok).seq
    (hello1_mAb_segWS hF hR (by omega) hhi hK hsW _)

end Closed

end Spike.Lib.X64.Flow.Hello1
