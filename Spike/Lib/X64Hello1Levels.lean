/-
**`hello1.w`'s `scc_rt_main` at the setup block's source in two levels**
(x86-64): the allocation-capable consumer's fragment of one allocation is a
level before the allocation at the static placement and, per fresh label
`l` at base `b` of `w` words, a level after it at the placement with `l`
placed. Here `hello1_setup_closedWS` and `hello1_main_post_closedWS`
(`Spike/Lib/X64Hello1SetupTail.lean`), which share one placement, are cut
at the allocation: the level before ends in the allocator's continuation
(`MemSide.xa`) and the heap abort; the level after starts at `wc_rodata`'s
`.x13`. The x86-64 twin of `Spike/Lib/A64Hello1Levels.lean`.

At a placement with no label (the static link's), `wc_rodata`'s return
exit `.x13` (`Alloc.E .ret`, the source's buffer a placed label's) has no
state, so the level before has no exit but the heap abort's tail.

- `rX_x13_none`: `wc_rodata`'s `.x13` has no state at a placement with no
  label.
- `hello1_setup_pre_main_closedWS`, `hello1_setup_pre_closedWS`: from
  `scc_rt_main`'s entry (the start's entry) at the setup block's source, no
  exit, cut A and the heap abort (the level before the allocation).
- `hello1_post_closedWS`: from `wc_rodata`'s `.x13` under `rodata`'s frame,
  for every value of the new stack's base and caller's state at the call,
  no exit (the level after the allocation).
- `landJ`: the allocator's landing left to `wc_rodata`'s region, the
  invariant at `.x13` the level after starts from.
- `rd_land`: at `rodata`'s allocation the landing's base is the arena's
  object of two words of `τ8` and its words are two.
- `land_post`: a landing state is at `.x13` of `landJ`
  (`hello1_main_xa_post`).

Where x86-64 differs from AArch64: the allocator's return is `.x13`
(`rdX13`, `rX .x13`; hence `rX_x13_none` for `rX_sp0_none`); the nodes
`rX`, `rN` and `mNC` name the region; after the start `scc_rt_main`'s
region is `mainR v L` (`mainE_ok`: `setupL + 8 ≤ L` before the allocation,
`296 ≤ L` after it, `8 ∣ L`), with no alignment premise.
-/
import Spike.Lib.X64Hello1SetupTail
import Spike.Lib.X64Hello1RodataSetup

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA tpOf)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.Rt (MainE mainE0 swFSL mainE_ok)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Hello1RodataSrc (rdCN τ8)
open Spike.Lib.Hello1Src (hello1Src)

/-! ## The return exit at a placement with no label -/

/-- **`wc_rodata`'s `.x13` has no state at a placement with no label**: its
invariant (`Alloc.E .ret`) represents the source's buffer by a placed
label. -/
theorem rX_x13_none {ms : MemSide isa} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    (hnone : ∀ l, lbl l = none) {R : Region} {J0 : AS → Ctl → Prop} {σ : AS} {c : Ctl} :
    ¬ (rX ms lab lbl R J0 .x13).J σ c := by
  rintro ⟨q, -, -, l, ini, old, hv, -⟩
  obtain ⟨-, x, hx, -⟩ := hv
  simp [Scc.Sem.wordAddr, hnone] at hx

/-! ## The level before the allocation -/

section Pre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source up to the
allocation, no exit**: the call of `rodata` and its first steps
(`setupCall_run`), cut A at the frame `setupFrame e env`
(`hello1_main_pre_segWS`), its return exit empty at a placement with no
label (`rX_x13_none`), its heap abort exit run on into the abort path
(`hello1_heapAb_segWS`), in a region of depth at least `setupL`. -/
theorem hello1_setup_pre_main_closedWS {W : FragS isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -setupL) (hhi : 8 ≤ R.hi)
    (hnone : ∀ l, lbl l = none)
    {e : Expr} {env : TermRun.Env} (hK' : (ms [setupFrame e env]).K = some Scc.Sem.X64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hsH : HAbStub W K p lbl ms exe endPc R F (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label R (rdJ' g)).J)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun _ _ _ => False) := by
  let lab := (_root_.Executable.labels exe).label
  have hlo' : R.lo ≤ -320 := by simp only [setupL] at hlo; omega
  have hA := hello1_main_pre_segWS (fs1 := [setupFrame e env]) hp hend hF hR (by omega) hhi
    (J := (mainE0 lab g).J) (J' := rdJ' g)
    (fun σ c ⟨⟨hc, hsp, htp⟩, hx⟩ => ⟨rdCN, hc ▸ hg ▸ setupCall_run hd hu, rfl, hsp, htp, hx⟩) hWe hPre.hW hPre.hlimM
    hPre.hlimR hPre.hq hPre.hmem hPre.hxa
  refine hA.seq ((hello1_heapAb_segWS hF hR hlo' hhi hK' hsH _).mono_pre ?_)
  rintro s c fs ⟨⟨m0, σC, y, h⟩, rfl⟩
  cases y
  · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := h
    exact (rX_x13_none hnone hJ).elim
  · exact ⟨⟨m0, σC, h⟩, rfl⟩

/-- **`hello1.w` from the start's entry at the setup block's source up to
the allocation, no exit**: the start's segment to `MainE` (`hD`), then for
every value `v` of the new stack's base `hello1_setup_pre_main_closedWS` in
`scc_rt_main`'s region `mainR v L` (`mainE_ok`: the new region of depth
`L ≥ setupL + 8`, `8 ∣ L`); cut A's premises and the heap abort's
obligations per `v` of a well-formed region (`hPre`, `hsH`). -/
theorem hello1_setup_pre_closedWS {W : FragS isa} {K : State → State → Prop} {P0 : FragS isa}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hL : setupL + 8 ≤ L) (hL8 : L % 8 = 0) (hnone : ∀ l, lbl l = none)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hK' : (ms [setupFrame e env]).K = some Scc.Sem.X64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, (swR v (-L) 0).OK → SetupPreP W K lbl ms exe endPc (mainR v L) (mainF rS tcb top v L)
      [setupFrame e env] (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩))
    (hsH : ∀ v, (swR v (-L) 0).OK →
      HAbStub W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J)) :
    SegWS W K p lbl ms P0 (fun _ _ _ => False) := by
  have hL' : 328 ≤ L := by simp only [setupL] at hL; omega
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc (mainR v.1 L) (mainF rS tcb top v.1 L)
        (mainE0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩)).at [])
    fun v => hello1_setup_pre_main_closedWS hp hend (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).2
      (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).1
      (show 8 - L ≤ -setupL by simp only [setupL]; omega) (show (8 : Int) ≤ 8 by decide) hnone hK' hd hu
      (g := ⟨top - 8#64, tpOf tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2, h⟩) (hPre v.1 v.2) (hsH v.1 v.2)).mono_pre ?_)
  rintro s c fs ⟨⟨v, hok, h⟩, rfl⟩
  exact ⟨⟨v, hok⟩, h, rfl⟩

end Pre

/-! ## The level after the allocation -/

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}

/-- **`scc_rt_main` from `wc_rodata`'s `.x13` under `rodata`'s frame, no
exit**, for every value `v` of the new stack's base (`scc_rt_main`'s region
`mainR v L` under `mainF`, the new region of depth `L ≥ 296`, as
`hello1_setup_pre_closedWS`'s) and caller's state `m0`, `σC` at
`wc_rodata`'s call: `hello1_main_post_closedWS` per `v`, `m0`, `σC` (cut
B's premises `hPost`, `print`'s abort's obligations `hsW`, per `v` of a
well-formed region). -/
theorem hello1_post_closedWS {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {L : Int}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hL : 296 ≤ L) (hL8 : L % 8 = 0) (hK : (ms []).K = some Scc.Sem.X64.abi) (hfr : fr.σs = [])
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hPost : ∀ v, (swR v (-L) 0).OK → ∀ m0 σC,
      SetupPostP W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) fr m0 σC
      (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC))
    (hsW : ∀ v, (swR v (-L) 0).OK → MAbStub W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) []) :
    SegWS W K p lbl ms (fun s c fs => ∃ v : BitVec 64, (swR v (-L) 0).OK ∧ ∃ m0 σC,
      (At exe endPc (mR (mainR v L)) (mF (mainR v L) (mainF rS tcb top v L) m0 σC)
        (rdX13 (_root_.Executable.labels exe).label (Jp v m0 σC))).at [fr] s c fs)
      (fun _ _ _ => False) := by
  refine (SegWS.exists_pre (P := fun v : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      fun s c fs => ∃ m0 σC, (At exe endPc (mR (mainR v.1 L)) (mF (mainR v.1 L) (mainF rS tcb top v.1 L) m0 σC)
        (rdX13 (_root_.Executable.labels exe).label (Jp v.1 m0 σC))).at [fr] s c fs)
    fun v => SegWS.exists_pre fun m0 => SegWS.exists_pre fun σC =>
      hello1_main_post_closedWS hp hend (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).2
        (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).1 (show 8 - L ≤ -288 by omega)
        (show (8 : Int) ≤ 8 by decide) hK hfr (hPost v.1 v.2 m0 σC)
        (hsW v.1 v.2)).mono_pre ?_
  rintro s c fs ⟨v, hok, m0, σC, h⟩
  exact ⟨⟨v, hok⟩, m0, σC, h⟩

end Post

/-! ## The landing -/

section Land

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The allocator's landing left to `wc_rodata`'s region** (`R` the
caller's): for a call `q` of the allocator from `wc_rodata`'s call node of
the caller's state `σC` at its call (of invariant `J`), the state left from
the allocator's continuation `Ea` of label `l`, base `b`, `w` words, and
the control there. -/
def landJ (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J : AS → Ctl → Prop)
    (l : WeakMem.AllocLabel) (b w : Nat) (σC : AS) (σ : AS) (c : Ctl) : Prop :=
  ∃ (q : AG ms lab) (σx σ' : AS) (c0 : Ctl), (Ea ms q.1 l b w).J σx c ∧
    (rN lab (mR R) (mRdJ0 (mNC lab R J).J σC) .call).J σ' c0 ∧ (Alloc.N lab ms q.1 .e).J (enter (-48) σ') c0 ∧
    σ = leave (aR (mR R)) (-48) σ' σx

/-- **The landing at `rodata`'s allocation**: from `wc_rodata`'s call node
at the source of `rodata`'s allocation (`rdJ' g`) and the allocator's entry
of the call `q`, the continuation's base is the object at some old count of
two words of `τ8` within the cells, and its words are two. -/
theorem rd_land {ms : MemSide isa} {lab : Label → Int64} {R : Region} {g : MainG} {σC σ' σx : AS} {c0 c : Ctl}
    {q : AG ms lab} {l : WeakMem.AllocLabel} {b w : Nat}
    (h1 : (rN lab (mR R) (mRdJ0 (mNC lab R (rdJ' g)).J σC) .call).J σ' c0)
    (h2 : (Alloc.N lab ms q.1 .e).J (enter (-48) σ') c0) (hJ : (Ea ms q.1 l b w).J σx c) :
    ∃ old, b = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells ∧ w = 2 := by
  obtain ⟨⟨σe, ⟨-, ⟨σm, ⟨hc, -⟩, -⟩⟩, -⟩, -⟩ := h1
  have hq : q.1.c0 = rdCN := h2.1 ▸ hc
  obtain ⟨-, hτ, -, hn⟩ := rdQ_facts q.2 hq
  obtain ⟨-, old, -, -, hb, hold, -, -, us, hus, hw⟩ := hJ
  rw [hτ] at hus
  have h8 : TermRun.accs (TermRun.close [] τ8) = some [.one] := by rfl
  have hus' : us = [.one] := Option.some.inj (hus.symm.trans h8)
  subst hus'
  rw [hn, hτ] at hb hold
  exact ⟨old, hb, hold, by rw [hw, hn]; rfl⟩

/-- **A landing state is at `wc_rodata`'s `.x13` of `landJ`**
(`hello1_main_xa_post`). -/
theorem land_post {ms : MemSide isa} {J : AS → Ctl → Prop} {m0 : MachineData}
    {σC : AS} {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J).J σC) .call).J σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 8 mC m)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC)
      (rdX13 (_root_.Executable.labels exe).label (landJ ms (_root_.Executable.labels exe).label R J l b w σC))
      s c :=
  hello1_main_xa_post hFF hkeep (fun σx σ c0 _ hJx h1 h2 => ⟨q, σx, σ, c0, hJx, h1, h2, rfl⟩) h

end Land

end Spike.Lib.X64.Flow.Hello1
