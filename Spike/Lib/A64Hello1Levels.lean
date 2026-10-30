/-
**`hello1.w`'s `scc_rt_main` at the setup block's source in two levels**
(AArch64): the allocation-capable consumer's fragment of one allocation
(`I2`, `Spike/Lib/A64SegInstA.lean`) is a level before the allocation at
the static placement and, per fresh label `l` at base `b` of `w` words, a
level after it at the placement with `l` placed. Here
`hello1_setup_closedWS` and `hello1_main_post_closedWS`
(`Spike/Lib/A64Hello1SetupTail.lean`), which share one placement, are cut
at the allocation: the level before ends in the allocator's continuation
(`MemSide.xa`) and the heap abort; the level after starts at `wc_rodata`'s
`.sp0`.

At a placement with no label (the static link's), `wc_rodata`'s return
exit `.sp0` (`Alloc.E .ret`, the source's buffer a placed label's) has no
state, so the level before has no exit but the heap abort's tail.

- `rX_sp0_none`: `wc_rodata`'s `.sp0` has no state at a placement with no
  label.
- `hello1_setup_pre_main_closedWS`, `hello1_setup_pre_closedWS`: from
  `scc_rt_main`'s entry (the start's entry) at the setup block's source, no
  exit, cut A and the heap abort (the level before the allocation).
- `hello1_post_closedWS`: from `wc_rodata`'s `.sp0` under `rodata`'s frame,
  for every value of the new stack's base and caller's state at the call,
  no exit (the level after the allocation).
- `landJ`: the allocator's landing left to `wc_rodata`'s region, the
  invariant at `.sp0` the level after starts from.
- `rd_land`: at `rodata`'s allocation the landing's base is the arena's
  object of two words of `τ8` and its words are two.
- `land_post`: a landing state is at `.sp0` of `landJ`
  (`hello1_main_xa_post`).
-/
import Spike.Lib.A64Hello1SetupTail
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA stackOff_stable)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Rt (MainE mainE0 swFSL swF_stableL)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Hello1RodataSrc (rdCN τ8)
open Spike.Lib.Hello1Src (hello1Src)

/-! ## The return exit at a placement with no label -/

/-- **`wc_rodata`'s `.sp0` has no state at a placement with no label**: its
invariant (`Alloc.E .ret`) represents the source's buffer by a placed
label. -/
theorem rX_sp0_none {ms : MemSide isaLSE2} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    (hnone : ∀ l, lbl l = none) {J0 : AS → Ctl → Prop} {σ : AS} {c : Ctl} :
    ¬ (rX ms lab lbl J0 .sp0).J σ c := by
  rintro ⟨q, -, l, ini, old, hv, -⟩
  obtain ⟨-, x, hx, -⟩ := hv
  simp [Scc.Sem.wordAddr, hnone] at hx

/-! ## The level before the allocation -/

section Pre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source up to the
allocation, no exit**: the call of `rodata` and its first steps
(`setupCall_run`), cut A at the frame `setupFrame e env`
(`hello1_main_pre_segWS`), its return exit empty at a placement with no
label (`rX_sp0_none`), its heap abort exit run on into the abort path
(`hello1_heapAb_segWS`), in a region of depth at least `setupL`. -/
theorem hello1_setup_pre_main_closedWS {W : FragS isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -setupL) (hhi : 0 ≤ R.hi)
    (hnone : ∀ l, lbl l = none)
    {e : Expr} {env : TermRun.Env} (hK' : (ms [setupFrame e env]).K = some Scc.Sem.A64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hsH : HAbStub W K p lbl ms exe endPc R F (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun _ _ _ => False) := by
  let lab := (_root_.Executable.labels exe).label
  have hlo' : R.lo ≤ -336 := by simp only [setupL] at hlo; omega
  have hA := hello1_main_pre_segWS (fs1 := [setupFrame e env]) hp hend hF hR hal (by omega) hhi
    (J := (mainE0 lab g).J) (J' := rdJ' g)
    (fun σ c ⟨⟨hc, hsp, htp⟩, hx⟩ => ⟨rdCN, hc ▸ hg ▸ setupCall_run hd hu, rfl, hsp, htp, hx⟩) hWe hPre.hW hPre.hlimM
    hPre.hlimR hPre.hq hPre.hmem hPre.hxa
  refine hA.seq ((hello1_heapAb_segWS hF hR hal hlo' hhi hK' hsH _).mono_pre ?_)
  rintro s c fs ⟨⟨m0, σC, y, h⟩, rfl⟩
  cases y
  · obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := h
    exact (rX_sp0_none hnone hJ).elim
  · exact ⟨⟨m0, σC, h⟩, rfl⟩

/-- **`hello1.w` from the start's entry at the setup block's source up to
the allocation, no exit**: the start's segment to `MainE` (`hD`), then for
every value `v` of the new stack's base `hello1_setup_pre_main_closedWS` in
its region of depth `L ≥ setupL`; cut A's premises and the heap abort's
obligations per aligned `v` of a well-formed region (`hPre`, `hsH`). -/
theorem hello1_setup_pre_closedWS {W : FragS isaLSE2} {K : State → State → Prop} {P0 : FragS isaLSE2}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hL : setupL ≤ L) (hnone : ∀ l, lbl l = none)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hK' : (ms [setupFrame e env]).K = some Scc.Sem.A64.abi)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      SetupPreP W K lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      [setupFrame e env] (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hsH : ∀ v, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      HAbStub W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      (setupFrame e env)
      (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J)) :
    SegWS W K p lbl ms P0 (fun _ _ _ => False) := by
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR v.1 (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v.1)
        (mainE0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩)).at [])
    fun v => hello1_setup_pre_main_closedWS hp hend (fun m m' h hd' =>
        ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩) v.2.2 v.2.1
      (show -L ≤ -setupL by simp only [setupL] at hL ⊢; omega) (Int.le_refl _) hnone hK' hd hu
      (g := ⟨top, UInt64.ofBitVec tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2.1, v.2.2, h⟩) (hPre v.1 v.2.1 v.2.2) (hsH v.1 v.2.1 v.2.2)).mono_pre ?_)
  rintro s c fs ⟨⟨v, h16, hok, h⟩, rfl⟩
  exact ⟨⟨v, h16, hok⟩, h, rfl⟩

end Pre

/-! ## The level after the allocation -/

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}

/-- **`scc_rt_main` from `wc_rodata`'s `.sp0` under `rodata`'s frame, no
exit**, for every value `v` of the new stack's base (the region of depth
`L ≥ 288` under `swFSL`, as `hello1_setup_pre_closedWS`'s) and caller's
state `m0`, `σC` at `wc_rodata`'s call: `hello1_main_post_closedWS` per
`v`, `m0`, `σC` (cut B's premises `hPost`, `print`'s abort's obligations
`hsW`, per aligned `v` of a well-formed region). -/
theorem hello1_post_closedWS {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {L : Int}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hL : 288 ≤ L) (hK : (ms []).K = some Scc.Sem.A64.abi) (hfr : fr.σs = [])
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hPost : ∀ v, v.toNat % 16 = 0 → (swR v (-L) 0).OK → ∀ m0 σC,
      SetupPostP W K p lbl ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) fr m0 σC (Jp v m0 σC) (J1 v m0 σC)
      (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC))
    (hsW : ∀ v, v.toNat % 16 = 0 → (swR v (-L) 0).OK →
      MAbStub W K p lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) []) :
    SegWS W K p lbl ms (fun s c fs => ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK ∧ ∃ m0 σC,
      (At exe endPc (mR (swR v (-L) 0)) (mF (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) m0 σC)
        (pN (_root_.Executable.labels exe).label (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC)
          .s0)).at [fr] s c fs)
      (fun _ _ _ => False) := by
  refine (SegWS.exists_pre (P := fun v : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      fun s c fs => ∃ m0 σC, (At exe endPc (mR (swR v.1 (-L) 0))
        (mF (swR v.1 (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v.1) m0 σC)
        (pN (_root_.Executable.labels exe).label (Jp v.1 m0 σC) (J1 v.1 m0 σC) (J2 v.1 m0 σC) (J3 v.1 m0 σC)
          (J4 v.1 m0 σC) .s0)).at [fr] s c fs)
    fun v => SegWS.exists_pre fun m0 => SegWS.exists_pre fun σC =>
      hello1_main_post_closedWS hp hend (fun m m' h hd' =>
          ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩) v.2.2 v.2.1
        (show -L ≤ -288 by omega) (Int.le_refl _) hK hfr (hPost v.1 v.2.1 v.2.2 m0 σC)
        (hsW v.1 v.2.1 v.2.2)).mono_pre ?_
  rintro s c fs ⟨v, h16, hok, m0, σC, h⟩
  exact ⟨⟨v, h16, hok⟩, m0, σC, h⟩

end Post

/-! ## The landing -/

section Land

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The allocator's landing left to `wc_rodata`'s region** (`R` the
caller's): for a call `q` of the allocator from `wc_rodata`'s call node of
the caller's state `σC` at its call (of invariant `J`), the state left from
the allocator's continuation `Ea` of label `l`, base `b`, `w` words, and
the control there. -/
def landJ (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (J : AS → Ctl → Prop)
    (l : WeakMem.AllocLabel) (b w : Nat) (σC : AS) (σ : AS) (c : Ctl) : Prop :=
  ∃ (q : AG ms lab) (σx σ' : AS) (c0 : Ctl), (Ea ms q.1 l b w).J σx c ∧
    (rN lab (mRdJ0 (mNC lab J).J σC) .call).J σ' c0 ∧ (Alloc.N lab ms q.1 .e).J (enter (-48) σ') c0 ∧
    σ = leave (aR (mR R)) (-48) σ' σx

/-- **The landing at `rodata`'s allocation**: from `wc_rodata`'s call node
at the source of `rodata`'s allocation (`rdJ' g`) and the allocator's entry
of the call `q`, the continuation's base is the object at some old count of
two words of `τ8` within the cells, and its words are two. -/
theorem rd_land {ms : MemSide isaLSE2} {lab : Label → Int64} {g : MainG} {σC σ' σx : AS} {c0 c : Ctl}
    {q : AG ms lab} {l : WeakMem.AllocLabel} {b w : Nat}
    (h1 : (rN lab (mRdJ0 (mNC lab (rdJ' g)).J σC) .call).J σ' c0)
    (h2 : (Alloc.N lab ms q.1 .e).J (enter (-48) σ') c0) (hJ : (Ea ms q.1 l b w).J σx c) :
    ∃ old, b = ms.heap + 16 * old + ms.off 2 τ8 ∧ old + ms.units 2 τ8 ≤ ms.cells ∧ w = 2 := by
  obtain ⟨⟨σe, ⟨-, ⟨σm, ⟨hc, -⟩, -⟩, -⟩, -, -⟩, -⟩ := h1
  have hq : q.1.c0 = rdCN := h2.1 ▸ hc
  obtain ⟨-, hτ, -, hn⟩ := rdQ_facts q.2 hq
  obtain ⟨-, old, -, -, hb, hold, -, -, -, us, hus, hw⟩ := hJ
  rw [hτ] at hus
  have h8 : TermRun.accs (TermRun.close [] τ8) = some [.one] := by rfl
  have hus' : us = [.one] := Option.some.inj (hus.symm.trans h8)
  subst hus'
  rw [hn, hτ] at hb hold
  exact ⟨old, hb, hold, by rw [hw, hn]; rfl⟩

/-- **A landing state is at `wc_rodata`'s `.sp0` of `landJ`**
(`hello1_main_xa_post`). -/
theorem land_post {ms : MemSide isaLSE2} {J : AS → Ctl → Prop} {J1 J2 J3 J4 : AS → Ctl → Prop} {m0 : MachineData}
    {σC : AS} {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mRdJ0 (mNC (_root_.Executable.labels exe).label J).J σC) .call).J
        σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧ CKept (mR R) (-48) (-160) 0 mC m)
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC)
      (pN (_root_.Executable.labels exe).label (landJ ms (_root_.Executable.labels exe).label R J l b w σC)
        J1 J2 J3 J4 .s0) s c :=
  hello1_main_xa_post hFF hkeep (fun σx σ c0 _ hJx h1 h2 => ⟨q, σx, σ, c0, hJx, h1, h2, rfl⟩) h

end Land

end Spike.Lib.A64.Flow.Hello1
