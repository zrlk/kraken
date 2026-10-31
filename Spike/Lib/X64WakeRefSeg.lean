/-
**wake.w on x86-64: main back from a refused `clone` does not return, at
`h1`'s level** (the spawn's refusal half; the twin of
`Spike/Lib/A64WakeRefSeg.lean`): from `WakeBoxW.RefB` (main past the
clone's `syscall` with a refusal in `%rax`, its frame in `wc_main`'s region
`R`, the frames `[]`), a segment inside `h1`'s fragment `W1X` under `h1`'s
outside move `K1W` and memory side `ms1W` into nothing: the state is at the
refusal path's first node (`SpawnFail.refuse_at`) and the path does not
return (`SpawnFail.seg_spawnFailW`, then `scc_rt_abort(5)`). This is
`WakeBoxW.hB_box`'s `hseg`.

The path's node obligations inside `W1X` (its test, its three blocks and
the threads abort path's `StubTW`) are `RefObl`, for every region `R` of
`RefB`'s shape, frame condition `DFrame R m0` and source control at
`SpawnSrc l`.

- `RefObl`: the refusal path's obligations inside `W1X`.
- `lbl_of_toNat`: `RefObl`'s slot words as the labels' values.
- `seg_refB`: the segment from `RefB` into nothing.

**Unlike AArch64**: `refuse_at` starts at the clone's node `wcNS` in `R`
(its frame words carry the slots the path reads), so A64's `at_wide` (the
parent's node `JS` widened to `R`) and `slot80_wcNS` are not needed; the
fragment is `WakeBoxW.W1X` at the frames `[]` (A64 defines its own `W1X`
here); the path has four nodes (`ts` a row, `je`, `x22`, `fl`; A64 `cb`,
`cl`, `fl`) and the dispatcher's region is `R.callee (-72 - 8) (-24) 16`
below the return address at `-72` (A64 `R.callee (-80) (-48) 0`), the
return address `raT lab ".Lwc_main"`; `RefB`'s region has no alignment and
is `64` below stack 0's top, `R.lo ≤ -320`, `16 ≤ R.hi` (A64: 16-aligned,
`48`, `-336`, `0`); the one-frame lift into nothing is
`SegWS.liftS`'s with an empty post (A64's `liftS_noret` lives in an AArch64
module). No absolute address appears in this file.
-/
import Spike.Lib.X64WakeRefuse
import Spike.Lib.X64WakeBoxW
import Spike.Lib.X64WakeSpawnAt

namespace Spike.Lib.X64.WakeRefSeg

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.SpawnFail (fN fE flB refuse_at seg_spawnFailW wake_failIn)
open Spike.Lib.X64.WakePh.Parent (jeB x22B)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64.WakeBoxW (RefB SpawnSrc W1X)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (Lays)

/-- **Main's slots as labels**: with `l` fresh in the start's labels
(`hl`), the box word `cA` at `b` and the `ThreadId` word `mT` at stack 0's
`tcb` are the values of `l` and of main's `ThreadId` label in the labels
with `l` at `b` (the form `PlacedSE` reads). -/
theorem lbl_of_toNat {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {cA mT : BitVec 64}
    (hl : L0T Λ l = none) (hcA : cA.toNat = b) (hm : mT.toNat = tcb0 Λ) :
    Spike.Lib.X64ConsumerA.upd (L0T Λ) l b l = some cA.toNat ∧
      Spike.Lib.X64ConsumerA.upd (L0T Λ) l b (mainTidLbl 2) = some mT.toNat := by
  have hne : l ≠ mainTidLbl 2 := by
    rintro rfl; simp [L0T, Spike.Lib.X64ConsumerA.upd] at hl
  refine ⟨?_, ?_⟩
  · simp only [Spike.Lib.X64ConsumerA.upd, ite_true, hcA]
  · simp only [Spike.Lib.X64ConsumerA.upd, Ne.symm hne, ite_false, L0T, ite_true, hm]

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The end of text. -/
local notation "eR" => WakeH1Inv.endR hp i

set_option hygiene false in
/-- The layout's labels. -/
local notation "LB" => (_root_.Executable.labels (Ly).exe).label

/-- **The refusal path's obligations inside `W1X`**, for every region `R`
of `RefB`'s shape (`OK`, offsets `[≤ -320, ≥ 16)`, base `64` below stack
0's top), frame condition `DFrame R m0`, source control `cP` at
`SpawnSrc l` and main's slots `cA` (`-16`, the box at `b`) and `mT` (`-8`,
main's `ThreadId` word, stack 0's `tcb`): the refusal path's test and
three blocks (`SpawnFail.fN`) and the threads abort path's obligations
below main's frame (`StubTW` in `R.callee (-72 - 8) (-24) 16` at the return
address `raT`) for every caller's state and control of the call
(`SpawnFail.fE`). -/
def RefObl (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64), SpawnSrc l cP → cA.toNat = b →
    mT.toNat = tcb0 (Ly).Λ → R.OK → R.lo ≤ -320 → 16 ≤ R.hi → R.base.toNat + 64 = (Ly).stacksA.toNat + 16384 →
    NodeW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (WakeH1Inv.K1W hp i E) (Ly).exe eR R (DFrame R m0)
        (fN LB cP cA mT .ts) ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (WakeH1Inv.K1W hp i E) (Ly).exe eR R (DFrame R m0)
        (fN LB cP cA mT .je) jeB ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (WakeH1Inv.K1W hp i E) (Ly).exe eR R (DFrame R m0)
        (fN LB cP cA mT .x22) x22B ∧
      BlkW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (WakeH1Inv.K1W hp i E) (Ly).exe eR R (DFrame R m0)
        (fN LB cP cA mT .fl) flB ∧
      ∀ m1 σC c0, (fE LB cP cA mT).J σC c0 →
        Abort.Disp.StubTW (fun s c => W1X asm hp i E Dt Ctx ls0 l b n s c []) (WakeH1Inv.K1W hp i E) wakeSrc
          (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (WakeH1Inv.ms1W asm hp i E cT ls0 l b n [])
          (Ly).exe eR (R.callee (-72 - 8) (-24) 16)
          (fun m' => DFrame R m0 m' ∧ CKept R (-72 - 8) (-24) 16 m1 m' ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m1 σC) c0
          (raT LB ".Lwc_main")

/-- **Main back from a refused clone does not return** at `h1`'s level:
from `RefB`, a segment inside `W1X` into nothing (`hB_box`'s `hseg`), given
wake's cells laid out in the layout's executable (`hl`) and the path's
obligations (`hobl`). -/
theorem seg_refB (hl : Lays (Ly).exe wakeCells (Ly).pfx) {l : WeakMem.AllocLabel} {b n : Nat}
    (hobl : RefObl asm hp i E cT Dt Ctx ls0 l b n) :
    SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) wakeSrc
      (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
      (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (RefB hp i l b) (fun _ _ _ => False) := by
  haveI := (Ly).valid
  have hcode := Spike.Lib.X64.WakePh.wake_svcCode hl (endPc := eR) rfl
  -- the entry: the refusal path's first node in `R`, the obligations there
  let P : Region × MachineData × Ctl × BitVec 64 × BitVec 64 → FragS isa := fun g s c fs =>
    (SpawnSrc l g.2.2.1 ∧ g.2.2.2.1.toNat = b ∧ g.2.2.2.2.toNat = tcb0 (Ly).Λ ∧ g.1.OK ∧
      g.1.lo ≤ -320 ∧ 16 ≤ g.1.hi ∧ g.1.base.toNat + 64 = (Ly).stacksA.toNat + 16384) ∧
    (At (Ly).exe eR g.1 (DFrame g.1 g.2.1) (fN LB g.2.2.1 g.2.2.2.1 g.2.2.2.2 .ts)).at [] s c fs
  refine (SegWS.exists_pre (P := P) fun g => ?_).mono_pre ?_
  · by_cases hg : SpawnSrc l g.2.2.1 ∧ g.2.2.2.1.toNat = b ∧ g.2.2.2.2.toNat = tcb0 (Ly).Λ ∧
        g.1.OK ∧ g.1.lo ≤ -320 ∧ 16 ≤ g.1.hi ∧ g.1.base.toNat + 64 = (Ly).stacksA.toNat + 16384
    · obtain ⟨hsrc, hcA, hmT, hR, hlo, hhi, hst⟩ := hg
      obtain ⟨hts, hje, hx22, hfl, hstub⟩ := hobl g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 hsrc hcA hmT hR hlo hhi hst
      refine ((SegWS.liftS [] (seg_spawnFailW hl rfl wake_failIn (Q := fun _ _ => False)
        (FStable.dframe g.1 g.2.1) hR (by omega) hhi rfl hts hje hx22 hfl hstub) fun _ _ h => h).mono_post
        fun _ _ _ h => h.1.elim).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · rintro s c fs ⟨rfl, hsrc, s0, r, rfl, hr, R, F₂, J, σC, cA, m, fr, t, hR, hlo, hhi, hst, -, -, -, hW, -,
      -, -, hcA, hm⟩
    refine ⟨(R, (abi.ret s0 r).st.1, c, cA, m), ⟨hsrc, hcA, hm, hR, hlo, hhi, hst⟩, ?_, rfl⟩
    exact refuse_at hcode hW hr

end Inst

end Spike.Lib.X64.WakeRefSeg

/-- info: 'Spike.Lib.X64.WakeRefSeg.lbl_of_toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefSeg.lbl_of_toNat

/-- info: 'Spike.Lib.X64.WakeRefSeg.seg_refB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefSeg.seg_refB
