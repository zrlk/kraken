/-
**wake.w on AArch64: main back from a refused `clone` does not return, at
`h1`'s level** (the spawn's refusal half): from
`WakeBoxW.RefB` (main past the clone's `svc` with a refusal in `x0`, its
frame in `wc_main`'s region `R`, the frames `[]`), a segment inside
`h1`'s fragment `W1W ∧ X1W` under `h1`'s outside move `K1W` and memory side
`ms1W` into nothing: the state is at the refusal path's first node
(`SpawnFail.refuse_at`) and the path does not return
(`SpawnFail.seg_spawnFailW_wake`, then `scc_rt_abort(5)`).

The path's node obligations inside `W1W ∧ X1W` (its three blocks and the
threads abort path's `StubTW`) are `RefObl`, for every region `R` of
`RefB`'s shape, frame condition `DFrame R m0` and source control at
`SpawnSrc l`.

- `W1X`: `h1`'s fragment at the frames `[]`.
- `RefObl`: the refusal path's obligations inside `W1X`.
- `at_wide`: main's parent node in the region `R` of `wc_main`'s `wcNS`
  (its offsets and slots agreeing with the narrower region's).
- `slot80_wcNS`: main's `ThreadId` word at slot `-80` at `wcNS`.
- `lbl_of_toNat`: `RefObl`'s slot words as the labels' values.
- `seg_refB`: the segment from `RefB` into nothing.
-/
import Spike.Lib.A64WakeRefuse
import Spike.Lib.A64WakeBoxW
import Spike.Lib.A64AbortHeapS

namespace Spike.Lib.WakeRefSeg

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS SegWS MemSide)
open Spike.Lib.A64.Flow (At AS BlkW DFrame CKept Abs FStable code_of)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb pfxM svcB wake_svcIn)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (fN fE flB refuse_at seg_spawnFailW_wake)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (cl)
open Spike.Lib.A64.ThreadsAb (raT)
open Spike.Lib.WakePreA (cloneAt)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeOPremW (W1W)
open Spike.Lib.WakeH1Inv (X1W K1W ms1W)
open Spike.Lib.WakeSpawnR (endR)
open Spike.Lib.WakeBoxW (RefB SpawnSrc)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays)

/-- **Main's parent node in the wider region**: main at the clone's `svc`
in `R` at `wcNS` (`hW`, offsets `oW = oP`) and at the parent's node in the
region `[-96, 16)` of the same base (`hN`, `JS`) is at the parent's node in
`R`: the slots `JS` reads (`-72`, `-16`, `-8`) are cells of both regions,
read from the same memory. -/
theorem at_wide {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {s : State}
    {c c0 : Ctl} {t k cA m x29 ra tp : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hW : At exe endPc R F (Spike.Lib.A64.WakePh.WcSp4.wcNS (_root_.Executable.labels exe).label c0 t k cA m fr)
      s c)
    (hN : At exe endPc ⟨R.base, -96, 16⟩ F ⟨cloneAt pfxM exe, oP, JS c cA x29 ra tp⟩ s c) :
    At exe endPc R F ⟨cloneAt pfxM exe, oP, JS c cA x29 ra tp⟩ s c := by
  obtain ⟨he, hn, hd, -, σ, hA, hF, -⟩ := hW
  obtain ⟨-, -, -, hpc, σ', hA', -, hc, h72, h16, h8, htp⟩ := hN
  have hsl : ∀ j : Int, j % 8 = 0 → -96 ≤ j → j + 8 ≤ 0 → σ.slot j = σ'.slot j := fun j h8' h1 h2 => by
    obtain ⟨v, hv, hσ⟩ := hA.slot j ⟨h8', by omega, by omega⟩
    obtain ⟨v', hv', hσ'⟩ := hA'.slot j ⟨h8', h1, by show j + 8 ≤ 16; omega⟩
    have he' : (⟨R.base, -96, 16⟩ : Region).addr j = R.addr j := rfl
    rw [he', hv] at hv'
    cases hv'
    rw [← hσ, hσ']
  have hr : σ.regs = σ'.regs := hA.regs.symm.trans hA'.regs
  refine ⟨he, hn, hd, hpc, σ, hA, hF, hc, ?_, ?_, ?_, ?_⟩
  · rw [hsl (-72) (by decide) (by decide) (by decide)]; exact h72
  · rw [hsl (-16) (by decide) (by decide) (by decide)]; exact h16
  · rw [hsl (-8) (by decide) (by decide) (by decide)]; exact h8
  · rw [hr]; exact htp

/-- **Main's slot `-80` at the clone**: main at `wcNS` in `R` (`hW`) has its
`ThreadId` word `m` at `-80` (`FrW`) in every abstraction at main's
offsets. -/
theorem slot80_wcNS {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {s : State}
    {c c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hW : At exe endPc R F (Spike.Lib.A64.WakePh.WcSp4.wcNS (_root_.Executable.labels exe).label c0 t k cA m fr)
      s c) :
    ∀ σ', Abs R oP s.st.1 σ' → σ'.slot (-80) = m := by
  obtain ⟨-, -, -, -, σ, hA, -, -, -, -, -, -, -, -, -, -, -, h80, -, -⟩ := hW
  intro σ' hA'
  have hk : R.Off (-80) := ⟨by decide, hlo, by omega⟩
  obtain ⟨v, hv, hσ⟩ := hA.slot (-80) hk
  obtain ⟨v', hv', hσ'⟩ := hA'.slot (-80) hk
  rw [hv] at hv'
  cases hv'
  rw [← hσ', hσ, h80]

/-- **Main's slots as labels**: with `l` fresh in the start's labels
(`hl`), the box word `cA` at `b` and the `ThreadId` word `mT` at stack 0's
`tcb` are the values of `l` and of main's `ThreadId` label in the labels
with `l` at `b` (the form `PlacedSE` reads). -/
theorem lbl_of_toNat {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {cA mT : BitVec 64}
    (hl : Spike.Lib.WakeLoadT.L0T Λ l = none) (hcA : cA.toNat = b) (hm : mT.toNat = Spike.Lib.WakeLoadT.tcb0 Λ) :
    Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T Λ) l b l = some cA.toNat ∧
      Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T Λ) l b (Spike.Lib.WakeT1.mainTidLbl 2) = some mT.toNat := by
  have hne : l ≠ Spike.Lib.WakeT1.mainTidLbl 2 := by
    rintro rfl; simp [Spike.Lib.WakeLoadT.L0T, Spike.Lib.A64ConsumerA.upd] at hl
  refine ⟨?_, ?_⟩
  · simp only [Spike.Lib.A64ConsumerA.upd, ite_true, hcA]
  · simp only [Spike.Lib.A64ConsumerA.upd, Ne.symm hne, ite_false, Spike.Lib.WakeLoadT.L0T, ite_true, hm]

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`h1`'s fragment at the frames `[]`**: `W1W ∧ X1W` at `l` placed at
`b`, `n` bytes. -/
def W1X (l : WeakMem.AllocLabel) (b n : Nat) : Frag isaLSE2 := fun s c =>
  W1W hp i E Dt Ctx ls0 l b n s c [] ∧
    X1W (Ly) (Spike.Lib.WakeOSide.aW hp i E) (endR hp i)
      (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
      (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) s c []

/-- **The refusal path's obligations inside `W1X`**, for every region `R`
of `RefB`'s shape (`OK`, 16-aligned, offsets `[≤ -336, ≥ 0)`, base 48
below stack 0's top), frame condition `DFrame R m0`, source control `cP`
at `SpawnSrc l` and main's slots `cA` (`-72`, the box at `b`) and `mT`
(`-80`, main's `ThreadId` word, stack 0's `tcb`): the refusal path's three
blocks (`SpawnFail.fN`) and the
threads abort path's obligations below main's frame (`StubTW` in
`R.callee (-80) (-48) 0` at the return address `raT`) for every caller's
state and control of the call (`SpawnFail.fE`). -/
def RefObl (l : WeakMem.AllocLabel) (b n : Nat) : Prop :=
  ∀ (R : Region) (m0 : MachineData) (cP : Ctl) (cA mT : BitVec 64), SpawnSrc l cP → cA.toNat = b →
    mT.toNat = Spike.Lib.WakeLoadT.tcb0 (Ly).Λ → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -336 →
    0 ≤ R.hi → R.base.toNat + 48 = (Ly).stacksA.toNat + 16384 →
    BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM (_root_.Executable.labels (Ly).exe).label cP cA mT .cb) (cb pfxM) ∧
      BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM (_root_.Executable.labels (Ly).exe).label cP cA mT .cl) (cl pfxM) ∧
      BlkW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) (Ly).exe (endR hp i) R (DFrame R m0)
        (fN pfxM (_root_.Executable.labels (Ly).exe).label cP cA mT .fl) flB ∧
      ∀ m1 σC c0, (fE pfxM (_root_.Executable.labels (Ly).exe).label cP cA mT).J σC c0 →
        Spike.Lib.A64.Abort.Disp.StubTW (W1X hp i E Dt Ctx ls0 l b n) (K1W hp i E) wakeSrc
          (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b) (ms1W hp i E cT ls0 l b n [])
          (Ly).exe (endR hp i) (R.callee (-80) (-48) 0)
          (fun m => DFrame R m0 m ∧ CKept R (-80) (-48) 0 m1 m ∧ Abs R oP m1 σC) c0
          (raT (_root_.Executable.labels (Ly).exe).label pfxM)

/-- **Main back from a refused clone does not return** at `h1`'s level:
from `RefB`, a segment inside `W1W ∧ X1W` into nothing, given wake's
program laid out in the layout's executable (`hl`) and the path's
obligations (`hobl`). -/
theorem seg_refB (hl : Lays (Ly).exe wakeProg (Ly).pfx) {l : WeakMem.AllocLabel} {b n : Nat}
    (hobl : RefObl hp i E cT Dt Ctx ls0 l b n) :
    SegWS (fun s c fs => W1W hp i E Dt Ctx ls0 l b n s c fs ∧
        X1W (Ly) (Spike.Lib.WakeOSide.aW hp i E) (endR hp i)
          (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
          (Spike.Lib.A64ConsumerA.updN (Spike.Lib.WakeLoadT.ls0T ls0) l n) s c fs)
      (K1W hp i E) wakeSrc (Spike.Lib.A64ConsumerA.upd (Spike.Lib.WakeLoadT.L0T (Ly).Λ) l b)
      (ms1W hp i E cT ls0 l b n) (RefB hp i l b) (fun _ _ _ => False) := by
  have : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  have hcode := code_of hl rfl wake_svcIn (q := cloneAt pfxM (Ly).exe) rfl
  -- the entry: the refusal path's first node in `R`, the obligations there
  let P : Region × MachineData × Ctl × BitVec 64 × BitVec 64 → FragS isaLSE2 := fun g s c fs =>
    (SpawnSrc l g.2.2.1 ∧ g.2.2.2.1.toNat = b ∧ g.2.2.2.2.toNat = Spike.Lib.WakeLoadT.tcb0 (Ly).Λ ∧ g.1.OK ∧
      g.1.base.toNat % 16 = 0 ∧ g.1.lo ≤ -336 ∧ 0 ≤ g.1.hi ∧ g.1.base.toNat + 48 = (Ly).stacksA.toNat + 16384) ∧
    (At (Ly).exe (endR hp i) g.1 (DFrame g.1 g.2.1)
      (fN pfxM (_root_.Executable.labels (Ly).exe).label g.2.2.1 g.2.2.2.1 g.2.2.2.2 .cb)).at [] s c fs
  refine (SegWS.exists_pre (P := P) fun g => ?_).mono_pre ?_
  · by_cases hg : SpawnSrc l g.2.2.1 ∧ g.2.2.2.1.toNat = b ∧ g.2.2.2.2.toNat = Spike.Lib.WakeLoadT.tcb0 (Ly).Λ ∧
        g.1.OK ∧ g.1.base.toNat % 16 = 0 ∧ g.1.lo ≤ -336 ∧ 0 ≤ g.1.hi ∧
        g.1.base.toNat + 48 = (Ly).stacksA.toNat + 16384
    · obtain ⟨hsrc, hcA, hmT, hR, hal, hlo, hhi, hst⟩ := hg
      obtain ⟨hcb, hcl, hfl, hstub⟩ := hobl g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 hsrc hcA hmT hR hal hlo hhi hst
      refine (SegWS.liftS_noret [] (seg_spawnFailW_wake hl rfl (Q := fun _ _ => False)
        (FStable.dframe g.1 g.2.1) hR hal (by omega) hhi rfl hcb hcl hfl hstub) (fun _ _ h => h) _).mono_pre
        fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hg h.1
  · rintro s c fs ⟨rfl, hsrc, s0, r, rfl, hr, R, F₂, J, σC, cA, m, fr, t, hR, hal, hlo, hhi, hst, -, -, -, hW, -,
      hN, -, hcA, hm⟩
    refine ⟨(R, (abi.ret s0 r).st.1, c, cA, m), ⟨hsrc, hcA, hm, hR, hal, hlo, hhi, hst⟩, ?_, rfl⟩
    exact refuse_at hcode (at_wide (R := R) (show R.lo ≤ -96 by omega) hhi hW hN) hr
      (slot80_wcNS (R := R) (show R.lo ≤ -80 by omega) hhi hW)

end Inst

end Spike.Lib.WakeRefSeg

/-- info: 'Spike.Lib.WakeRefSeg.at_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefSeg.at_wide

/-- info: 'Spike.Lib.WakeRefSeg.seg_refB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefSeg.seg_refB

/-- info: 'Spike.Lib.WakeRefSeg.lbl_of_toNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefSeg.lbl_of_toNat
