/-
**wake.w's extended phase** (x86-64; twin of `Spike/Lib/A64WakePh.lean`):
the canonical phase index of wake.w's cells (`phOf` at the canonical code
base `0x400000`, `SccCode.wakeCells` of `Spike/Lib/X64WakeCode.lean`) with
the fifth bit of `Spike/Lib/X64PhExt.lean` set on the pcs after the thread
counter's add (`wakeR`, `inR`, `phW`). Wake-specific phase extension;
generic multi-spawn needs a reserve phase bit in PhasesX64 (trusted).

`wakeR` is two code ranges named by the cells' labels: the rest of
`scc_rt_thread_reserve` after its `lock xadd` (`.entry` + 27 up to
`scc_rt_thread_init`), and `wc_main` from the reserve's return point
`.x19` up to `.stk` (on x86-64 the child stub
`.child.scc_rt_thr_worker` lies inside it; A64 needs a third range).
Every fact is decided by `decide +kernel` on the cells' labels (through
the keyed table `codeT`, `codeT_eq`); no pc range is a hypothesis.

- `RC`, `TC`, `SC`: the resolved ranges, the canonical phase table and the
  sites (`wakeR_eq`, `phTab_eq`, `sites_eq`); `phW_eq`, `okPc_eq`: the phase
  and the off-site pcs through them.
- `ownW`: `X64PhRec.ownOf` with `scc_rt_nthreads` at `0`, `1` by the fifth
  bit.
- `resPhW`: `ResPh` at `phW`, returning to `wc_main`'s `.x19` (the
  reserve's return point, in `wakeR` as the pcs after the add are;
  `resPh_of_a13code` returns to `scc_rt_main`'s, outside it). The take's
  field `noTk` is asked of the caller.
- `phW_out`, `phW_in`: off `wakeR` the canonical phase, in it plus `16`.
- `instOkW`: the instance's facts at `phW` with `ownW`.
-/
import Spike.Lib.X64PhExt
import Spike.Lib.X64WakeCode
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64RtReservePh

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhRange PhTab inRs phOf phTabOf okPcOf sitesOf codeT codeT_eq blkOkN factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.PhExt (phExt)
open Spike.Lib.X64.Flow.Reserve
open Spike.Lib.X64.Rt.Reserve (ResPh ntA siPcs resPcs)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.Rt (ownUpdB InstOk RuntimeLayout)
open Spike.Lib.X64Consumer

/-- The code base: the linked `.text` base `0x401000` of `ld`'s default layout
(`Spike.Test.WakeLinkedX64.Λe.code.lo`, `WakeLinkedX64.hlo`).

Unlike AArch64, whose phase is at `Scc.Cert.Link.canonical.codeLo`, the x86-64
phase is at the linked binary's `.text` base, so the root's `hlo` is decided. -/
abbrev lo : Nat := 0x401000

/-! ## The ranges and the phase -/

/-- **The pcs after the thread counter's add**, by the cells' labels. -/
def wakeR : List PhRange :=
  [⟨".Lscc_rt_thread_reserve.entry", 27, "scc_rt_thread_init", 0⟩,
    ⟨".Lwc_main.x1", 0, ".Lwc_main.stk", 0⟩]

/-- The pc is in `wakeR` (resolved in the cells at the canonical base). -/
def inR (pc : Nat) : Bool :=
  match wakeR.mapM (PhRange.resolve (codeLabel lo wakeCells)) with
  | some rs => inRs rs pc
  | none => false

/-- **wake.w's extended phase index.** -/
def phW : Nat → Nat := phExt (phOf lo wakeCells) inR

/-- The resolved ranges. -/
def RC : List (Nat × Nat) := [(4199482, 4199545), (4203387, 4203552)]

/-- The canonical phase table of the cells. -/
def TC : PhTab where
  p := [(4198400, 4198487), (4198992, 4199196)]
  l := [(4199939, 4200133)]
  n := [(4198400, 4198500), (4198992, 4199447), (4199545, 4199569), (4199695, 4200163)]
  t := [(4198400, 4198500), (4198992, 4199447), (4199545, 4199569), (4199695, 4200278)]

/-- The sites (`siteLabels` at `Link.abortName`). -/
def SC : List Nat := [4200277, 4200317, 4202693, 4202761, 4202829, 4202897, 4202965]

theorem wakeR_eq : wakeR.mapM (PhRange.resolve (codeLabel lo wakeCells)) = some RC := by
  rw [← codeT_eq]; decide +kernel

theorem phTab_eq : phTabOf lo wakeCells = some TC := by
  unfold phTabOf; rw [← codeT_eq]; decide +kernel

theorem sites_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    sitesOf lo wakeCells Λ = some SC := by
  unfold sitesOf Scc.Cert.Rt.X64.sitesBy Scc.Cert.Rt.X64.siteLabels
  rw [hΛ, ← codeT_eq]; decide +kernel

/-- The phase through the resolved tables. -/
def phC (pc : Nat) : Nat := TC.ph pc + 16 * (inRs RC pc).toNat

/-- The off-site pcs through the resolved sites. -/
def okC (pc : Nat) : Bool := !(SC.contains pc)

theorem phW_eq : phW = phC := by
  funext pc
  unfold phW phExt phC phOf inR
  rw [phTab_eq, wakeR_eq]

theorem inR_eq : inR = inRs RC := by
  funext pc; unfold inR; rw [wakeR_eq]

/-- **Off `wakeR` the extended phase is the canonical one.** -/
theorem phW_out {pc : Nat} (h : inRs RC pc = false) : phW pc = phOf lo wakeCells pc := by
  unfold phW phExt; rw [inR_eq, h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- **In `wakeR` it is the canonical one plus `16`.** -/
theorem phW_in {pc : Nat} (h : inRs RC pc = true) : phW pc = phOf lo wakeCells pc + 16 := by
  unfold phW phExt; rw [inR_eq, h, Bool.toNat_true, Nat.mul_one]

theorem okPc_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    okPcOf lo wakeCells Λ = okC := by
  funext pc; unfold okPcOf okC; rw [sites_eq hΛ]

/-! ## The owned words -/

/-- **The owned words at an extended phase index**: `X64PhRec.ownOf`'s four
counters (by the low bits) and `scc_rt_nthreads` (at `a`), `0` before the
add and `1` after it (the fifth bit). -/
def ownW (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : List (Loc × Val) :=
  Spike.Lib.X64.PhRec.ownOf L i ++ [(⟨a, 8⟩, (if i / 16 % 2 = 1 then 1#64 else 0#64).setWidth 128)]

/-! ## `scc_rt_thread_reserve`'s phase facts -/

/-- The reserve's blocks' checks at `phW`, returning to `wc_main`'s `.x19`. -/
theorem resBlks :
    blkOkN (codeT lo wakeCells) okC phC 4199447 0 rPro (some (".Lwc_main.x1", 0)) none = true ∧
    blkOkN (codeT lo wakeCells) okC phC 4199455 7 rArg (some (".Lwc_main.x1", 0)) none = true ∧
    blkOkN (codeT lo wakeCells) okC phC 4199455 27 rBnd (some (".Lwc_main.x1", 0)) none = true ∧
    blkOkN (codeT lo wakeCells) okC phC 4199455 65 rJ (some (".Lwc_main.x1", 0)) none = true ∧
    blkOkN (codeT lo wakeCells) okC phC 4199536 0 rRet (some (".Lwc_main.x1", 0)) none = true := by
  decide +kernel

/-- The reserve's labels. -/
theorem resLabs : codeLabel lo wakeCells fnL = some 4199447 ∧ codeLabel lo wakeCells entryL = some 4199455 ∧
    codeLabel lo wakeCells okL = some 4199536 := by
  rw [← codeT_eq]; decide +kernel

/-- The reserve's single step and the add off the sites, at `phW`. -/
theorem resSteps : factOk (codeT lo wakeCells) okC phC (.step entryL 0 7) = true ∧
    factOk (codeT lo wakeCells) okC phC (.ok entryL 22) = true ∧ phC 4199477 = 0 ∧ phC 4199482 = 16 := by
  decide +kernel

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- `lab l + k` at a resolved label. -/
theorem pc_eq (hlab : ∀ l a, codeLabel lo wakeCells l = some a → lab l = Int64.ofNat a) {l : Label} {a : Nat}
    (hl : codeLabel lo wakeCells l = some a) (k : Nat) :
    (lab l + Int64.ofNat k).toBitVec.toNat = (a + k) % 2 ^ 64 := by
  rw [hlab l a hl, toNat_add]

/-- **`ResPh` at `phW`** with `ownW`, returning to `wc_main`'s `.x19`, the
labels resolved as the certificate's (`hlab`), the counter off the four
counters (`hsep`); the take's field given. -/
theorem resPhW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {Tk : State → Prop}
    (hlab : ∀ l a, codeLabel lo wakeCells l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s) :
    ResPh (okPcOf lo wakeCells Λ) phW Tk (ownW L (ntA lab)) lab (lab ".Lwc_main.x1") := by
  obtain ⟨bE, bA, bB, bJ, bO⟩ := resBlks
  obtain ⟨lF, lE, lO⟩ := resLabs
  obtain ⟨s0, s22, p22, p27⟩ := resSteps
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at bE bA bB bJ bO
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at s0 s22
  rw [← phW_eq] at p22 p27
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', some (".Lwc_main.x1", 0) = some (r, o') →
      lab ".Lwc_main.x1" = lab r + Int64.ofNat o' := fun _ _ h => by
    cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm
  have hrmw : (rmwPc lab).toBitVec.toNat = 4199477 := pc_eq hlab lE 22
  have hrmw5 : (rmwPc lab + Int64.ofNat 5).toBitVec.toNat = 4199482 := by
    unfold rmwPc; rw [hlab _ _ lE, Int64.add_assoc, ← Int64.ofNat_add, toNat_add]
  exact {
    e := blkPh_of_blkOkN hlab lF hr hn bE
    arg := blkPh_of_blkOkN hlab lE hr hn bA
    bnd := blkPh_of_blkOkN hlab lE hr hn bB
    j := blkPh_of_blkOkN hlab lE hr hn bJ
    ok := blkPh_of_blkOkN hlab lO hr hn bO
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact step_of_factOk hlab s0
    rmwOk := ok_of_factOk hlab s22
    noTk := noTk
    rmwIn := ⟨(0#64).setWidth 128, by rw [hrmw, p22]; simp [ownW]⟩
    rmwUpd := by
      obtain ⟨h1, h2, h3, h4⟩ := hsep
      rw [hrmw, hrmw5, p22, p27]
      simp [ownUpdB, ownW, Spike.Lib.X64.PhRec.ownOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4] }

/-! ## The instance's facts -/

/-- **The instance's facts at `phW`** with `ownW` (the counter at `a`) and
a take's phase `TkW` of the phase index, for a layout of the cells at the
canonical base, the take site at its label (`hsite`). -/
theorem instOkW {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) phW L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (ownW L a) h, by simp only [h]⟩
  off := by
    have h := Spike.Lib.X64.PhRec.off L (rS := rS) hsite
    unfold Spike.Lib.X64.PhRec.okPc at h
    rw [hp, hlo] at h
    exact h

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.wakeR_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.wakeR_eq

/-- info: 'Spike.Lib.X64.WakePh.phTab_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.phTab_eq

/-- info: 'Spike.Lib.X64.WakePh.sites_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.sites_eq

/-- info: 'Spike.Lib.X64.WakePh.phW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.phW_eq

/-- info: 'Spike.Lib.X64.WakePh.inR_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.inR_eq

/-- info: 'Spike.Lib.X64.WakePh.phW_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.phW_out

/-- info: 'Spike.Lib.X64.WakePh.phW_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.phW_in

/-- info: 'Spike.Lib.X64.WakePh.okPc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.okPc_eq

/-- info: 'Spike.Lib.X64.WakePh.resBlks' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.resBlks

/-- info: 'Spike.Lib.X64.WakePh.resLabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.resLabs

/-- info: 'Spike.Lib.X64.WakePh.resSteps' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.resSteps

/-- info: 'Spike.Lib.X64.WakePh.pc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.pc_eq

/-- info: 'Spike.Lib.X64.WakePh.resPhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.resPhW

/-- info: 'Spike.Lib.X64.WakePh.instOkW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOkW
