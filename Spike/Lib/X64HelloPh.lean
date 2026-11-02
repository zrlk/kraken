/-
**hello.w's extended phase** (x86-64): the twin of `Spike/Lib/A64HelloPh.lean`, and
`Spike/Lib/X64WakePh.lean` restated at hello.w's cells (`SccCode.helloCells` of
`Spike/Lib/X64HelloCode.lean`, code base `lo = 0x401000`): the canonical phase index with
the fifth bit of `Spike/Lib/X64PhExt.lean` set on the pcs after the thread counter's add
(`helloR`, `inR`, `phH`).

`helloR` is two code ranges named by the cells' labels: the rest of
`scc_rt_thread_reserve` after its `lock xadd` (`.entry` + 27 up to `scc_rt_thread_init`),
and `wc_main` from the reserve's return point `.x23` up to `.stk` (the child stub
`.child.scc_rt_thr_worker` lies inside it). Every fact is decided by `decide +kernel` on the
cells' labels (through `codeT`, `codeT_eq`); no pc range is a hypothesis. The reserve is
wake.w's byte for byte (but its abort label `.x7`), 37 bytes later (hello.w's `printL`,
`print` and setup block `wc_rodata` come before it).

- `RC`, `TC`, `SC`: the resolved ranges, the canonical phase table and the sites
  (`helloR_eq`, `phTab_eq`, `sites_eq`); `phH_eq`, `okPc_eq`.
- `ownH`: wake's `X64.WakePh.ownW` (generic in the layout and the counter).
- `resPhH`: `ResPh` at `phH`, returning to `wc_main`'s `.x23`.
- `phH_out`, `phH_in`: off `helloR` the canonical phase, in it plus `16`.
- `instOkH`: the instance's facts at `phH` with `ownH`.

Unlike AArch64 (`Spike/Lib/A64HelloPh.lean`): the code base is the linked `.text` base
`0x401000` (not the canonical `0x210550`), `helloR` has two ranges (the child stub is inside
`wc_main`'s range), and the reserve's single step is one `.step entryL 0 7` fact (x86-64
facts carry the byte length).
-/
import Spike.Lib.X64PhExt
import Spike.Lib.X64WakePh
import Spike.Lib.X64HelloCode
import Spike.Lib.X64PhRec
import Spike.Lib.Rt.X64RtReservePh

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhRange PhTab inRs phOf phTabOf okPcOf sitesOf codeT codeT_eq blkOkN factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.PhExt (phExt)
open Spike.Lib.X64.Flow.Reserve
open Spike.Lib.X64.Rt.Reserve (ResPh ntA siPcs resPcs)
open Spike.Lib.X64.Rt.PhOfTab
open Spike.Lib.X64.Rt (ownUpdB InstOk RuntimeLayout)
open Spike.Lib.X64Consumer

/-- The code base: the linked `.text` base `0x401000` of `ld`'s default layout (wake's
`X64.WakePh.lo`; hello.w's executable is linked the same way).

Unlike AArch64, whose phase is at `Scc.Cert.Link.canonical.codeLo`, the x86-64
phase is at the linked binary's `.text` base, so the root's `hlo` is decided. -/
abbrev lo : Nat := 0x401000

/-! ## The ranges and the phase -/

/-- **The pcs after the thread counter's add**, by the cells' labels. -/
def helloR : List PhRange :=
  [⟨".Lscc_rt_thread_reserve.entry", 27, "scc_rt_thread_init", 0⟩,
    ⟨".Lwc_main.x23", 0, ".Lwc_main.stk", 0⟩]

/-- The pc is in `helloR` (resolved in the cells at the canonical base). -/
def inR (pc : Nat) : Bool :=
  match helloR.mapM (PhRange.resolve (codeLabel lo helloCells)) with
  | some rs => inRs rs pc
  | none => false

/-- **hello.w's extended phase index.** -/
def phH : Nat → Nat := phExt (phOf lo helloCells) inR

/-- The resolved ranges. -/
def RC : List (Nat × Nat) := [(4199519, 4199582), (4203726, 4203948)]

/-- The canonical phase table of the cells. -/
def TC : PhTab where
  p := [(4198400, 4198487), (4199029, 4199233)]
  l := [(4199976, 4200170)]
  n := [(4198400, 4198500), (4199029, 4199484), (4199582, 4199606), (4199732, 4200200)]
  t := [(4198400, 4198500), (4199029, 4199484), (4199582, 4199606), (4199732, 4200315)]

/-- The sites (`siteLabels` at `Link.abortName`). -/
def SC : List Nat := [4200314, 4200354, 4202692, 4202760, 4202828, 4202896, 4202964]

theorem helloR_eq : helloR.mapM (PhRange.resolve (codeLabel lo helloCells)) = some RC := by
  rw [← codeT_eq]; decide +kernel

theorem phTab_eq : phTabOf lo helloCells = some TC := by
  unfold phTabOf; rw [← codeT_eq]; decide +kernel

theorem sites_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    sitesOf lo helloCells Λ = some SC := by
  unfold sitesOf Scc.Cert.Rt.X64.sitesBy Scc.Cert.Rt.X64.siteLabels
  rw [hΛ, ← codeT_eq]; decide +kernel

/-- The phase through the resolved tables. -/
def phC (pc : Nat) : Nat := TC.ph pc + 16 * (inRs RC pc).toNat

/-- The off-site pcs through the resolved sites. -/
def okC (pc : Nat) : Bool := !(SC.contains pc)

theorem phH_eq : phH = phC := by
  funext pc
  unfold phH phExt phC phOf inR
  rw [phTab_eq, helloR_eq]

theorem inR_eq : inR = inRs RC := by
  funext pc; unfold inR; rw [helloR_eq]

/-- **Off `helloR` the extended phase is the canonical one.** -/
theorem phH_out {pc : Nat} (h : inRs RC pc = false) : phH pc = phOf lo helloCells pc := by
  unfold phH phExt; rw [inR_eq, h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- **In `helloR` it is the canonical one plus `16`.** -/
theorem phH_in {pc : Nat} (h : inRs RC pc = true) : phH pc = phOf lo helloCells pc + 16 := by
  unfold phH phExt; rw [inR_eq, h, Bool.toNat_true, Nat.mul_one]

theorem okPc_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    okPcOf lo helloCells Λ = okC := by
  funext pc; unfold okPcOf okC; rw [sites_eq hΛ]

/-! ## The owned words -/

/-- **The owned words at an extended phase index**: wake's `ownW`
(`X64PhRec.ownOf`'s four counters and `scc_rt_nthreads` at `a` by the fifth
bit). -/
abbrev ownH (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : List (Loc × Val) := Spike.Lib.X64.WakePh.ownW L a i

/-! ## `scc_rt_thread_reserve`'s phase facts -/

/-- The reserve's blocks' checks at `phH`, returning to `wc_main`'s `.x23`. -/
theorem resBlks :
    blkOkN (codeT lo helloCells) okC phC 4199484 0 rPro (some (".Lwc_main.x23", 0)) none = true ∧
    blkOkN (codeT lo helloCells) okC phC 4199492 7 rArg (some (".Lwc_main.x23", 0)) none = true ∧
    blkOkN (codeT lo helloCells) okC phC 4199492 27 rBnd (some (".Lwc_main.x23", 0)) none = true ∧
    blkOkN (codeT lo helloCells) okC phC 4199492 65 rJ (some (".Lwc_main.x23", 0)) none = true ∧
    blkOkN (codeT lo helloCells) okC phC 4199573 0 rRet (some (".Lwc_main.x23", 0)) none = true := by
  decide +kernel

/-- The reserve's labels. -/
theorem resLabs : codeLabel lo helloCells fnL = some 4199484 ∧ codeLabel lo helloCells entryL = some 4199492 ∧
    codeLabel lo helloCells okL = some 4199573 := by
  rw [← codeT_eq]; decide +kernel

/-- The reserve's single step and the add off the sites, at `phH`. -/
theorem resSteps : factOk (codeT lo helloCells) okC phC (.step entryL 0 7) = true ∧
    factOk (codeT lo helloCells) okC phC (.ok entryL 22) = true ∧ phC 4199514 = 0 ∧ phC 4199519 = 16 := by
  decide +kernel

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- `lab l + k` at a resolved label. -/
theorem pc_eq (hlab : ∀ l a, codeLabel lo helloCells l = some a → lab l = Int64.ofNat a) {l : Label} {a : Nat}
    (hl : codeLabel lo helloCells l = some a) (k : Nat) :
    (lab l + Int64.ofNat k).toBitVec.toNat = (a + k) % 2 ^ 64 := by
  rw [hlab l a hl, toNat_add]

/-- **`ResPh` at `phH`** with `ownW`, returning to `wc_main`'s `.x23`, the
labels resolved as the certificate's (`hlab`), the counter off the four
counters (`hsep`); the take's field given. -/
theorem resPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {Tk : State → Prop}
    (hlab : ∀ l a, codeLabel lo helloCells l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s) :
    ResPh (okPcOf lo helloCells Λ) phH Tk (ownH L (ntA lab)) lab (lab ".Lwc_main.x23") := by
  obtain ⟨bE, bA, bB, bJ, bO⟩ := resBlks
  obtain ⟨lF, lE, lO⟩ := resLabs
  obtain ⟨s0, s22, p22, p27⟩ := resSteps
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at bE bA bB bJ bO
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at s0 s22
  rw [← phH_eq] at p22 p27
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.X64.deadN (codeLabel lo helloCells) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', some (".Lwc_main.x23", 0) = some (r, o') →
      lab ".Lwc_main.x23" = lab r + Int64.ofNat o' := fun _ _ h => by
    cases h; exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm
  have hrmw : (rmwPc lab).toBitVec.toNat = 4199514 := pc_eq hlab lE 22
  have hrmw5 : (rmwPc lab + Int64.ofNat 5).toBitVec.toNat = 4199519 := by
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
    rmwIn := ⟨(0#64).setWidth 128, by rw [hrmw, p22]; simp [ownH, Spike.Lib.X64.WakePh.ownW]⟩
    rmwUpd := by
      obtain ⟨h1, h2, h3, h4⟩ := hsep
      rw [hrmw, hrmw5, p22, p27]
      simp [ownUpdB, ownH, Spike.Lib.X64.WakePh.ownW, Spike.Lib.X64.PhRec.ownOf, Ne.symm h1, Ne.symm h2,
        Ne.symm h3, Ne.symm h4] }

/-! ## The instance's facts -/

/-- **The instance's facts at `phH`** with `ownW` (the counter at `a`) and
a take's phase `TkH` of the phase index, for a layout of the cells at the
canonical base, the take site at its label (`hsite`). -/
theorem instOkH {L : RuntimeLayout} (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkH : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s)))
      (fun s => TkH (phH (pcOf s))) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo helloCells L.Λ) phH L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (ownH L a) h, by simp only [h]⟩
  off := by
    have h := Spike.Lib.X64.PhRec.off L (rS := rS) hsite
    unfold Spike.Lib.X64.PhRec.okPc at h
    rw [hp, hlo] at h
    exact h

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.helloR_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.helloR_eq

/-- info: 'Spike.Lib.X64.HelloPh.phTab_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.phTab_eq

/-- info: 'Spike.Lib.X64.HelloPh.sites_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.sites_eq

/-- info: 'Spike.Lib.X64.HelloPh.phH_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.phH_eq

/-- info: 'Spike.Lib.X64.HelloPh.inR_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.inR_eq

/-- info: 'Spike.Lib.X64.HelloPh.phH_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.phH_out

/-- info: 'Spike.Lib.X64.HelloPh.phH_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.phH_in

/-- info: 'Spike.Lib.X64.HelloPh.okPc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.okPc_eq

/-- info: 'Spike.Lib.X64.HelloPh.resBlks' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.resBlks

/-- info: 'Spike.Lib.X64.HelloPh.resLabs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.resLabs

/-- info: 'Spike.Lib.X64.HelloPh.resSteps' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.resSteps

/-- info: 'Spike.Lib.X64.HelloPh.pc_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.pc_eq

/-- info: 'Spike.Lib.X64.HelloPh.resPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.resPhH

/-- info: 'Spike.Lib.X64.HelloPh.instOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.instOkH
