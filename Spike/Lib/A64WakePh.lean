/-
**wake.w's extended phase** (AArch64): the canonical phase index of
wake.w's certificate (`phOf` at the canonical code base `0x210550`) with
the fifth bit of `Spike/Lib/A64PhExt.lean` set on the pcs after the
thread counter's add (`wakeR`, `inR`, `phW`). Wake-specific phase
extension; generic multi-spawn needs a reserve phase bit in PhasesA64
(trusted).

`wakeR` is three code ranges named by wakeProg's labels: the rest of
`scc_rt_thread_reserve` after its `ldaddal` (`.0_entry` + 6 up to
`scc_rt_thread_init`), `wc_main` from the reserve's return point `.sp3` up
to `.stack_grow`, and the child stub `.child9` up to `scc_rt_morestack`.
Every fact is decided by `decide +kernel` on the program's labels
(through the keyed table `codeT`, `codeT_eq`); no pc range is a hypothesis.

- `RC`, `TC`, `SC`: the resolved ranges, the canonical phase table and the
  sites (`wakeR_eq`, `phTab_eq`, `sites_eq`); `phW_eq`, `okPc_eq`: the phase
  and the off-site pcs through them.
- `ownW`: `A64PhRec.ownOf` with `scc_rt_nthreads` at `0`, `1` by the fifth
  bit.
- `resPhW`: `ResPh` at `phW`, returning to `wc_main`'s `.sp3` (the reserve's
  return point, in `wakeR` as the pcs after the add are; `resPh_of_a13code`
  returns to `scc_rt_main`'s, outside it). The take's field `noTk` is asked
  of the caller.
- `phW_out`, `phW_in`: off `wakeR` the canonical phase, in it plus `16`.
- `instOkW`: the instance's facts at `phW` with `ownW`.
-/
import Spike.Lib.A64PhExt
import Spike.Lib.A64WakeLabels
import Spike.Lib.A64PhRec
import Spike.Lib.Rt.A64RtReservePh

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhRange PhTab inRs phOf phTabOf okPcOf sitesOf codeT codeT_eq blkOkN factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.PhExt (phExt)
open Spike.Lib.A64.Flow.Reserve
open Spike.Lib.A64.Rt.Reserve (ResPh ntA siPcs resPcs)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.Rt (ownUpdB InstOk RuntimeLayout)
open Spike.Lib.A64Consumer

/-- The canonical code base. -/
abbrev lo : Nat := 0x210550

/-! ## The ranges and the phase -/

/-- **The pcs after the thread counter's add**, by wakeProg's labels. -/
def wakeR : List PhRange :=
  [⟨".L4_scc_rt_thread_reserve.0_entry", 6, "scc_rt_thread_init", 0⟩,
    ⟨".L21_wc_main.sp3", 0, ".L21_wc_main.stack_grow", 0⟩,
    ⟨".L21_wc_main.child9", 0, "scc_rt_morestack", 0⟩]

/-- The pc is in `wakeR` (resolved in wakeProg at the canonical base). -/
def inR (pc : Nat) : Bool :=
  match wakeR.mapM (PhRange.resolve (codeOf lo wakeProg)) with
  | some rs => inRs rs pc
  | none => false

/-- **wake.w's extended phase index.** -/
def phW : Nat → Nat := phExt (phOf lo wakeProg) inR

/-- The resolved ranges. -/
def RC : List (Nat × Nat) := [(2165172, 2165244), (2169248, 2169408), (2169512, 2169532)]

/-- The canonical phase table of wakeProg. -/
def TC : PhTab where
  p := [(2164048, 2164120), (2164712, 2164908)]
  l := [(2165644, 2165824)]
  n := [(2164048, 2164132), (2164712, 2165132), (2165244, 2165272), (2165400, 2165848)]
  t := [(2164048, 2164132), (2164712, 2165132), (2165244, 2165272), (2165400, 2165944)]

/-- The sites (`siteLabels` at `Link.abortName`). -/
def SC : List Nat := [2165940, 2165996, 2168260, 2168332, 2168404, 2168476, 2168548]

theorem wakeR_eq : wakeR.mapM (PhRange.resolve (codeOf lo wakeProg)) = some RC := by
  rw [← codeT_eq]; decide +kernel

theorem phTab_eq : phTabOf lo wakeProg = some TC := by
  unfold phTabOf; rw [← codeT_eq]; decide +kernel

theorem sites_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    sitesOf lo wakeProg Λ = some SC := by
  unfold sitesOf Scc.Cert.Rt.A64.sitesBy Scc.Cert.Rt.A64.siteLabels
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
theorem phW_out {pc : Nat} (h : inRs RC pc = false) : phW pc = phOf lo wakeProg pc := by
  unfold phW phExt; rw [inR_eq, h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- **In `wakeR` it is the canonical one plus `16`.** -/
theorem phW_in {pc : Nat} (h : inRs RC pc = true) : phW pc = phOf lo wakeProg pc + 16 := by
  unfold phW phExt; rw [inR_eq, h, Bool.toNat_true, Nat.mul_one]

theorem okPc_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    okPcOf lo wakeProg Λ = okC := by
  funext pc; unfold okPcOf okC; rw [sites_eq hΛ]

/-! ## The owned words -/

/-- **The owned words at an extended phase index**: `A64PhRec.ownOf`'s four
counters (by the low bits) and `scc_rt_nthreads` (at `a`), `0` before the
add and `1` after it (the fifth bit). -/
def ownW (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : List (Loc × Val) :=
  Spike.Lib.A64.PhRec.ownOf L i ++ [(⟨a, 8⟩, (if i / 16 % 2 = 1 then 1#64 else 0#64).setWidth 128)]

/-! ## `scc_rt_thread_reserve`'s phase facts -/

/-- The reserve's blocks' checks at `phW`, returning to `wc_main`'s `.sp3`. -/
theorem resBlks :
    blkOkN (codeT lo wakeProg) okC phC 2165132 0 rPro (some ".L21_wc_main.sp3") none = true ∧
    blkOkN (codeT lo wakeProg) okC phC 2165148 2 rArg (some ".L21_wc_main.sp3") none = true ∧
    blkOkN (codeT lo wakeProg) okC phC 2165148 6 rBnd (some ".L21_wc_main.sp3") none = true ∧
    blkOkN (codeT lo wakeProg) okC phC 2165148 15 rJ (some ".L21_wc_main.sp3") none = true ∧
    blkOkN (codeT lo wakeProg) okC phC 2165224 0 rRet (some ".L21_wc_main.sp3") none = true := by
  decide +kernel

/-- The reserve's labels. -/
theorem resLabs : codeOf lo wakeProg fnL = some 2165132 ∧ codeOf lo wakeProg entryL = some 2165148 ∧
    codeOf lo wakeProg okL = some 2165224 := by
  rw [← codeT_eq]; decide +kernel

/-- The reserve's single steps and the add off the sites, at `phW`. -/
theorem resSteps : factOk (codeT lo wakeProg) okC phC (.step entryL 0) = true ∧
    factOk (codeT lo wakeProg) okC phC (.step entryL 1) = true ∧
    factOk (codeT lo wakeProg) okC phC (.ok entryL 5) = true ∧ phC 2165168 = 0 ∧ phC 2165172 = 16 := by
  decide +kernel

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- `lab l + 4 k` at a resolved label. -/
theorem pc_eq (hlab : ∀ l a, codeOf lo wakeProg l = some a → lab l = Int64.ofNat a) {l : Label} {a : Nat}
    (hl : codeOf lo wakeProg l = some a) (k : Nat) :
    (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = (a + 4 * k) % 2 ^ 64 := by
  rw [hlab l a hl, toNat_add]

/-- **`ResPh` at `phW`** with `ownW`, returning to `wc_main`'s `.sp3`, the
labels resolved as the certificate's (`hlab`), the counter off the four
counters (`hsep`); the take's field given. -/
theorem resPhW (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {Tk : State → Prop}
    (hlab : ∀ l a, codeOf lo wakeProg l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s) :
    ResPh (okPcOf lo wakeProg Λ) phW Tk (ownW L (ntA lab)) lab (lab ".L21_wc_main.sp3") := by
  obtain ⟨bE, bA, bB, bJ, bO⟩ := resBlks
  obtain ⟨lF, lE, lO⟩ := resLabs
  obtain ⟨s0, s1, s5, p5, p6⟩ := resSteps
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at bE bA bB bJ bO
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at s0 s1 s5
  rw [← phW_eq] at p5 p6
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, some ".L21_wc_main.sp3" = some r → lab ".L21_wc_main.sp3" = lab r := fun _ h => by cases h; rfl
  have hrmw : (rmwPc lab).toBitVec.toNat = 2165168 := pc_eq hlab lE 5
  have hrmw4 : (rmwPc lab + Int64.ofNat 4).toBitVec.toNat = 2165172 := by
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
      rcases hp with rfl | rfl
      · exact step_of_factOk hlab s0
      · exact step_of_factOk hlab s1
    rmwOk := ok_of_factOk hlab s5
    noTk := noTk
    rmwIn := ⟨(0#64).setWidth 128, by rw [hrmw, p5]; simp [ownW]⟩
    rmwUpd := by
      obtain ⟨h1, h2, h3, h4⟩ := hsep
      rw [hrmw, hrmw4, p5, p6]
      simp [ownUpdB, ownW, Spike.Lib.A64.PhRec.ownOf, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
      decide }

/-! ## The instance's facts -/

/-- **The instance's facts at `phW`** with `ownW` (the counter at `a`) and
a take's phase `TkW` of the phase index, for a layout of wakeProg at the
canonical base, the take site at its label (`hsite`). -/
theorem instOkW {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) phW L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (ownW L a) h, by simp only [h]⟩
  off := by
    have h := Spike.Lib.A64.PhRec.off L (rS := rS) hsite
    unfold Spike.Lib.A64.PhRec.okPc at h
    rw [hp, hlo] at h
    exact h

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.resPhW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.resPhW

/-- info: 'Spike.Lib.A64.WakePh.instOkW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.instOkW
